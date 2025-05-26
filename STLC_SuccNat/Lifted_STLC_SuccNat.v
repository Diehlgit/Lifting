Require Import STLC_SuccNat.
Require Import String List Maps.
Import ListNotations.

Open Scope string_scope.
(* A Feature is represented by a string *)
Definition Feature := string.

(*A Feature Configuration is a list of features *)
Definition FeatureConfig := list Feature.

(* A Presence Condition is a Boolean expression over features *)
Inductive PresenceCondition : Type :=
  | PC_Feature : Feature -> PresenceCondition
  | PC_And     : PresenceCondition -> PresenceCondition -> PresenceCondition
  | PC_Or      : PresenceCondition -> PresenceCondition -> PresenceCondition
  | PC_Not     : PresenceCondition -> PresenceCondition
  | PC_True    : PresenceCondition
  | PC_False   : PresenceCondition.

Declare Custom Entry pc_syntax.

Notation "x" := x (in custom pc_syntax at level 0, x constr).
Notation "'FEATURE' f" := (PC_Feature f)
  (in custom pc_syntax at level 0, f constr).
Notation "x '/\' y" := (PC_And x y)
  (in custom pc_syntax at level 40, left associativity).
Notation "x '\/' y" := (PC_Or x y)
  (in custom pc_syntax at level 50, left associativity).
Notation "'~' x" := (PC_Not x)
  (in custom pc_syntax at level 35, right associativity).
Notation "'TRUE'" := PC_True (in custom pc_syntax at level 0).
Notation "'FALSE'" := PC_False (in custom pc_syntax at level 0).
Notation "'(' x ')'" := x
  (in custom pc_syntax, x at level 0).
Notation "'[[' x ']]'" := x
  (at level 0, x custom pc_syntax at level 99).

(* Function that evaluates a Presence Condition given a Feature Configuration *)
(* Q: Should I do a relational definition of this function?
      Since it might be easier to prove something *)
Fixpoint pc_eval (cfg : FeatureConfig) (pc : PresenceCondition) : bool :=
  match pc with
  | PC_Feature f => if in_dec String.string_dec f cfg then true else false
  | PC_And p1 p2 => pc_eval cfg p1 && pc_eval cfg p2
  | PC_Or  p1 p2 => pc_eval cfg p1 || pc_eval cfg p2
  | PC_Not p1   => negb (pc_eval cfg p1)
  | PC_True => true
  | PC_False => false
  end.

Example pc1: pc_eval ["A"; "B"] [[ (FEATURE "A") /\ (FEATURE "B") ]] = true.
Proof. reflexivity. Qed.

Example pc2: pc_eval [] [[ ~ FEATURE "C" ]] = true.
Proof. reflexivity. Qed.

Example pc3: pc_eval ["A"; "B"; "C"] [[ (FEATURE "A") /\ ~ (FEATURE "B") \/ (FEATURE "C") ]] = true.
Proof. reflexivity. Qed.

Example pc4: pc_eval ["A"] [[ TRUE /\ (FEATURE "A") ]] = true.
Proof. reflexivity. Qed.

Example pc5: pc_eval ["A"] [[ FALSE /\ (FEATURE "A") ]] = false.
Proof. reflexivity. Qed.

(*TODO: Define a plusone because it's simpler to work with*)
Definition plusone := abs "n" Nat (succ (var "n")).

Definition plustwo := abs "n" Nat (succ (succ (var "n"))).

Example ty_plusone: has_type empty plusone (Arrow Nat Nat).
Proof.
  apply T_Abs.
  apply T_Succ.
  apply T_Var.
  reflexivity.
Qed.

Example ty_plustwo: has_type empty plustwo (Arrow Nat Nat).
Proof.
  apply T_Abs.
  apply T_Succ. apply T_Succ.
  apply T_Var. reflexivity.
Qed.

Example plusone_0_is_1:
  step_normal_form_of (STLC_SuccNat.app plusone (const 0)) (const 1).
Proof.
  split.
  - eapply multi_step.
    + apply ST_AppAbs. apply v_nat.
    + eapply multi_step.
      * simpl. eapply ST_SuccConst.
      * apply multi_refl.
  - intros [t' Contra]. inversion Contra.
Qed.

Example plustwo_3_is_5:
  step_normal_form_of (STLC_SuccNat.app plustwo (const 3)) (const 5).
Proof.
  split.
  - eapply multi_step.
    + apply ST_AppAbs. apply v_nat.
    + eapply multi_step.
      * simpl. eapply ST_Succ. apply ST_SuccConst.
      * eapply multi_step.
        ** apply ST_SuccConst.
        ** apply multi_refl.
  - intros [t' Contra]. inversion Contra.
Qed.

Definition lifted_plustwo := [(abs "n" Nat (succ (succ (var "n"))), [[TRUE]])].
Check lifted_plustwo.

(* It's possible to define this like a function that receives a ty and returns a lifted_ty *)
Definition lifted_ty := list (ty * PresenceCondition).
Definition lifted_tm := list (tm * PresenceCondition).

Definition disjoint (pc1 pc2 : PresenceCondition) : Prop :=
  forall (cfg : FeatureConfig), ~(pc_eval cfg pc1 = true /\ pc_eval cfg pc2 = true).

Example disjoint1: disjoint [[TRUE]] [[FALSE]].
Proof.
  intros cfg [Hpc1 Hpc2].
  rewrite <- Hpc1 in Hpc2.
  simpl in Hpc2.
  inversion Hpc2.
Qed.

Example disjoint2: ~(disjoint [[FEATURE "A"]] [[FEATURE "B"]]).
Proof.
  unfold disjoint; intros Hd.
  specialize Hd with ["A"; "B"].
  apply Hd. split; simpl; reflexivity.
Qed.

Example disjoint3:
  (disjoint
    [[ ~(FEATURE "A") /\ (FEATURE "B") ]]
    [[ ~(FEATURE "A") /\ ~(FEATURE "B") ]]
  ).
Proof.
  unfold disjoint.
  intros cfg [Hpc1 Hpc2].
  simpl in *.
  remember (if in_dec string_dec "A" cfg then true else false) as a.
  remember (if in_dec string_dec "B" cfg then true else false) as b.
  destruct a, b; 
    try (inversion Hpc1);
    inversion Hpc2.
Qed.

Fixpoint disjointness (lftd_tm : lifted_tm) : Prop :=
  match lftd_tm with
  | [] => True
  | (_, pc) :: rest =>
      (forall t' pc', In (t', pc') rest -> disjoint pc pc') /\ disjointness rest
  end.

Definition lifted_x :=
  [
   (const 1, [[FEATURE "A"]]);
   (const 2, [[~ (FEATURE "A") /\ (FEATURE "B")]]);
   (const 3, [[~ (FEATURE "A") /\ ~ (FEATURE "B")]])
  ].

Example disjointness_lftd_x: disjointness lifted_x.
Proof.
  simpl. split.
  - intros. destruct H.
    + inversion H; subst.
      intros cfg [Hpc1 Hpc2].
      simpl in *.
      rewrite Hpc1 in Hpc2.
      simpl in Hpc2. discriminate.
    + destruct H.
      * inversion H.
        intros cfg [Hpc1 Hpc2].
        simpl in *.
        rewrite Hpc1 in Hpc2.
        simpl in Hpc2. discriminate.
      * inversion H.
  - split.
    + intros. destruct H.
      * inversion H. apply disjoint3.
      * inversion H.
    + split; auto.
      intros. inversion H.
Qed.

Definition lifted_y :=
  [
    (const 5, [[(FEATURE "A") /\ ~ (FEATURE "B")]]);
    (const 4, [[FEATURE "B"]]);
    (const 3, [[~(FEATURE "A") /\ ~(FEATURE "B")]])
  ].

(*Definetively can make a Ltac to solve this stuff*)
Example disjointness_lftd_y: disjointness lifted_y.
Proof.
  split.
  - intros. destruct H; inversion H.
    + intros cfg [Hpc1 Hpc2].
      simpl in *.
      remember (if in_dec string_dec "A" cfg then true else false) as a.
      remember (if in_dec string_dec "B" cfg then true else false) as b.
      rewrite Hpc2 in Hpc1.
      destruct a; discriminate.
    + inversion H0.
      intros cfg [Hpc1 Hpc2].
      simpl in *.
      remember (if in_dec string_dec "A" cfg then true else false) as a.
      remember (if in_dec string_dec "B" cfg then true else false) as b.
      destruct a, b; discriminate.
    + inversion H0.
  - split.
    + intros. destruct H.
      * inversion H.
        intros cfg [Hpc1 Hpc2].
        simpl in *.
        remember (if in_dec string_dec "A" cfg then true else false) as a.
        remember (if in_dec string_dec "B" cfg then true else false) as b.
        rewrite Hpc1 in Hpc2.
        destruct a; discriminate.
      * inversion H.
    + split.
      * intros. inversion H.
      * apply I.
Qed.

Definition lifted_z := [ (const 19, [[TRUE]]) ].

Example disjointness_lftd_z: disjointness lifted_z.
Proof.
  split.
  - intros. inversion H.
  - apply I.
Qed.
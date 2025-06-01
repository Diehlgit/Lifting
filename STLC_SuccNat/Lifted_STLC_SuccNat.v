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

Definition lifted_plusone := [(abs "n" Nat (succ (var "n")), [[TRUE]])].

Definition lifted_plustwo := [(abs "n" Nat (succ (succ (var "n"))), [[TRUE]])].
Check lifted_plustwo.

(* It's possible to define this like a function that receives a ty and returns a lifted_ty *)
Definition lifted_tm := list (tm * PresenceCondition).

(* Example disjoint1: disjoint [[TRUE]] [[FALSE]].
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
 *)
(* Fixpoint disjointness (lftd_tm : lifted_tm) : Prop :=
  match lftd_tm with
  | [] => True
  | (_, pc) :: rest =>
      (forall t' pc', In (t', pc') rest -> disjoint pc pc') /\ disjointness rest
  end.
 *)
Definition lifted_x :=
  [
   (const 1, [[FEATURE "A"]]);
   (const 2, [[~ (FEATURE "A") /\ (FEATURE "B")]]);
   (const 3, [[~ (FEATURE "A") /\ ~ (FEATURE "B")]])
  ].
(* 
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
Qed. *)

Definition lifted_y :=
  [
    (const 5, [[(FEATURE "A") /\ ~ (FEATURE "B")]]);
    (const 4, [[FEATURE "B"]]);
    (const 3, [[~(FEATURE "A") /\ ~(FEATURE "B")]])
  ].

(* (*Definetively can make a Ltac to solve this stuff*)
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
Qed. *)

(* Fixpoint lift (t:tm) : lifted_tm :=
  match t with
  | var s => [(var s, [[TRUE]])]
  | STLC_SuccNat.app t1 t2 =>
    flat_map (fun '(tm1, pc1) =>
      map (fun '(tm2, pc2) => 
        ((STLC_SuccNat.app tm1 tm2), (PC_And pc1 pc2))) (lift t2)) (lift t1)
  | const n => [(const n, [[TRUE]])]
  | succ t1 =>
    map (fun '(tm, pc) => (succ tm, pc)) (lift t1)
  | abs s T t1 =>
    map (fun '(tm, pc) => (abs s T tm, pc)) (lift t1)
  end. *)

(* Example lifting_plusone: lift plusone = lifted_plusone.
Proof.
  unfold lifted_plusone.
  simpl. reflexivity.
Qed.

Example lifting_plustwo: lift plustwo = lifted_plustwo.
Proof.
  unfold lifted_plustwo.
  simpl. reflexivity.
Qed.
*)

(* Automatic lifting *)
Inductive ty' : Type :=
  | Arrow' : ty' -> ty' -> ty'
  | Nat' : ty'.

Fixpoint lift_ty (T : ty) : ty' :=
  match T with
    | Nat => Nat'
    | Arrow T1 T2 => Arrow' (lift_ty T1) (lift_ty T2)
  end.

Inductive tm' :=
  | var' : string -> tm'
  | abs' : string ->  ty' -> tm' -> tm'
  | app' : tm' -> tm' -> tm'

  | const' : (list (nat * PresenceCondition)) -> tm'
  | succ' : tm' -> tm'.

Fixpoint lift (t:tm) : tm':=
  match t with
  | var s => (var' s)
  | abs s T t => (abs' s (lift_ty T) (lift t))
  | STLC_SuccNat.app t1 t2 => (app' (lift t1) (lift t2))

  | const n => (const' [(n, [[TRUE]])])
  | succ t => (succ' (lift t))
  end.

Fixpoint derive_ty (T':ty') : ty :=
  match T' with
  | Nat' => Nat
  | Arrow' T1' T2' => Arrow (derive_ty T1') (derive_ty T2')
  end.

Fixpoint derive_const_list (lst : list (nat * PresenceCondition)) (cfg : FeatureConfig) : option tm :=
  match lst with
  | [] => None
  | (t, pc) :: rest =>
    if pc_eval cfg pc then Some (const t)
    else derive_const_list rest cfg
  end.

Fixpoint derive (t':tm') (cfg:FeatureConfig) : option tm :=
  match t' with
  | var' s => Some (var s)
  | abs' s T' t1' =>
    match derive t1' cfg with
    | Some t1 => Some (abs s (derive_ty T') t1)
    | None => None
    end
  | app' t1' t2' =>
    match derive t1' cfg, derive t2' cfg with
    | Some t1, Some t2 => Some (STLC_SuccNat.app t1 t2)
    | _, _ => None
    end
  | const' n' => derive_const_list n' cfg
  | succ' t1' =>
    match derive t1' cfg with
    | Some t1 => Some (succ t1)
    | None => None
    end
  end.

Example const1': lift (const 1) = const' [(1, [[TRUE]])].
Proof. simpl. reflexivity. Qed.

Example plusone': lift plusone = abs' "n" Nat' (succ' (var' "n")).
Proof. simpl. reflexivity. Qed.

Definition x':= const' [
   (1, [[FEATURE "A"]]);
   (2, [[~ (FEATURE "A") /\ (FEATURE "B")]]);
   (3, [[~ (FEATURE "A") /\ ~ (FEATURE "B")]])
  ].

Definition y' := const' [
    (5, [[(FEATURE "A") /\ ~ (FEATURE "B")]]);
    (4, [[FEATURE "B"]]);
    (3, [[~(FEATURE "A") /\ ~(FEATURE "B")]])
  ].

Definition z' := const' [ (19, [[TRUE]]) ].

Definition disjoint (pc1 pc2 : PresenceCondition) : Prop :=
  forall (cfg : FeatureConfig), ~(pc_eval cfg pc1 = true /\ pc_eval cfg pc2 = true).

Fixpoint disjoint_lst (l : list(nat * PresenceCondition)) : Prop :=
  match l with
  | [] => True
  | (_, pc) :: rest =>
      (forall t' pc', In (t', pc') rest -> disjoint pc pc') /\ disjoint_lst rest
  end.

Fixpoint disjointness (t' : tm') : Prop :=
  match t' with
  | var' s => True
  | abs' s T' t1' => disjointness t1'
  | app' t1' t2' => disjointness t1' /\ disjointness t2'
  | const' n' => disjoint_lst n'
  | succ' t1' => disjointness t1'
  end.

Lemma disjointness_x': disjointness x'.
Proof.
  unfold disjointness.
  simpl. split.
  - intros t' pc' [].
    + injection H as []. rewrite <- H.
      unfold disjoint; intros cfg [].
      simpl in H0, H1.
      destruct in_dec; discriminate.
    + destruct H.
      * injection H as []. rewrite <- H.
        intros cfg []. simpl in H0, H1.
        destruct in_dec; discriminate.
      * destruct H.
  - split.
    + intros t' pc' [].
      * injection H as []. rewrite <- H.
        intros cfg []. simpl in H0, H1.
        destruct in_dec; destruct in_dec; discriminate.
      * destruct H.
    + split.
      * intros. destruct H.
      * apply I.
Qed.

Inductive value' : tm' -> Prop :=
  | v_abs' : forall x T' t', value' (abs' x T' t')
  | v_nat' : forall n', value' (const' n').

Fixpoint subst' (x:string) (s' t': tm'): tm' :=
  match t' with
  | var' y => if String.eqb x y then s' else t'
  | abs' y T' t1' => if String.eqb x y then t1' else abs' y T' (subst' x s' t1')
  | app' t1' t2' => app' (subst' x s' t1') (subst' x s' t2')
  | const' _ => t'
  | succ' t1' => succ' (subst' x s' t1')
  end.

Inductive step': tm' -> tm' -> Prop :=
  | ST_App1': forall t1' t1'' t2',
    step' t1' t1'' ->
      step' (app' t1' t2') (app' t1'' t2')
  | ST_App2': forall v' t2' t2'',
    value' v' ->
    step' t2' t2'' ->
      step' (app' v' t2') (app' v' t2'')
  | ST_AppAbs': forall x T' t' v',
    value' v' ->
      step' (app' (abs' x T' t') v') (subst' x v' t')
  | ST_Succ': forall t' t'',
    step' t' t'' ->
      step' (succ' t') (succ' t'')
  | ST_SuccConst': forall n',
      step' (succ' (const' n'))
      (const' (map (fun '(n,pc) => ((S n), pc)) n')).

Definition step'_normal_form_of t' t'':=
  (multi step t' t'' /\ normal_form step t'').
Require Import STLC_SuccNat.
Require Import String List Maps.
Import ListNotations.

Open Scope string_scope.
(* A Feature is represented by a string *)
Definition Feature := string.

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

(*A Feature Configuration is a list of features *)
Definition FeatureConfig := list Feature.

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

Definition pc1 := [[ (FEATURE "A") /\ (FEATURE "B") ]].
Compute pc_eval ["A"; "B"] pc1.

Definition pc2 := [[ ~ FEATURE "C" ]].
Compute pc_eval [] pc2.

Definition pc3 := [[ (FEATURE "A") /\ ~ (FEATURE "B") \/ (FEATURE "C") ]].
Compute pc_eval ["A"; "B"; "C"] pc2.

Definition pc4 := [[ TRUE /\ (FEATURE "A") ]].
Compute pc_eval ["A"] pc4.

Definition pc5 := [[ FALSE /\ (FEATURE "A") ]].
Compute pc_eval ["A"] pc5.

Definition plustwo := abs "n" Nat (succ (succ (var "n"))).

Example ty_plustwo: has_type empty plustwo (Arrow Nat Nat).
Proof.
  apply T_Abs.
  apply T_Succ. apply T_Succ.
  apply T_Var. reflexivity.
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

Definition lifted_n :=
  [
   (1, [[FEATURE "A"]]);
   (2, [[~ (FEATURE "A") /\ (FEATURE "B")]]);
   (3, [[~ (FEATURE "A") /\ ~ (FEATURE "B")]])
  ].

(* Lifted Types *)

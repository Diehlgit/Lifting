Require Import Maps.

(* Terms and Values *)
Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty.

(* Notation "S -> T" := (Arrow S T). *)

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm

  | const : nat -> tm
  | succ : tm -> tm

  | tm_fix : tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (abs x T t)
  | v_nat : forall (n : nat), value (const n).


(* Evaluation *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y => if String.eqb x y then s else t
  | abs y T t1 => if String.eqb x y then t else abs y T (subst x s t1)
  | app t1 t2 => app (subst x s t1) (subst x s t2)

  | const _ => t
  | succ t1 => succ (subst x s t1)

  | tm_fix t => tm_fix (subst x s t)
  end.

(* Notation "[ x := s ] t" := (subst x s t) (at level 100).
Check [ "t" := const 1 ] (abs "t" Nat (succ (var "t"))). *)


Inductive step : tm -> tm -> Prop :=
  | ST_App1: forall t1 t2 t3,
    step t1 t2 ->
      step (app t1 t3) (app t2 t3)
  | ST_App2: forall v t2 t3,
    value v -> step t2 t3 ->
      step (app v t2) (app v t3)
  | ST_AppAbs: forall x T t v,
    value v ->
      step (app (abs x T t) v) (subst x v t)

  | ST_Succ: forall t1 t2,
    step t1 t2 ->
      step (succ t1) (succ t2)
  | ST_SuccConst : forall (n : nat),
    step (succ (const n)) (const (S n))

  | ST_Fix : forall t1 t2,
    step t1 t2 ->
      step (tm_fix t1) (tm_fix t2)
  | ST_FixAbs : forall t1 T1 xf,
    step (tm_fix (abs xf T1 t1)) (subst xf (tm_fix (abs xf T1 t1)) t1).

Inductive multi {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition normal_form {X : Type}
              (R : X -> X -> Prop) (t1 : X) : Prop :=
  ~(exists t2, R t1 t2).

Definition step_normal_form_of t1 t2:=
  (multi step t1 t2 /\ normal_form step t2).

(*Typing*)
Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
    Gamma x = Some T ->
      has_type Gamma (var x) T
  | T_Abs : forall Gamma x T1 T2 t,
    has_type (x |-> T2 ; Gamma) t T1 ->
      has_type Gamma (abs x T2 t) (Arrow T2 T1)
  | T_App : forall Gamma T1 T2 t1 t2,
    has_type Gamma t1 (Arrow T2 T1) ->
    has_type Gamma t2 T2 ->
      has_type Gamma (app t1 t2) T1

  | T_Nat : forall Gamma (n : nat),
    has_type Gamma (const n) Nat
  | T_Succ : forall Gamma t,
    has_type Gamma t Nat -> has_type Gamma (succ t) Nat

  | T_Fix : forall Gamma t1 T1,
    has_type Gamma t1 (Arrow T1 T1) ->
    has_type Gamma (tm_fix t1) T1.


(* Properties *)
Lemma weakening : forall Gamma1 Gamma2 t T,
  includedin Gamma1 Gamma2 ->
  has_type Gamma1 t T ->
  has_type Gamma2 t T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; intros Gamma' Hi;
    econstructor; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     has_type empty t T ->
     has_type Gamma t T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma canonical_forms_nat : forall t,
  has_type empty t Nat ->
  value t ->
  exists n, t = const n.
Proof.
  intros t Ht Hv; induction t;
    inversion Hv; subst;
    inversion Ht;
    eauto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  has_type empty t (Arrow T1 T2) ->
  value t ->
  exists x u, t = abs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| ] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

Ltac unfold_exists :=
  repeat try match goal with
      | [ H: exists _, _ |- _ ] => destruct H
  end.

Theorem progress : forall t1 T,
    has_type empty t1 T ->
      value t1 \/ exists t2, step t1 t2.
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma;
    try (left; constructor).
  - inversion H.
  - right. destruct IHHt1;
    destruct IHHt2; unfold_exists; eauto using ST_App1, ST_App2.
    + eapply canonical_forms_fun in Ht1 as [x [u Ht1]]; subst;
      eauto; eexists; econstructor; assumption.
  - right. destruct IHHt; eauto.
    + eapply canonical_forms_nat in H as [n H]; subst; eauto.
      eexists. apply ST_SuccConst.
    + destruct H; eexists; eapply ST_Succ; eauto.
  - right. destruct IHHt; auto.
    + eapply canonical_forms_fun in Ht as [x [u Ht1]];
      subst; auto; eexists.
      apply ST_FixAbs.
    + unfold_exists. exists (tm_fix x).
      apply ST_Fix. auto.
Qed.

Lemma value_is_nf: forall t,
  value t -> step_normal_form_of t t.
Proof.
  intros t Hv.
  induction t; split;
    try inversion Hv; subst;
    try (intros [t' Hc]; inversion Hc);
    try constructor.
Qed.

Ltac value_no_step :=
	match goal with
	| [ H1: value ?t, H2: step ?t  _ |- _ ] =>
		exfalso; apply value_is_nf in H1 as [_ H1]; eauto
	end.

Ltac solve_by_inverts n :=
	match goal with | H : ?T  |-  _  =>
	match type of T with Prop =>
		solve [ inversion H;
		match n with S (S (?n')) =>
			subst; solve_by_inverts (S n') end ]
	end end.

Theorem determinism : forall t1 t2 t3,
  step t1 t2 -> step t1 t3 -> t2 = t3.
Proof.
  intros t1 t2 t3 Ht.
  generalize dependent t3.
  induction Ht; intros t4 Ht';
    inversion Ht'; subst; eauto;
    try value_no_step;
    try (f_equal; eauto);
    solve_by_inverts 1.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  has_type (x |-> U ; Gamma) t T ->
  has_type empty v U ->
  has_type Gamma (subst x v t) T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    inversion H; clear H; subst; simpl; eauto;
    try (econstructor; eauto);
    destruct (eqb_spec x s); subst; try (constructor).
    + rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + rewrite update_neq in H2; auto.
    + rewrite update_shadow in H5. assumption.
    + apply IHt. eapply update_permute in n.
      rewrite n in H5. assumption.
Qed.

Theorem preservation: forall t1 t2 T,
  has_type empty t1 T ->
  step t1 t2 ->
  has_type empty t2 T.
Proof.
  intros t1 t2 T Ht;
  generalize dependent t2.
  remember empty as Gamma.
  induction Ht; intros t3 H0;
    inversion H0; subst;
      try (econstructor; eauto).
  apply (T_App _ _ _ _ _ Ht1) in Ht2.
  eapply substitution_preserves_typing;
    inversion Ht2; inversion H4; subst;
    eassumption.
  inversion Ht; subst.
  apply substitution_preserves_typing with T1;
    try constructor; auto.
Qed.

Lemma preservation_multi: forall t1 t2 T,
  has_type empty t1 T ->
  multi step t1 t2 ->
  has_type empty t2 T.
Proof.
  intros t1 t2 T Htype Hmulti.
  induction Hmulti.
  - assumption.
  - apply (preservation _ _ _ Htype) in H.
    apply IHHmulti. apply H.
Qed.

Theorem normal_forms_unique: forall t1 t2 t3,
  step_normal_form_of t1 t2 ->
  step_normal_form_of t1 t3 ->
  t2 = t3.
Proof.
  intros t1 t2 t2' P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  induction P11; subst;
    inversion P21; subst;
    try (apply (IHP11 P12)).
  - reflexivity.
  - destruct P12. eauto.
  - destruct y; destruct P22; eauto.
  - remember (determinism _ _ _ H H0) as e. congruence.
Qed.

(* Auxiliary Lemmas about the language's functioning *)

Lemma succ_arg_normalizes: forall t1 t2,
  step_normal_form_of t1 t2 ->
  multi step (succ t1) (succ t2).
Proof.
  intros t1 t2 [Hms Hnf].
  induction Hms; subst.
  - apply multi_refl.
  - apply IHHms in Hnf.
    eapply multi_step.
    + apply ST_Succ. exact H.
    + exact Hnf.
Qed.

Lemma multi_step_trans: forall t1 t2 t3,
  multi step t1 t2 ->
  multi step t2 t3 ->
  multi step t1 t3.
Proof.
  intros t1 t2 t3 H12 H23.
  induction H12.
  - exact H23.
  - apply IHmulti in H23.
    eapply multi_step.
    + exact H.
    + exact H23.
Qed.

Lemma multistep_App2 : forall v t1 t2,
  value v -> (multi step t1 t2) -> multi step (app v t1) (app v t2).
Proof.
  intros v t1 t2 V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.

Lemma multistep_succ : forall t1 t2,
  multi step t1 t2 -> multi step (succ t1) (succ t2).
Proof.
  intros t1 t2 STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_Succ; eauto.  auto.
Qed.
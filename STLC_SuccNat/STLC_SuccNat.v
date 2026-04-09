Require Import Maps.

(* Terms and Values *)
Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty
  | NatList : ty.

(* Notation "S -> T" := (Arrow S T). *)

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm

  | const : nat -> tm
  | succ : tm -> tm
  | op : tm -> tm -> tm

  | nil :  tm
  | cons : tm -> tm -> tm
  | case : tm -> tm -> string -> string -> tm -> tm
  (* i.e., case t1 of | nil ⇒ t2 | x::y ⇒ t3 *).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (abs x T t)
  | v_nat : forall (n : nat), value (const n)
  | v_lnil : value nil
  | v_lcons : forall v1 v2, value v1 -> value v2 -> value (cons v1 v2).


(* Evaluation *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var y => if String.eqb x y then s else t
  | abs y T t1 => if String.eqb x y then t else abs y T (subst x s t1)
  | app t1 t2 => app (subst x s t1) (subst x s t2)

  | const _ => t
  | succ t1 => succ (subst x s t1)
  | op t1 t2 => op (subst x s t1) (subst x s t2)

  | nil => nil
  | cons t1 t2 => cons (subst x s t1) (subst x s t2)
  | case t1 t2 y z t3 => case (subst x s t1) (subst x s t2) y z
                              (if (orb (eqb x y) (eqb x z)) then t3 else (subst x s t3))
  end.

(* Notation "[ x := s ] t" := (subst x s t) (at level 100).
Check [ "t" := const 1 ] (abs "t" Nat (succ (var "t"))). *)


Class NatOp := { nat_op : nat -> nat -> nat }.

Inductive step `{NatOp} : tm -> tm -> Prop :=
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

  | ST_Op1: forall t1 t1' t2,
    step t1 t1' ->
      step (op t1 t2) (op t1' t2)
  | ST_Op2: forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
      step (op v1 t2) (op v1 t2')
  | ST_OpConst: forall (n1 n2 : nat),
    step (op (const n1) (const n2)) (const (nat_op n1 n2))

  | ST_Cons1: forall t1 t2 t3,
    step t1 t2 ->
    step (cons t1 t3) (cons t2 t3)
  | ST_Cons2: forall v t2 t3,
    value v ->
    step t2 t3 ->
    step (cons v t2) (cons v t3)
  | ST_Case1: forall x y t1 t2 tnil tcons,
    step t1 t2 ->
    step (case t1 tnil x y tcons) (case t2 tnil x y tcons)
  | ST_CaseNil: forall x y tnil tcons,
    step (case nil tnil x y tcons) tnil
  | ST_CaseCons: forall x y vh vt tnil tcons,
    value vh ->
    value vt ->
    step (case (cons vh vt) tnil x y tcons) (subst y vt (subst x vh tcons)).

Inductive multi {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition normal_form {X : Type}
              (R : X -> X -> Prop) (t : X) : Prop :=
  ~(exists t', R t t').

Definition step_normal_form_of `{NatOp} t1 t2:=
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
  | T_Op : forall Gamma t1 t2,
    has_type Gamma t1 Nat ->
    has_type Gamma t2 Nat ->
    has_type Gamma (op t1 t2) Nat

  | T_Nil : forall Gamma,
    has_type Gamma nil NatList
  | T_Cons : forall Gamma t1 t2,
    has_type Gamma t1 Nat ->
    has_type Gamma t2 NatList ->
      has_type Gamma (cons t1 t2) NatList
  | T_Case : forall Gamma x y T t1 tnil tcons,
    has_type Gamma t1 NatList ->
    has_type Gamma tnil T ->
    has_type (x |-> Nat; y |-> NatList; Gamma) tcons T ->
    has_type Gamma (case t1 tnil x y tcons) T.


(* Properties *)
Lemma weakening : forall Gamma1 Gamma2 t T,
  includedin Gamma1 Gamma2 ->
  has_type Gamma1 t T ->
  has_type Gamma2 t T.
Proof.
  intros Gamma1 Gamma2 t T H Ht.
  generalize dependent Gamma2.
  induction Ht; intros Gamma2 Hi;
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
  destruct HVal as [x ? t1| | |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

Lemma canonical_forms_list : forall t,
  has_type empty t NatList ->
  value t ->
    t = nil \/
    (exists v1 v2,
      value v1 /\ value v2 /\ t = (cons v1 v2)).
Proof.
  intros t HT Hv.
  destruct Hv; inversion HT; subst; eauto 7.
(*- auto.
  - right. exists v1, v2.
    split; [auto|split;auto]. *)
Qed.

Ltac unfold_exists :=
  repeat try match goal with
      | [ H: exists _, _ |- _ ] => destruct H
  end.

Ltac solve_by_inverts n :=
	match goal with | H : ?T  |-  _  =>
	match type of T with Prop =>
		solve [ inversion H;
		match n with S (S (?n')) =>
			subst; solve_by_inverts (S n') end ]
	end end.

Theorem progress `{NatOp} : forall t T,
    has_type empty t T ->
      value t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma.
    (*try (left; constructor).*)
  - inversion H0.
  - left; constructor.
  - right. destruct IHHt1;
    destruct IHHt2; unfold_exists; eauto using ST_App1, ST_App2.
    + eapply canonical_forms_fun in Ht1 as [x [u Ht1]]; subst;
      eauto; eexists; econstructor; assumption.
  - left; constructor.
  - right. destruct IHHt; eauto.
    + eapply canonical_forms_nat in H0 as [n H0]; subst; eauto.
      eexists. apply ST_SuccConst.
    + destruct H0; eexists; eapply ST_Succ; eauto.
  - right. destruct IHHt2, IHHt1; eauto.
    + eapply canonical_forms_nat in H0 as [n2 H2];
      eapply canonical_forms_nat in H1 as [n1 H3];
      subst; eauto. eexists. apply ST_OpConst.
    + destruct H1; eexists;
      eapply ST_Op1; eassumption.
    + destruct H0; eexists;
      eapply ST_Op2; eassumption.
    + destruct H1; eexists;
      eapply ST_Op1; eassumption.
  - left; constructor.
  - destruct IHHt1; auto.
    + destruct IHHt2; auto.
      * left. constructor; auto.
      * right. unfold_exists.
        eexists; eauto using ST_Cons2.
    + right. unfold_exists.
      eexists; eauto using ST_Cons1.
  - destruct IHHt1; auto; right.
    + destruct t1;
        try solve_by_inverts 1; eexists.
        * apply ST_CaseNil.
        * inversion H0; subst.
          eapply ST_CaseCons; auto.
    + unfold_exists. eexists.
      constructor. eauto.
Qed.

Lemma value_is_nf `{NatOp} : forall t,
  value t -> step_normal_form_of t t.
Proof.
  intros t Hv.
  induction t; split;
    try inversion Hv; subst;
    try (intros [t1 Hc]; inversion Hc);
    try constructor; subst.
  - apply IHt1 in H2 as [_ H2].
    apply IHt2 in H3 as [_ H3].
    intros H4. destruct H4 as [x H4].
    inversion H4; subst; eauto.
Qed.

Ltac value_no_step :=
	match goal with
	| [ H1: value ?t, H2: step ?t  _ |- _ ] =>
		exfalso; apply value_is_nf in H1 as [_ H1]; eauto
  | [ H1: value ?t1, H2: value ?t2, H3: step (cons ?t1 ?t2) _ |- _] =>
    inversion H3; subst; exfalso;
             apply value_is_nf in H1 as [_ H1];
             apply value_is_nf in H2 as [_ H2]; eauto
  end.

Theorem determinism `{NatOp} : forall t1 t2 t3,
  step t1 t2 -> step t1 t3 -> t2 = t3.
Proof.
  intros t1 t2 t3 Ht.
  generalize dependent t3.
  induction Ht; intros t4 Ht';
    inversion Ht'; subst; eauto;
    try value_no_step;
    try (f_equal; eauto);
    try solve_by_inverts 2.
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
    destruct (eqb_spec x s); subst; simpl; try (constructor).
    + rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + rewrite update_neq in H2; auto.
    + rewrite update_shadow in H5. assumption.
    + apply IHt. eapply update_permute in n.
      rewrite n in H5. assumption.
    + destruct (eqb_spec s s0); subst.
      * repeat rewrite update_shadow in H9.
        rewrite update_shadow. assumption.
      * rewrite update_permute in H9; auto.
        rewrite update_shadow in H9.
        rewrite update_permute; auto.
    + destruct (eqb_spec x s0); subst.
      * rewrite update_shadow in H9. assumption.
      * apply IHt3. assert (
          (x) |-> U; (s) |-> Nat; (s0) |-> NatList; Gamma =
          (s) |-> Nat; (s0) |-> NatList; (x) |-> U; Gamma).
        { rewrite update_permute; auto. f_equal.
          rewrite update_permute; auto. }
        rewrite H. assumption.
Qed.

Theorem preservation `{NatOp} : forall t1 t2 T,
  has_type empty t1 T ->
  step t1 t2 ->
  has_type empty t2 T.
Proof.
  intros t t' T Ht;
  generalize dependent t'.
  remember empty as Gamma.
  induction Ht; intros t' H1;
    inversion H1; subst;
      try (econstructor; eauto).
  apply (T_App _ _ _ _ _ Ht1) in Ht2.
  - eapply substitution_preserves_typing;
    inversion Ht2; inversion H5; subst;
    eassumption.
  - assumption.
  - inversion Ht1; subst.
    repeat eapply substitution_preserves_typing; eauto.
Qed.

Lemma preservation_multi `{NatOp}: forall t1 t2 T,
  has_type empty t1 T ->
  multi step t1 t2 ->
  has_type empty t2 T.
Proof.
  intros t t' T Htype Hmulti.
  induction Hmulti.
  - assumption.
  - apply (preservation _ _ _ Htype) in H0.
    apply IHHmulti. apply H0.
Qed.

Theorem normal_forms_unique `{NatOp}: forall t1 t2 t3,
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
  - remember (determinism _ _ _ H0 H1) as e. congruence.
Qed.

Lemma wt_nf_is_value `{NatOp}: forall t1 t2 T,
  has_type empty t1 T ->
  step_normal_form_of t1 t2 ->
  value t2.
Proof.
  intros t1 t2 T HT [Hms Hnf].
  apply (preservation_multi _ _ _ HT) in Hms.
  apply progress in Hms as [].
  - assumption.
  - destruct Hnf. assumption.
Qed.

(* Auxiliary Lemmas about the language's functioning *)

Lemma succ_arg_normalizes `{NatOp}: forall t1 t2,
  step_normal_form_of t1 t2 ->
  multi step (succ t1) (succ t2).
Proof.
  intros t1 t2 [Hms Hnf].
  induction Hms; subst.
  - apply multi_refl.
  - apply IHHms in Hnf.
    eapply multi_step.
    + apply ST_Succ. exact H0.
    + exact Hnf.
Qed.

Lemma multi_step_trans `{NatOp}: forall t1 t2 t3,
  multi step t1 t2 ->
  multi step t2 t3 ->
  multi step t1 t3.
Proof.
  intros t1 t2 t3 H12 H23.
  induction H12.
  - exact H23.
  - apply IHmulti in H23.
    eapply multi_step.
    + exact H0.
    + exact H23.
Qed.

Lemma multistep_app1 `{NatOp}: forall t1 t2 t3,
  multi step t1 t2 -> multi step (app t1 t3) (app t2 t3).
Proof.
  intros t1 t2 t3 STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App1; eauto.  auto.
Qed.

Lemma multistep_app2 `{NatOp}: forall v t1 t2,
  value v -> (multi step t1 t2) -> multi step (app v t1) (app v t2).
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2; eauto.  auto.
Qed.

Lemma multistep_succ `{NatOp}: forall t1 t2,
  multi step t1 t2 -> multi step (succ t1) (succ t2).
Proof.
  intros t t' STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_Succ; eauto.  auto.
Qed.

Lemma multistep_cons1 `{NatOp}: forall t1 t2 t3,
  multi step t1 t2 -> multi step (cons t1 t3) (cons t2 t3).
Proof.
  intros t1 t2 t3 Hms. induction Hms.
    apply multi_refl.
    eapply multi_step.
      apply ST_Cons1; eauto. auto.
Qed.

Lemma multistep_cons2 `{NatOp}: forall v1 t2 t3,
  value v1 ->
  multi step t2 t3 ->
  multi step (cons v1 t2) (cons v1 t3).
Proof.
  intros v1 t2 t3 Hv Hms. induction Hms.
    apply multi_refl.
    eapply multi_step.
      apply ST_Cons2; eauto. auto.
Qed.

Lemma multistep_case1 `{NatOp}: forall x y t1 t2 tnil tcons,
  multi step t1 t2 -> multi step (case t1 tnil x y tcons)
                                 (case t2 tnil x y tcons).
Proof.
  intros x y t1 t2 tnil tcons Hms. induction Hms.
    apply multi_refl.
    eapply multi_step.
      apply ST_Case1; eauto. auto.
Qed.

Lemma multistep_op1 `{NatOp}: forall t1 t1' t2,
  multi step t1 t1' -> multi step (op t1 t2) (op t1' t2).
Proof.
  intros t1 t1' t2 STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_Op1; eauto.  auto.
Qed.

Lemma multistep_op2 `{NatOp}: forall v1 t2 t2',
  value v1 -> multi step t2 t2' ->
    multi step (op v1 t2) (op v1 t2').
Proof.
  intros v1 t2 t2' Hv STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_Op2; eauto.  auto.
Qed.
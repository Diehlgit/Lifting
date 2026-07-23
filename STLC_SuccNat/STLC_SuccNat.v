From STLC Require Import Maps.
Require Export Maps.

(* Terms and Values *)
Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty
  | NatList : ty.

Notation "S -> T" := (Arrow S T).

Inductive tm : Type :=
  | var : string -> tm
  | abs : string -> ty -> tm -> tm
  | app : tm -> tm -> tm
  | fixp : tm -> tm

  | const : nat -> tm
  | succ : tm -> tm
  | add : tm -> tm -> tm

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
  | fixp t1 => fixp (subst x s t1)

  | const _ => t
  | succ t1 => succ (subst x s t1)
  | add t1 t2 => add (subst x s t1) (subst x s t2)

  | nil => nil
  | cons t1 t2 => cons (subst x s t1) (subst x s t2)
  | case t1 t2 y z t3 => case (subst x s t1) (subst x s t2) y z
                              (if (orb (eqb x y) (eqb x z)) then t3 else (subst x s t3))
  end.

(* Notation "[ x := s ] t" := (subst x s t) (at level 100).
Check [ "t" := const 1 ] (abs "t" Nat (succ (var "t"))). *)

Inductive step : tm -> tm -> Prop :=
  | ST_App: forall t1 t1' t2,
    step t1 t1' ->
      step (app t1 t2) (app t1' t2)
  | ST_AppAbs: forall x T t1 t2,
    step (app (abs x T t1) t2) (subst x t2 t1)
  | ST_FixpAbs: forall x T t1,
    step (fixp (abs x T t1)) (app (abs x T t1) (fixp (abs x T t1)))
  | ST_Fixp: forall t1 t2,
    step t1 t2 ->
      step (fixp t1) (fixp t2)

  | ST_Succ: forall t1 t2,
    step t1 t2 ->
      step (succ t1) (succ t2)
  | ST_SuccConst : forall (n : nat),
    step (succ (const n)) (const (S n))

  | ST_Add1: forall t1 t1' t2,
    step t1 t1' ->
      step (add t1 t2) (add t1' t2)
  | ST_Add2: forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
      step (add v1 t2) (add v1 t2')
  | ST_AddConst: forall (n1 n2 : nat),
    step (add (const n1) (const n2)) (const (n1 + n2))

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

Definition step_normal_form_of t t':=
  (multi step t t' /\ normal_form step t').

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
  | T_Fixp : forall Gamma T1 t1,
    has_type Gamma t1 (Arrow T1 T1) ->
      has_type Gamma (fixp t1) T1

  | T_Nat : forall Gamma (n : nat),
    has_type Gamma (const n) Nat
  | T_Succ : forall Gamma t,
    has_type Gamma t Nat -> has_type Gamma (succ t) Nat
  | T_Add : forall Gamma t1 t2,
    has_type Gamma t1 Nat ->
    has_type Gamma t2 Nat ->
    has_type Gamma (add t1 t2) Nat

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

Lemma value_is_nf: forall t,
  value t -> step_normal_form_of t t.
Proof.
  induction t; intros Hv;
  split;
    try inversion Hv; subst;
    try (intros [t3 Hc]; inversion Hc);
    try constructor.
  - subst. apply IHt1 in H1.
    apply H1. exists t4. assumption.
  - subst. apply IHt2 in H2.
    apply H2. exists t4. assumption.
Qed.
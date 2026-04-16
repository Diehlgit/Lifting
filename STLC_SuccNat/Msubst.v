Require Import String List Maps.
Import ListNotations.
Require Import STLC_SuccNat.
Require Import Environments.

Hint Constructors multi : core.
Hint Constructors value : core.
Hint Constructors step : core.
Hint Constructors has_type : core.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

Definition halts t : Prop := exists t', multi step t t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

Inductive appears_free_in : string -> tm -> Prop :=
  |afi_var : forall (x:string), appears_free_in x (var x)
  |afi_app1 : forall x t1 t2,
    appears_free_in x t1 -> appears_free_in x (app t1 t2)
  |afi_app2 : forall x t1 t2,
    appears_free_in x t2 -> appears_free_in x (app t1 t2)
  |afi_abs : forall x y T11 t12,
    y <> x -> appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  |afi_fixp : forall x t1,
    appears_free_in x t1 ->
      appears_free_in x (fixp t1)
  (* nats*)
  |afi_succ : forall x t1, appears_free_in x t1 -> appears_free_in x (succ t1).

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance: forall Gamma Gamma' t S,
  has_type Gamma t S ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  has_type Gamma' t S.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto 12.
  - (* T_Var *)
    apply T_Var. rewrite <- H0; auto.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_spec x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
Qed.

Ltac false_eqb_string :=
  try match goal with
      | [ H: (?x <> ?y)%string |- _ ] => apply eqb_neq in H; rewrite H in *
      | [ H: ?x <> ?y |- _ ] => apply eqb_neq in H; rewrite H in *
  end.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    false_eqb_string...
Qed.

Corollary typable_empty__closed : forall t T,
    has_type empty t T  -> closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', subst x t' t = t.
Proof with eauto.
  induction t; intros x Hnafi t';
    simpl; eauto.
  - (* Var *)
    rename s into y. destruct (eqb_spec x y); simpl.
    exfalso. subst...
    reflexivity.
  - (* App *)
    rewrite IHt1, IHt2.
    reflexivity.
    intros H; eauto.
    intros H; eauto.
  - (* Abs *)
    rename s into y. destruct (eqb_spec x y); simpl.
    reflexivity.
    f_equal. apply IHt.
    intros H. apply Hnafi.
    apply afi_abs...
  - (* Fixp *)
    rewrite IHt...
  - (* Subst *)
    rewrite IHt...
Qed.

Lemma subst_closed: forall t,
  closed t -> forall x t', subst x t' t = t.
Proof.
  intros. apply vacuous_substitution. apply H.
Qed.

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

Lemma subst_not_afi : forall t x v,
    closed v ->  ~ appears_free_in x (subst x v t).
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_spec x s)...
     inversion A; subst. auto.
    - (* app *)
     inversion A; subst...
    - (* abs *)
     destruct (eqb_spec x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* fixp *)
     inversion A; subst...
    - (* const *)
     inversion A.
    - (* succ *)
     inversion A; subst...
Qed.

Lemma duplicate_subst : forall t' x t v,
  closed v -> (subst x t (subst x v t')) = (subst x v t').
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    (subst x1 v1 (subst x v t)) = (subst x v(subst x1 v1 t)).
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite String.eqb_refl. apply subst_closed...
   + subst. simpl. rewrite String.eqb_refl. rewrite subst_closed...
   + simpl. apply eqb_neq in n, n0. rewrite n, n0...
  - (* app *)
   rewrite IHt1, IHt2...
  - (* abs *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite eqb_refl. apply eqb_neq in n; rewrite n...
   + subst. simpl. rewrite eqb_refl. apply eqb_neq in n; rewrite n...
   + simpl. apply eqb_neq in n, n0; rewrite n, n0...
     rewrite IHt...
  - (* fixp *)
    rewrite IHt...
  - (* const *)
   reflexivity.
  - (* succ *)
   rewrite IHt...
Qed.

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env (subst x v t) = subst x v (msubst (drop x env) t) .
Proof.
  induction env; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_spec s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var: forall ss x, closed_env ss ->
  msubst ss (var x) =
  match lookup x ss with
  | Some t => t
  | None => var x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (eqb s x).
        apply msubst_closed. inversion H; auto.
        apply IHss. inversion H; auto.
Qed.
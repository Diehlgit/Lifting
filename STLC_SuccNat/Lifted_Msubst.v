Require Import String List Maps.
Import ListNotations.
Require Import STLC_SuccNat.
Require Import Lifted_STLC_SuccNat.
Require Import Environments.

Hint Constructors multi : core.
Hint Constructors value' : core.
Hint Constructors step' : core.
Hint Constructors has_type' : core.

Hint Extern 2 (has_type' _ (app' _ _) _) => eapply T_App'; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

Definition halts' t' : Prop := exists t1', multi step' t' t1' /\ value' t1'.

Lemma value'_halts' : forall v', value' v' -> halts' v'.
Proof.
  intros v H. unfold halts'.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

Inductive appears_free_in' : string -> tm' -> Prop :=
  |afi_var' : forall (x:string), appears_free_in' x (var' x)
  |afi_app1' : forall x t1' t2',
    appears_free_in' x t1' -> appears_free_in' x (app' t1' t2')
  |afi_app2' : forall x t1' t2',
    appears_free_in' x t2' -> appears_free_in' x (app' t1' t2')
  |afi_abs' : forall x y T11' t12',
    y <> x -> appears_free_in' x t12' ->
      appears_free_in' x (abs' y T11' t12')
  |afi_fixp' : forall x t1',
    appears_free_in' x t1' ->
      appears_free_in' x (fixp' t1')
  (* nats*)
  |afi_succ' : forall x t1', appears_free_in' x t1' -> appears_free_in' x (succ' t1').

Hint Constructors appears_free_in' : core.

Definition closed' (t':tm') :=
  forall x, ~ appears_free_in' x t'.

Lemma context'_invariance: forall Gamma' Gamma1' t' S',
  has_type' Gamma' t' S' ->
  (forall x, appears_free_in' x t' -> Gamma' x = Gamma1' x) ->
  has_type' Gamma1' t' S'.
Proof.
  intros.
  generalize dependent Gamma1'.
  induction H; intros; eauto 12.
  - (* T_Var' *)
    apply T_Var'. rewrite <- H0; auto.
  - (* T_Abs' *)
    apply T_Abs'.
    apply IHhas_type'. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_spec x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
  intros x y. rewrite String.eqb_neq.
  intros H. apply H. Qed.

Lemma free_in_context' : forall x t' T' Gamma',
   appears_free_in' x t' ->
   has_type' Gamma' t' T' ->
   exists T1', Gamma' x = Some T1'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs' *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx...
Qed.

Corollary typable_empty__closed' : forall t' T',
    has_type' empty t' T'  -> closed' t'.
Proof.
  intros. unfold closed'. intros x H1.
  destruct (free_in_context' _ _ _ _ H1 H) as [T1' C].
  discriminate C.
Qed.

Lemma vacuous_substitution' : forall  t' x,
     ~ appears_free_in' x t'  ->
     forall t1', subst' x t1' t' = t'.
Proof with eauto.
  induction t'; intros x Hnafi t1';
    simpl; eauto.
  - (* Var' *)
    rename s into y. destruct (eqb_spec x y); simpl.
    exfalso. subst...
    reflexivity.
  - (* Abs' *)
    rename s into y. destruct (eqb_spec x y); simpl.
    reflexivity.
    f_equal. apply IHt'.
    intros H. apply Hnafi.
    apply afi_abs'...
 - (* App' *)
    rewrite IHt'1, IHt'2.
    reflexivity.
    intros H; eauto.
    intros H; eauto.
 - (* Fixp' *)
    rewrite IHt'...
 - (* Succ' *)
    rewrite IHt'...
Qed.

Lemma subst'_closed': forall t',
  closed' t' -> forall x t1', subst' x t1' t' = t'.
Proof.
  intros. apply vacuous_substitution'. apply H.
Qed.

Lemma msubst'_closed': forall t', closed' t' -> forall ss, msubst' ss t' = t'.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst'_closed'; assumption.
Qed.

Fixpoint closed'_env' (env':env') :=
  match env' with
  | nil => True
  | (x,t')::env1' => closed' t' /\ closed'_env' env1'
  end.

Lemma subst'_not_afi' : forall t' x v',
    closed' v' ->  ~ appears_free_in' x (subst' x v' t').
Proof with eauto.  (* rather slow this way *)
  unfold closed', not.
  induction t'; intros x v P A; simpl in A.
    - (* var' *)
     destruct (eqb_spec x s)...
     inversion A; subst. auto.
    - (* abs' *)
     destruct (eqb_spec x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* app' *)
     inversion A; subst...
    - (* fixp' *)
     inversion A; subst...
    - (* const' *)
     inversion A.
    - (* succ' *)
     inversion A; subst...
Qed.

Lemma duplicate_subst' : forall t1' x t' v',
  closed' v' -> (subst' x t' (subst' x v' t1')) = (subst' x v' t1').
Proof.
  intros. eapply vacuous_substitution'. apply subst'_not_afi'. assumption.
Qed.

Lemma swap_subst' : forall t' x x1 v' v1',
    x <> x1 ->
    closed' v' -> closed' v1' ->
    (subst' x1 v1' (subst' x v' t')) = (subst' x v'(subst' x1 v1' t')).
Proof with eauto.
 induction t'; intros; simpl.
  - (* var' *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite String.eqb_refl. apply subst'_closed'...
   + subst. simpl. rewrite String.eqb_refl. rewrite subst'_closed'...
   + simpl. rewrite false_eqb_string... rewrite false_eqb_string...
  - (* abs' *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite eqb_refl. rewrite false_eqb_string...
   + subst. simpl. rewrite eqb_refl. rewrite false_eqb_string...
   + simpl. rewrite false_eqb_string... rewrite false_eqb_string...
     rewrite IHt'...
  - (* app' *)
   rewrite IHt'1, IHt'2...
  - (* fixp' *)
   rewrite IHt'...
  - (* const' *)
   reflexivity.
  - (* succ' *)
   rewrite IHt'...
Qed.

Lemma subst'_msubst': forall env' x v' t', closed' v' -> closed'_env' env' ->
    msubst' env' (subst' x v' t') = subst' x v' (msubst' (drop x env') t') .
Proof.
  induction env'; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_spec s x).
  - subst. rewrite duplicate_subst'; auto.
  - simpl. rewrite swap_subst'; eauto.
Qed.

Lemma msubst'_var': forall ss x, closed'_env' ss ->
  msubst' ss (var' x) =
  match lookup x ss with
  | Some t' => t'
  | None => var' x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (eqb s x).
        apply msubst'_closed'. inversion H; auto.
        apply IHss. inversion H; auto.
Qed.
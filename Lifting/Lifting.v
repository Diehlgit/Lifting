From Languages_Scheme Require Import PCFm_Lifted PCFm_Base.
Import List.ListNotations.

Fixpoint lift_ty (T : ty) : ty' :=
  match T with
    | Nat => Nat'
    | Arrow T1 T2 => Arrow' (lift_ty T1) (lift_ty T2)
    | NatList => NatList'
  end.

Fixpoint lift (t:tm) : tm':=
  match t with
  | var s => (var' s)
  | abs s T t => (abs' s (lift_ty T) (lift t))
  | app t1 t2 => (app' (lift t1) (lift t2))
  | fixp t => (fixp' (lift t))

  | const n => (const' [(n, pc_True)])
  | succ t => (succ' (lift t))
  | add t1 t2 => (add' (lift t1) (lift t2))

  | nil => nil'
  | cons t1 t2 => cons' (lift t1) (lift t2)
  | case t1 tnil x y tcons => case' (lift t1) (lift tnil) x y (lift tcons)
  end.

Definition lift_context (Gamma : context) : context' :=
fun x => option_map lift_ty (Gamma x).

Lemma has_type'_lookup_equiv : forall Gamma1 Gamma2 t T,
  (forall x, Gamma1 x = Gamma2 x) ->
  has_type' Gamma1 t T ->
  has_type' Gamma2 t T.
Proof.
  intros Gamma1 Gamma2 t T H_equiv H_type.
  revert Gamma2 H_equiv.
  induction H_type; intros Gamma2 H_equiv.
  
  - (* T_Var' *)
    apply T_Var'.
    rewrite <- H_equiv.
    exact H.
  - (* T_Abs' *)
    apply T_Abs'.
    apply IHH_type.
    intro y.
    unfold update.
    destruct (String.eqb x y) eqn:Heq;
      unfold t_update;
      rewrite Heq.
    + (* x = y case *) reflexivity.
    + (* x != y case *) apply H_equiv.
  - (* T_App' *)
    eapply T_App'.
    + apply IHH_type1. exact H_equiv.
    + apply IHH_type2. exact H_equiv.
  - (* T_Fixp' *)
    eapply T_Fixp'.
    apply IHH_type. exact H_equiv.
  - (* T_Nat' *)
    apply T_Nat'.
  - (* T_Succ' *)
    apply T_Succ'.
    apply IHH_type. exact H_equiv.
  - (* T_Add' *)
    apply T_Add'.
    + apply IHH_type1. exact H_equiv.
    + apply IHH_type2. exact H_equiv.
  - (* T_Nil' *)
    apply T_Nil'.
  - (* T_Cons' *)
    eapply T_Cons'.
    + apply IHH_type1. exact H_equiv.
    + apply IHH_type2. exact H_equiv.
  - (* T_Case' *)
    eapply T_Case'.
    + apply IHH_type1. assumption.
    + apply IHH_type2. assumption.
    + apply IHH_type3. intro z.
      unfold update.
      destruct (eqb x z) eqn:Heq;
        unfold t_update;
        rewrite Heq; auto.
      destruct (eqb y z) eqn:Heq0; auto.
Qed.

Lemma lift_context_update : forall (Gamma : partial_map ty) x T y,
  lift_context (x |-> T ; Gamma) y = 
  if String.eqb x y then Some (lift_ty T) else lift_context Gamma y.
Proof.
  intros. unfold lift_context, update.
  destruct (eqb_spec x y).
  - rewrite e. unfold t_update.
    rewrite eqb_refl. simpl.
    reflexivity.
  - unfold t_update.
    apply eqb_neq in n;
    rewrite n; auto.
Qed.

Theorem lifting_types: forall t T Gamma,
  has_type Gamma t T ->
  has_type' (lift_context Gamma) (lift t) (lift_ty T).
Proof.
  intros t T Gamma H. induction H;
    simpl; econstructor; eauto.
  - unfold lift_context.
    rewrite H. simpl.
    reflexivity.
  - apply has_type'_lookup_equiv with (lift_context (x |-> T2; Gamma)).
    + intro y. apply lift_context_update.
    + exact IHhas_type.
  - apply has_type'_lookup_equiv with (lift_context (x) |-> Nat; (y) |-> NatList; Gamma).
    + intro z. repeat rewrite lift_context_update.
      destruct (eqb_spec x z), (eqb_spec y z);
        subst; unfold update;
        try (rewrite t_update_eq; auto);
        try (rewrite t_update_neq; auto).
        rewrite t_update_eq; auto.
        rewrite t_update_neq; auto.
    + exact IHhas_type3.
Qed.

Lemma lifting_types_empty: forall t T,
  has_type empty t T ->
  has_type' empty (lift t) (lift_ty T).
Proof.
  intros.
  eapply (has_type'_lookup_equiv (lift_context empty)).
  - reflexivity.
  - eapply lifting_types.
    assumption.
Qed.

Lemma lift_subst_subst'_lift: forall body x t,
  lift (subst x t body) = subst' x (lift t) (lift body).
Proof.
  induction body;
    try (rename t into T);
    intros x t; simpl.
  - (* Var *)
    destruct (eqb_spec x s);
    reflexivity.
  - (* Abs *)
    destruct (eqb_spec x s).
    + reflexivity.
    + simpl. rewrite IHbody.
      reflexivity.
  - (* App *)
    rewrite IHbody1.
    rewrite IHbody2.
    reflexivity.
  - (* Fixp *)
    rewrite IHbody. reflexivity.
  - (* Const *)
    reflexivity.
  - (* Succ *)
    rewrite IHbody.
    reflexivity.
  - (* Add *)
    rewrite IHbody1, IHbody2.
    reflexivity.
  - (* Nil *)
    reflexivity.
  - (* Cons *)
    rewrite IHbody1.
    rewrite IHbody2.
    reflexivity.
  - (* Case *)
    destruct (eqb_spec x s), (eqb_spec x s0);
    rewrite IHbody1, IHbody2;
     simpl; auto.
    rewrite IHbody3; reflexivity.
Qed.

Lemma value_value': forall v,
  value v -> value' (lift v).
Proof.
  induction v; intros Hv;
    try solve_by_inverts 2;
    constructor;
    try inversion Hv; auto.
Qed.
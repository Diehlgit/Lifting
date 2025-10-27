Require Import String List Maps.
Import ListNotations.
Require Import STLC_SuccNat.
Require Import Presence_Conditions.

(* Automatic lifting *)
Inductive ty' : Type :=
  | Arrow' : ty' -> ty' -> ty'
  | Nat' : ty'.

Fixpoint lift_ty (T : ty) : ty' :=
  match T with
    | Nat => Nat'
    | Arrow T1 T2 => Arrow' (lift_ty T1) (lift_ty T2)
  end.

Definition nat' := variational_value nat.

Inductive tm' :=
  | var' : string -> tm'
  | abs' : string ->  ty' -> tm' -> tm'
  | app' : tm' -> tm' -> tm'

  | const' : nat' -> tm'
  | succ' : tm' -> tm'.

Fixpoint lift (t:tm) : tm':=
  match t with
  | var s => (var' s)
  | abs s T t => (abs' s (lift_ty T) (lift t))
  | app t1 t2 => (app' (lift t1) (lift t2))

  | const n => (const' [(n, pc_True)])
  | succ t => (succ' (lift t))
  end.

Inductive value' : tm' -> Prop :=
  | v_abs' : forall x T' t', value' (abs' x T' t')
  | v_nat' : forall n', value' (const' n').

Fixpoint subst' (x:string) (s' t': tm'): tm' :=
  match t' with
  | var' y => if String.eqb x y then s' else t'
  | abs' y T' t1' => if String.eqb x y then t' else abs' y T' (subst' x s' t1')
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
  (multi step' t' t'' /\ normal_form step' t'').

(* Typing *)
Definition context' := partial_map ty'.

Definition lift_context (Gamma : context) : context' :=
  fun x => option_map lift_ty (Gamma x).

Inductive has_type': context' -> tm' -> ty' -> Prop :=
  | T_Var' : forall Gamma' x T',
    Gamma' x = Some T' ->
      has_type' Gamma' (var' x) T'
  | T_Abs' : forall Gamma' x T1' T2' t',
    has_type' (x |-> T2' ; Gamma') t' T1' ->
      has_type' Gamma' (abs' x T2' t') (Arrow' T2' T1')
  | T_App' : forall Gamma' T1' T2' t1' t2',
    has_type' Gamma' t1' (Arrow' T2' T1') ->
    has_type' Gamma' t2' T2' ->
      has_type' Gamma' (app' t1' t2') T1'

  | T_Nat' : forall Gamma' (n' : nat'),
    has_type' Gamma' (const' n') Nat'
  | T_Succ' : forall Gamma' t',
    has_type' Gamma' t' Nat' ->
      has_type' Gamma' (succ' t') Nat'.

(* Typing Theorems *)
Lemma weakening': forall Gamma1' Gamma2' t' T',
  includedin Gamma1' Gamma2' ->
  has_type' Gamma1' t' T' ->
  has_type' Gamma2' t' T'.
Proof.
  intros Gamma1' Gamma2' t' T' H Ht.
  generalize dependent Gamma2'.
  induction Ht; intros Gamma2' Hi;
    econstructor; eauto using includedin_update.
Qed.

Lemma weakening_empty' : forall Gamma' t' T',
  has_type' empty t' T' ->
  has_type' Gamma' t' T'.
Proof.
  intros Gamma' t' T'.
  eapply weakening'.
  discriminate.
Qed.

Lemma canonical_forms_nat' : forall t',
  has_type' empty t' Nat' ->
  value' t' ->
  exists n', t' = const' n'.
Proof.
  intros t' Ht Hv; induction t';
    inversion Hv; subst;
    inversion Ht;
    eauto.
Qed.

Lemma canonical_forms_fun' : forall t' T1' T2',
  has_type' empty t' (Arrow' T1' T2') ->
  value' t' ->
  exists x u', t' = abs' x T1' u'.
Proof.
  intros t' T1' T2' HT HVal.
  destruct HVal as [x ? t1'| ] ; inversion HT; subst.
  exists x, t1'. reflexivity.
Qed.

Theorem progress' : forall t1' T',
  has_type' empty t1' T' ->
    value' t1' \/ exists t2', step' t1' t2'.
Proof.
  intros t' T' Ht.
  remember empty as Gamma'.
  induction Ht; subst Gamma';
    try (left; constructor).
  - inversion H.
  - right. destruct IHHt1;
    destruct IHHt2; unfold_exists; eauto using ST_App1', ST_App2'.
    eapply canonical_forms_fun' in Ht1 as [x [u' Ht1'] ]; subst;
      eauto; eexists; econstructor; assumption.
  - right. destruct IHHt; eauto.
    + eapply canonical_forms_nat' in H as [n' H]; subst; eauto.
      eexists. apply ST_SuccConst'.
    + destruct H; eexists; eapply ST_Succ'; eauto.
Qed.

Lemma substitution_preserves_typing': forall Gamma' x U' t' v' T',
  has_type' (x |-> U' ; Gamma') t' T' ->
  has_type' empty v' U' ->
  has_type' Gamma' (subst' x v' t') T'.
Proof.
  intros Gamma' x U' t' v' T' Ht' Hv'.
  generalize dependent Gamma'. generalize dependent T'.
  induction t'; intros T' Gamma' H;
    inversion H; clear H; subst; simpl; eauto;
    try (econstructor; eauto);
    destruct (eqb_spec x s); subst; try (constructor).
    + rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty'. assumption.
    + rewrite update_neq in H2; auto.
    + rewrite update_shadow in H5. assumption.
    + apply IHt'. eapply update_permute in n.
      rewrite n in H5. assumption.
Qed.

Theorem preservation': forall t1' t2' T',
  has_type' empty t1' T' ->
  step' t1' t2' ->
  has_type' empty t2' T'.
Proof.
  intros t1' t2' T' Ht;
  generalize dependent t2'.
  remember empty as Gamma'.
  induction Ht; intros ts' H0;
    inversion H0; subst;
      try (econstructor; eauto).
  apply (T_App' _ _ _ _ _ Ht1) in Ht2.
  eapply substitution_preserves_typing';
    inversion Ht2; inversion H4; subst;
    eassumption.
Qed.

Lemma preservation'_multi: forall t1' t2' T',
  has_type' empty t1' T' ->
  multi step' t1' t2' ->
  has_type' empty t2' T'.
Proof.
  intros t1' t2' T' Htype' Hmulti.
  induction Hmulti.
  - assumption.
  - apply (preservation' _ _ _ Htype') in H.
    apply IHHmulti. apply H.
Qed.

(* Auxialiary Mapping theorems *)
Theorem mapping_not_change_deriving: forall (spl:nat') (cfg:feat_config) (p:nat) (analysis:nat->nat),
  derive spl cfg = Some p ->
  derive (map (fun '(n, pc) => (analysis n, pc)) spl) cfg = Some (analysis p).
Proof.
  induction spl;
  intros cfg p analysis Hd.
  - inversion Hd.
  - destruct a. simpl in Hd.
    destruct (pc_eval cfg p0) eqn: EQ.
    + simpl. rewrite EQ in *.
      f_equal. injection Hd as Hd.
      f_equal. assumption.
    + simpl. rewrite EQ in *.
      apply IHspl. assumption.
Qed.

Lemma map_map_fst: forall {A B: Type} (l: list (A*B)) (f g: A -> A),
  map (fun '(v2, pc2) => (g v2, pc2)) (map (fun '(v1, pc1) => (f v1, pc1)) l) =
  map (fun '(v3, pc3) => (g (f v3), pc3)) l.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    f_equal. destruct a.
    reflexivity.
Qed.

(* Language Theorems *)
Lemma multi_step'_trans: forall t1' t2' t3',
  multi step' t1' t2' ->
  multi step' t2' t3' ->
  multi step' t1' t3'.
Proof.
  intros t1' t2' t3' H12 H23.
  induction H12.
  - exact H23.
  - apply IHmulti in H23.
    eapply multi_step.
    + exact H.
    + exact H23.
Qed.

Lemma value'_is_nf: forall t',
  value' t' -> step'_normal_form_of t' t'.
Proof.
  induction t'; intros Hv;
  split;
    try inversion Hv; subst;
    try (intros [t1' Hc]; inversion Hc);
    try constructor.
Qed.

Ltac value'_no_step :=
	match goal with
	| [ H1: value' ?t, H2: step' ?t  _ |- _ ] =>
		exfalso; apply value'_is_nf in H1 as [_ H1]; eauto
	end.

Theorem determinism' : forall t1' t2' t3',
  step' t1' t2' -> step' t1' t3' -> t2' = t3'.
Proof.
  intros t1' t2' t3' Ht.
  generalize dependent t3'.
  induction Ht; intros t3' Ht';
    inversion Ht'; subst; eauto;
    try value'_no_step;
    try (f_equal; eauto);
    try solve_by_inverts 1.
Qed.

Theorem normal_forms'_unique: forall t1' t2' t3',
  step'_normal_form_of t1' t2' ->
  step'_normal_form_of t1' t3' ->
  t2' = t3'.
Proof.
  intros t1' t2' t3' P1 P2.
  destruct P1 as [P12 Pnf2].
  destruct P2 as [P13 Pnf3].
  induction P12; subst;
    inversion P13; subst;
    try (apply (IHP12 Pnf2)).
  - reflexivity.
  - destruct Pnf2. eauto.
  - destruct y; destruct Pnf3; eauto.
  - remember (determinism' _ _ _ H H0) as e. congruence.
Qed.

Lemma succ'_arg_normalizes: forall t1' t2',
  step'_normal_form_of t1' t2' ->
  multi step' (succ' t1') (succ' t2').
Proof.
  intros t1' t2' [Hms' Hnf'].
  induction Hms'; subst.
  - apply multi_refl.
  - apply IHHms' in Hnf'.
    eapply multi_step.
    + apply ST_Succ'. exact H.
    + exact Hnf'.
Qed.

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
  - (* T_Nat' *)
    apply T_Nat'.
  - (* T_Succ' *)
    apply T_Succ'.
    apply IHH_type. exact H_equiv.
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
  - destruct (eqb_spec x s);
    reflexivity.
  - rewrite IHbody1.
    rewrite IHbody2.
    reflexivity.
  - destruct (eqb_spec x s).
    + reflexivity.
    + simpl. rewrite IHbody.
      reflexivity.
  - reflexivity.
  - rewrite IHbody.
    reflexivity.
Qed.

Lemma value_value': forall v,
  value v -> value' (lift v).
Proof.
  induction v; intros Hv;
    try solve_by_inverts 2;
    constructor.
Qed.

Lemma step_step': forall t1 t2,
  step t1 t2 ->
  step' (lift t1) (lift t2).
Proof.
  induction t1; intros t2 Hstep;
    try solve_by_inverts 2.
  - inversion Hstep; subst.
    + apply IHt1_1 in H2.
      apply ST_App1'.
      assumption.
    + apply IHt1_2 in H3.
      apply ST_App2';
        try (apply value_value' in H1);
        assumption.
    + rewrite lift_subst_subst'_lift.
      apply ST_AppAbs'.
      apply value_value'; assumption.
  - inversion Hstep; subst.
    + apply IHt1 in H0.
      apply ST_Succ'; assumption.
    + apply ST_SuccConst'.
Qed.

Lemma mstep_mstep': forall t1 t2,
  multi step t1 t2 ->
  multi step' (lift t1) (lift t2).
Proof.
  intros t1 t2 Hmulti.
  induction Hmulti.
  - apply multi_refl.
  - eapply multi_step with (y:= (lift y)).
    + apply step_step'. apply H.
    + exact IHHmulti.
Qed.

Lemma multistep'_App2' : forall v' t' t1',
  value' v' -> (multi step' t' t1') -> multi step' (app' v' t') (app' v' t1').
Proof.
  intros v t t' V STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_App2'; eauto.  auto.
Qed.

Lemma multistep'_succ' : forall t' t1',
  multi step' t' t1' -> multi step' (succ' t') (succ' t1').
Proof.
  intros t t' STM. induction STM.
   apply multi_refl.
   eapply multi_step.
     apply ST_Succ'; eauto.  auto.
Qed.
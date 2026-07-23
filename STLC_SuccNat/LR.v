From STLC Require Import STLC_SuccNat Lifted_STLC_SuccNat Derivation.

Inductive LR (conf:feat_config) : tm -> tm' -> Prop :=
  | LR_var: forall x, LR conf (var x) (var' x)
  | LR_app: forall t1 t2 t1' t2',
    LR conf t1 t1' ->
    LR conf t2 t2' ->
    LR conf (app t1 t2) (app' t1' t2')
  | LR_abs: forall x T t t',
    LR conf t t' ->
    LR conf (abs x T t) (abs' x (lift_ty T) t')
  | LR_fixp: forall t t',
    LR conf t t' -> LR conf (fixp t) (fixp' t')
  | LR_const: forall n n',
    derive n' conf = Some n ->
    LR conf (const n) (const' n')
  | LR_succ: forall t t',
    LR conf t t' ->
    LR conf (succ t) (succ' t')
  | LR_add: forall t1 t2 t1' t2',
    LR conf t1 t1' ->
    LR conf t2 t2' ->
    LR conf (add t1 t2) (add' t1' t2')
  | LR_nil: LR conf nil nil'
  | LR_cons: forall t h t' h',
    LR conf t t' ->
    LR conf h h' ->
    LR conf (cons t h) (cons' t' h')
  | LR_case: forall x y t tnil tcons t' tnil' tcons',
    LR conf t t' ->
    LR conf tnil tnil' ->
    LR conf tcons tcons' ->
    LR conf (case t tnil x y tcons) (case' t' tnil' x y tcons').

Lemma subst_LR_subst': forall conf t1 t1' t2 t2' s,
  LR conf t1 t1' ->
  LR conf t2 t2' ->
  LR conf (subst s t2 t1) (subst' s t2' t1').
Proof.
  intros conf t1 t1' t2 t2' s HLR.
  induction HLR; intros.
  - simpl. destruct (eqb_spec s x).
    assumption. constructor.
  - simpl. apply LR_app.
    + apply IHHLR1. assumption.
    + apply IHHLR2. assumption.
  - simpl. destruct (eqb_spec s x).
    + constructor. assumption.
    + constructor. apply IHHLR. assumption.
  - simpl. constructor.
    apply IHHLR. assumption.
  - simpl. constructor. assumption.
  - simpl. constructor.
    apply IHHLR. assumption.
  - simpl. apply LR_add.
    + apply IHHLR1. assumption.
    + apply IHHLR2. assumption.
  - simpl. constructor.
  - simpl. apply LR_cons.
    + apply IHHLR1. assumption.
    + apply IHHLR2. assumption.
  - simpl. destruct (eqb_spec s x), (eqb_spec s y);
      simpl; constructor; eauto.
Qed.

Lemma value_LR_value': forall conf t t',
  LR conf t t' ->
  value t <->
  value' t'.
Proof.
  intros conf t t' HLR. split.
  - intro H.
    generalize dependent t'.
    induction H; intros; subst;
    try inversion HLR; constructor.
    + apply IHvalue1; assumption.
    + apply IHvalue2; assumption.
  - intro H.
    generalize dependent t.
    induction H; intros; subst;
    try inversion HLR; constructor.
    + apply IHvalue'1; assumption.
    + apply IHvalue'2; assumption.
Qed.

Lemma step_LR_step': forall conf t1 t2 t1' t2',
  LR conf t1 t1' -> LR conf t2 t2'.
Proof.
  intros conf t1 t2 t1' t2' Hstep Hstep' HLR.
  generalize dependent Hstep'.
  generalize dependent t2'.
  generalize dependent Hstep.
  generalize dependent t2.
  induction HLR; intros;
    try solve_by_inverts 1.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2.
    + constructor.
      * apply IHHLR1; assumption.
      * assumption.
    + inversion HLR1; subst.
      apply subst_LR_subst'; assumption. 
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + assumption.
    + constructor. assumption.
    + apply IHHLR; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + eapply IHHLR; assumption. 
    + apply mapping_not_change_deriving.
      inversion HLR. assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + apply IHHLR1; assumption.
    + assumption.
    + pose proof (value_LR_value' conf t1 t1' HLR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t1'0. assumption.
    + pose proof (value_LR_value' conf t1 t1' HLR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t1'0. assumption.
    + pose proof (value_LR_value' conf t1 t1' HLR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t1''. assumption.
    + pose proof (value_LR_value' conf t1 t1' HLR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t1''. assumption.
    + assumption.
    + apply IHHLR2; assumption.
    + apply binop_not_change_deriving.
      inversion HLR1; assumption.
      inversion HLR2; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + apply IHHLR1; assumption.
    + assumption.
    + pose proof (value_LR_value' conf t t' HLR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t0. assumption.
    + pose proof (value_LR_value' conf t t' HLR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t0. assumption.
    + pose proof (value_LR_value' conf t t' HLR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t2'0. assumption.
    + pose proof (value_LR_value' conf t t' HLR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t2'0. assumption.
    + assumption.
    + apply IHHLR2; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor;
    try assumption.
    + apply IHHLR1; assumption.
    + pose proof (v_lcons' vh' vt' H12 H13).
      pose proof (value_LR_value' conf t (cons' vh' vt') HLR1)
      as [_ H1]. apply H1 in H.
      exfalso. apply value_is_nf in H.
      apply H. exists t0. assumption.
    + pose proof (v_lcons vh vt H5 H6).
      pose proof (value_LR_value' conf (cons vh vt) t' HLR1)
      as [H1 _]. apply H1 in H.
      exfalso. apply value'_is_nf in H.
      apply H. exists t2'0. assumption.
    + repeat (apply subst_LR_subst').
      * assumption.
      * inversion HLR1; subst. assumption.
      * inversion HLR1; subst. assumption.
Qed.

Lemma LR_step: forall conf t1 t1' t2,
  LR conf t1 t1' -> step t1 t2 -> exists t2', step' t1' t2'.
Proof.
  intros conf t1 t1' t2 HLR; generalize dependent t2.
  induction HLR; intros t21 Hstep; inversion Hstep; subst.
  - apply IHHLR1 in H2 as []. eexists. apply ST_App'. eassumption.
  - inversion HLR1; subst. eexists. apply ST_AppAbs'.
  - inversion HLR; subst. eexists. apply ST_FixpAbs'.
  - apply IHHLR in H0 as []. eexists. apply ST_Fixp'. eassumption.
  - apply IHHLR in H0 as []. eexists. apply ST_Succ'. eassumption.
  - inversion HLR; subst. eexists. apply ST_SuccConst'.
  - apply IHHLR1 in H2 as []. eexists. apply ST_Add1'. eassumption.
  - apply IHHLR2 in H3 as []. eexists. apply ST_Add2'.
    + rewrite value_LR_value' in H1; eassumption.
    + eassumption.
  - inversion HLR1; inversion HLR2; subst. eexists. apply ST_AddConst'.
  - apply IHHLR1 in H2 as []. eexists. apply ST_Cons1'. eassumption.
  - apply IHHLR2 in H3 as []. eexists. apply ST_Cons2'.
    + rewrite value_LR_value' in H1; eassumption.
    + eassumption.
  - apply IHHLR1 in H5 as []. eexists. apply ST_Case1'. eassumption.
  - inversion HLR1; subst. eexists. apply ST_CaseNil'.
  - inversion HLR1; subst. eexists. apply ST_CaseCons'.
    + rewrite value_LR_value' in H5; eassumption.
    + rewrite value_LR_value' in H6; eassumption.
Qed.

Lemma LR_step': forall conf t1 t1' t2',
  LR conf t1 t1' -> step' t1' t2' -> exists t2, step t1 t2.
Proof.
  intros conf t1 t1' t2 HLR; generalize dependent t2.
  induction HLR; intros t21 Hstep; inversion Hstep; subst.
  - apply IHHLR1 in H2 as []. eexists. apply ST_App. eassumption.
  - inversion HLR1; subst. eexists. apply ST_AppAbs.
  - inversion HLR; subst. eexists. apply ST_FixpAbs.
  - apply IHHLR in H0 as []. eexists. apply ST_Fixp. eassumption.
  - apply IHHLR in H0 as []. eexists. apply ST_Succ. eassumption.
  - inversion HLR; subst. eexists. apply ST_SuccConst.
  - apply IHHLR1 in H2 as []. eexists. apply ST_Add1. eassumption.
  - apply IHHLR2 in H3 as []. eexists. apply ST_Add2.
    + rewrite <- value_LR_value' in H1; eassumption.
    + eassumption.
  - inversion HLR1; inversion HLR2; subst. eexists. apply ST_AddConst.
  - apply IHHLR1 in H2 as []. eexists. apply ST_Cons1. eassumption.
  - apply IHHLR2 in H3 as []. eexists. apply ST_Cons2.
    + rewrite <- value_LR_value' in H1; eassumption.
    + eassumption.
  - apply IHHLR1 in H5 as []. eexists. apply ST_Case1. eassumption.
  - inversion HLR1; subst. eexists. apply ST_CaseNil.
  - inversion HLR1; subst. eexists. apply ST_CaseCons.
    + rewrite <- value_LR_value' in H5; eassumption.
    + rewrite <- value_LR_value' in H6; eassumption.
Qed.

Corollary LR_reducible_iff: forall conf t1 t1',
  LR conf t1 t1' ->
  (exists t2, step t1 t2) <-> (exists t2', step' t1' t2').
Proof.
  intros. split.
  - intros [t2 Hs]. eapply LR_step_forward; eauto.
  - intros [t2' Hs']. eapply LR_step_backward; eauto.
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

Theorem determinism : forall t1 t2 t3,
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

Ltac value'_no_step :=
	match goal with
	| [ H1: value' ?t, H2: step' ?t  _ |- _ ] =>
		exfalso; apply value'_is_nf in H1 as [_ H1]; eauto
	| [ H1: value' ?t1, H2: value' ?t2, H3: step' (cons' ?t1 ?t2) _ |- _] =>
    inversion H3; subst; exfalso;
             apply value'_is_nf in H1 as [_ H1];
             apply value'_is_nf in H2 as [_ H2]; eauto
  end.

Theorem determinism' : forall t1' t2' t3',
  step' t1' t2' -> step' t1' t3' -> t2' = t3'.
Proof.
  intros t1' t2' t3' Ht.
  generalize dependent t3'.
  induction Ht; intros t4' Ht';
    inversion Ht'; subst; eauto;
    try value'_no_step;
    try (f_equal; eauto);
    try solve_by_inverts 1.
Qed.

Lemma mstep_mstep'__LR: forall conf t1 t1' t2 t2',
  LR conf t1 t1' ->
  step_normal_form_of t1 t2 ->
  step'_normal_form_of t1' t2' ->
  LR conf t2 t2'.
Proof.
  intros conf t1 t1' t2 t2' HLR [Hm1 Hnf1] [Hm2 Hnf2].
  generalize dependent t2'.
  generalize dependent t1'.
  induction Hm1 as [ t1 | t1 t3 t2 Hstep1 Hm1' IH ];
    intros t1' HLR t2' Hm2 Hnf2.

  - (* t1 already stuck *)
    inversion Hm2; subst.
    + assumption.
    + exfalso. apply Hnf1.
      eapply LR_step'; eauto.

  - (* t1 --> t3 --> ... --> t2 *)
    assert (Hex1' : exists t3', step' t1' t3')
      by (eapply LR_step; eauto).
    destruct Hex1' as [t3' Hstep1'].
    assert (HLR3 : LR conf t3 t3') by (eapply step_LR_step'; eauto).
    inversion Hm2; subst.
    + exfalso. apply Hnf2. exists t3'. assumption.
    + pose proof (determinism' t1' t3' y Hstep1' H).
      subst. eapply IH; eauto.
Qed.

Lemma derive_LR: forall conf n' n,
  derive n' conf = Some n ->
  LR conf (const n) (const' n').
Proof.
  intros. constructor. assumption.
Qed.

(* Lemmas about other variations of derivation functions *)

Lemma derive'_LR: forall conf t' t,
  derive' conf t' = Some t ->
  LR conf t t'.
Proof.
  induction t'; intros;
  try discriminate.
  - simpl in H.
    destruct (derive n conf) eqn:Heq;
    try discriminate.
    apply derive_LR in Heq.
    injection H as H. subst.
    assumption.
  - simpl in H. injection H as H.
    subst. constructor.
  - simpl in H.
    destruct (derive' conf t'1) eqn:Heq1;
    try discriminate.
    destruct (derive' conf t'2) eqn:Heq2;
    try discriminate.
    injection H as H.
    rewrite <- H.
    constructor.
    + apply IHt'1; reflexivity.
    + apply IHt'2; reflexivity.
Qed.

Lemma derive'_canonical_forms: forall conf t t',
  derive' conf t' = Some t ->
  (exists n n',  t = (const n) /\ t' = (const' n')) \/
  (t = nil /\ t' = nil') \/
  (exists x xs x' xs', t = (cons x xs) /\ t' = (cons' x' xs')).
Proof.
  intros conf t t' Hd.
  destruct t'; intros;
  try solve_by_inverts 1.
  (* const *)
  - left. simpl in Hd.
    destruct (derive n conf);
    try discriminate.
    injection Hd as Hd.
    exists n0, n.
    split; auto.
  (* nil *)
  - right. left.
    simpl in Hd.
    injection Hd as Hd.
    split; auto.
  (* cons *)
  - right. right.
    simpl in Hd.
    destruct (derive' conf t'1);
    try discriminate.
    destruct (derive' conf t'2);
    try discriminate.
    injection Hd as Hd.
    exists t0, t1, t'1, t'2.
    split; auto.
Qed.

Lemma term_derivation_LR: forall conf t' t,
  term_derivation conf t' = Some t ->
  LR conf t t'.
Proof.
  induction t'; intros;
  try (injection H as H; subst; constructor);
  simpl in H.
  (* abs *)
  - destruct (term_derivation conf t');
    try discriminate.
    injection H as H.
    rename t into T'.
    remember (type_derivation T') as T.
    symmetry in HeqT.
    rewrite inv_ty_ld in HeqT.
    subst. constructor.
    apply IHt'. reflexivity.
  (* app *)
  - destruct (term_derivation conf t'1);
    try discriminate.
    destruct (term_derivation conf t'2);
    try discriminate.
    injection H as H.
    subst. constructor.
    + apply IHt'1. reflexivity.
    + apply IHt'2. reflexivity.
  (* fixp *)
  - destruct (term_derivation conf t');
    try discriminate.
    injection H as H.
    subst. constructor.
    apply IHt'. reflexivity.
  (* const *)
  - destruct (derive n conf) eqn:Hd;
    try discriminate.
    injection H as H.
    subst.
    constructor. assumption.
  (* succ *)
  - destruct (term_derivation conf t');
    try discriminate.
    injection H as H.
    subst. constructor.
    apply IHt'. reflexivity.
  (* add *)
  - destruct (term_derivation conf t'1);
    try discriminate.
    destruct (term_derivation conf t'2);
    try discriminate.
    injection H as H.
    subst. constructor.
    + apply IHt'1. reflexivity.
    + apply IHt'2. reflexivity.
  (* cons *)
  - destruct (term_derivation conf t'1);
    try discriminate.
    destruct (term_derivation conf t'2);
    try discriminate.
    injection H as H.
    subst. constructor.
    + apply IHt'1. reflexivity.
    + apply IHt'2. reflexivity.
  (* case *)
  - destruct (term_derivation conf t'1);
    try discriminate.
    destruct (term_derivation conf t'2);
    try discriminate.
    destruct (term_derivation conf t'3);
    try discriminate.
    injection H as H.
    subst. constructor.
    + apply IHt'1. reflexivity.
    + apply IHt'2. reflexivity.
    + apply IHt'3. reflexivity.
Qed.

Lemma LR_term_derivation: forall conf t' t,
  LR conf t t' ->
  term_derivation conf t' = Some t.
Proof.
  intros. induction H; simpl.
  - reflexivity.
  - rewrite IHLR1, IHLR2. reflexivity.
  - rewrite IHLR.
    rewrite ty_derivation_inv_of_lift_ty.
    reflexivity.
  - rewrite IHLR. reflexivity.
  - rewrite H. reflexivity.
  - rewrite IHLR. reflexivity.
  - rewrite IHLR1, IHLR2. reflexivity.
  - reflexivity.
  - rewrite IHLR1, IHLR2. reflexivity.
  - rewrite IHLR1, IHLR2, IHLR3. reflexivity.
Qed.

(* Trivially a term is always related to its lifted counterpart. *)

Lemma lift_LR: forall conf t,
  LR conf t (lift t).
Proof.
  induction t;
  try (constructor; assumption).
  - constructor. reflexivity.
Qed.

(* LR implies derivation existance *)

Lemma LR_derive: forall conf n n',
  LR conf (const n) (const' n') ->
  derive n' conf = Some n.
Proof.
  intros. inversion H. assumption.
Qed. 

(* The main commutativity theorem *)

Theorem commutativity: forall conf analysis spl p r r',
  derive spl conf = Some p ->
  step_normal_form_of (app analysis (const p)) (const r) ->
  step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_derive.
  assumption.
Qed.

(* Variations of the commutativity theorem *)

Theorem arbitrary_results_commutativity: forall conf analysis spl p r r',
  term_derivation conf spl = Some p ->
  step_normal_form_of (app analysis p) r ->
  step'_normal_form_of (app' (lift analysis) spl) r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (term_derivation_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_term_derivation.
  assumption.
Qed.

Theorem commutativity': forall conf analysis spl p r r',
  derive' conf spl = Some p ->
  step_normal_form_of (app analysis p) r ->
  step'_normal_form_of (app' (lift analysis) spl) r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (derive'_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_term_derivation.
  assumption.
Qed.

(* Proving the Commutativity Theorem
    with only 2 given hypothesis *)

Lemma mstep__LRL: forall conf t t' v,
  LR conf t t' ->
  step_normal_form_of t v ->
  exists v', step'_normal_form_of t' v' /\
  LR conf v v'.
Proof.
Admitted.

Lemma mstep__LRR: forall conf t t' v',
  LR conf t t' ->
  step'_normal_form_of t' v' ->
  exists v, step_normal_form_of t v /\
  LR conf v v'.
Proof.
Admitted.

Theorem commutativityL: forall conf analysis spl p r,
  derive spl conf = Some p ->
  step_normal_form_of (app analysis (const p)) (const r) ->
  exists r', step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') /\
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r Hd Hms.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep__LRL _ _ _ _ H1 Hms) as [v' [H2 H3]].
  inversion H3; subst.
  eexists; split; eassumption.
Qed.

Theorem commutativityR: forall conf analysis spl p r',
  derive spl conf = Some p ->
  step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
  exists r, step_normal_form_of (app analysis (const p)) (const r)  /\
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r' Hd Hms'.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep__LRR _ _ _ _ H1 Hms') as [v [H2 H3]].
  inversion H3; subst.
  eexists; split; eassumption.
Qed.

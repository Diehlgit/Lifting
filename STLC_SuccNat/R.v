From STLC Require Import PCFm Lifted_PCFm Derivation.

Inductive R (conf:feat_config) : tm -> tm' -> Prop :=
  | R_var: forall x, R conf (var x) (var' x)
  | R_app: forall t1 t2 t1' t2',
    R conf t1 t1' ->
    R conf t2 t2' ->
    R conf (app t1 t2) (app' t1' t2')
  | R_abs: forall x T t t',
    R conf t t' ->
    R conf (abs x T t) (abs' x (lift_ty T) t')
  | R_fixp: forall t t',
    R conf t t' -> R conf (fixp t) (fixp' t')
  | R_const: forall n n',
    derive n' conf = Some n ->
    R conf (const n) (const' n')
  | R_succ: forall t t',
    R conf t t' ->
    R conf (succ t) (succ' t')
  | R_add: forall t1 t2 t1' t2',
    R conf t1 t1' ->
    R conf t2 t2' ->
    R conf (add t1 t2) (add' t1' t2')
  | R_nil: R conf nil nil'
  | R_cons: forall t h t' h',
    R conf t t' ->
    R conf h h' ->
    R conf (cons t h) (cons' t' h')
  | R_case: forall x y t tnil tcons t' tnil' tcons',
    R conf t t' ->
    R conf tnil tnil' ->
    R conf tcons tcons' ->
    R conf (case t tnil x y tcons) (case' t' tnil' x y tcons').

Lemma subst_R_subst': forall conf t1 t1' t2 t2' s,
  R conf t1 t1' ->
  R conf t2 t2' ->
  R conf (subst s t2 t1) (subst' s t2' t1').
Proof.
  intros conf t1 t1' t2 t2' s HR.
  induction HR; intros.
  - simpl. destruct (eqb_spec s x).
    assumption. constructor.
  - simpl. apply R_app.
    + apply IHHR1. assumption.
    + apply IHHR2. assumption.
  - simpl. destruct (eqb_spec s x).
    + constructor. assumption.
    + constructor. apply IHHR. assumption.
  - simpl. constructor.
    apply IHHR. assumption.
  - simpl. constructor. assumption.
  - simpl. constructor.
    apply IHHR. assumption.
  - simpl. apply R_add.
    + apply IHHR1. assumption.
    + apply IHHR2. assumption.
  - simpl. constructor.
  - simpl. apply R_cons.
    + apply IHHR1. assumption.
    + apply IHHR2. assumption.
  - simpl. destruct (eqb_spec s x), (eqb_spec s y);
      simpl; constructor; eauto.
Qed.

Lemma value_R_value': forall conf t t',
  R conf t t' ->
  value t <->
  value' t'.
Proof.
  intros conf t t' HR. split.
  - intro H.
    generalize dependent t'.
    induction H; intros; subst;
    try inversion HR; constructor.
    + apply IHvalue1; assumption.
    + apply IHvalue2; assumption.
  - intro H.
    generalize dependent t.
    induction H; intros; subst;
    try inversion HR; constructor.
    + apply IHvalue'1; assumption.
    + apply IHvalue'2; assumption.
Qed.

Lemma R_step: forall conf t1 t1' t2,
  R conf t1 t1' -> step t1 t2 -> exists t2', step' t1' t2'.
Proof.
  intros conf t1 t1' t2 HR; generalize dependent t2.
  induction HR; intros t21 Hstep; inversion Hstep; subst.
  - apply IHHR1 in H2 as []. eexists. apply ST_App'. eassumption.
  - inversion HR1; subst. eexists. apply ST_AppAbs'.
  - inversion HR; subst. eexists. apply ST_FixpAbs'.
  - apply IHHR in H0 as []. eexists. apply ST_Fixp'. eassumption.
  - apply IHHR in H0 as []. eexists. apply ST_Succ'. eassumption.
  - inversion HR; subst. eexists. apply ST_SuccConst'.
  - apply IHHR1 in H2 as []. eexists. apply ST_Add1'. eassumption.
  - apply IHHR2 in H3 as []. eexists. apply ST_Add2'.
    + rewrite value_R_value' in H1; eassumption.
    + eassumption.
  - inversion HR1; inversion HR2; subst. eexists. apply ST_AddConst'.
  - apply IHHR1 in H2 as []. eexists. apply ST_Cons1'. eassumption.
  - apply IHHR2 in H3 as []. eexists. apply ST_Cons2'.
    + rewrite value_R_value' in H1; eassumption.
    + eassumption.
  - apply IHHR1 in H5 as []. eexists. apply ST_Case1'. eassumption.
  - inversion HR1; subst. eexists. apply ST_CaseNil'.
  - inversion HR1; subst. eexists. apply ST_CaseCons'.
    + rewrite value_R_value' in H5; eassumption.
    + rewrite value_R_value' in H6; eassumption.
Qed.

Lemma R_step': forall conf t1 t1' t2',
  R conf t1 t1' -> step' t1' t2' -> exists t2, step t1 t2.
Proof.
  intros conf t1 t1' t2 HR; generalize dependent t2.
  induction HR; intros t21 Hstep; inversion Hstep; subst.
  - apply IHHR1 in H2 as []. eexists. apply ST_App. eassumption.
  - inversion HR1; subst. eexists. apply ST_AppAbs.
  - inversion HR; subst. eexists. apply ST_FixpAbs.
  - apply IHHR in H0 as []. eexists. apply ST_Fixp. eassumption.
  - apply IHHR in H0 as []. eexists. apply ST_Succ. eassumption.
  - inversion HR; subst. eexists. apply ST_SuccConst.
  - apply IHHR1 in H2 as []. eexists. apply ST_Add1. eassumption.
  - apply IHHR2 in H3 as []. eexists. apply ST_Add2.
    + rewrite <- value_R_value' in H1; eassumption.
    + eassumption.
  - inversion HR1; inversion HR2; subst. eexists. apply ST_AddConst.
  - apply IHHR1 in H2 as []. eexists. apply ST_Cons1. eassumption.
  - apply IHHR2 in H3 as []. eexists. apply ST_Cons2.
    + rewrite <- value_R_value' in H1; eassumption.
    + eassumption.
  - apply IHHR1 in H5 as []. eexists. apply ST_Case1. eassumption.
  - inversion HR1; subst. eexists. apply ST_CaseNil.
  - inversion HR1; subst. eexists. apply ST_CaseCons.
    + rewrite <- value_R_value' in H5; eassumption.
    + rewrite <- value_R_value' in H6; eassumption.
Qed.

Corollary R_redux_iff: forall conf t1 t1',
  R conf t1 t1' ->
  (exists t2, step t1 t2) <-> (exists t2', step' t1' t2').
Proof.  
  intros. split.
  - intros [t2 Hs]. eapply R_step; eauto.
  - intros [t2' Hs']. eapply R_step'; eauto.
Qed.

Lemma step_R_step': forall conf t1 t2 t1' t2',
  step t1 t2 -> step' t1' t2' ->
  R conf t1 t1' -> R conf t2 t2'.
Proof.
  intros conf t1 t2 t1' t2' Hstep Hstep' HR.
  generalize dependent Hstep'.
  generalize dependent t2'.
  generalize dependent Hstep.
  generalize dependent t2.
  induction HR; intros;
    try solve_by_inverts 1.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2.
    + constructor.
      * apply IHHR1; assumption.
      * assumption.
    + inversion HR1; subst.
      apply subst_R_subst'; assumption. 
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + assumption.
    + constructor. assumption.
    + apply IHHR; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + eapply IHHR; assumption. 
    + apply mapping_not_change_deriving.
      inversion HR. assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + apply IHHR1; assumption.
    + assumption.
    + pose proof (value_R_value' conf t1 t1' HR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t1'0. assumption.
    + pose proof (value_R_value' conf t1 t1' HR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t1'0. assumption.
    + pose proof (value_R_value' conf t1 t1' HR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t1''. assumption.
    + pose proof (value_R_value' conf t1 t1' HR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t1''. assumption.
    + assumption.
    + apply IHHR2; assumption.
    + apply binop_not_change_deriving.
      inversion HR1; assumption.
      inversion HR2; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor.
    + apply IHHR1; assumption.
    + assumption.
    + pose proof (value_R_value' conf t t' HR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t0. assumption.
    + pose proof (value_R_value' conf t t' HR1)
      as [_ H]. apply H in H5.
      exfalso. apply value_is_nf in H5.
      apply H5. exists t0. assumption.
    + pose proof (value_R_value' conf t t' HR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t2'0. assumption.
    + pose proof (value_R_value' conf t t' HR1)
      as [H _]. apply H in H1.
      exfalso. apply value'_is_nf in H1.
      apply H1. exists t2'0. assumption.
    + assumption.
    + apply IHHR2; assumption.
  - inversion Hstep;
    inversion Hstep'; subst;
    try solve_by_inverts 2;
    try constructor;
    try assumption.
    + apply IHHR1; assumption.
    + pose proof (v_lcons' vh' vt' H12 H13).
      pose proof (value_R_value' conf t (cons' vh' vt') HR1)
      as [_ H1]. apply H1 in H.
      exfalso. apply value_is_nf in H.
      apply H. exists t0. assumption.
    + pose proof (v_lcons vh vt H5 H6).
      pose proof (value_R_value' conf (cons vh vt) t' HR1)
      as [H1 _]. apply H1 in H.
      exfalso. apply value'_is_nf in H.
      apply H. exists t2'0. assumption.
    + repeat (apply subst_R_subst').
      * assumption.
      * inversion HR1; subst. assumption.
      * inversion HR1; subst. assumption.
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

Ltac value'_no_step :=
	match goal with
	| [ H1: value' ?t, H2: step' ?t  _ |- _ ] =>
		exfalso; apply value'_is_nf in H1 as [_ H1]; eauto
	| [ H1: value' ?t1, H2: value' ?t2, H3: step' (cons' ?t1 ?t2) _ |- _] =>
    inversion H3; subst; exfalso;
             apply value'_is_nf in H1 as [_ H1];
             apply value'_is_nf in H2 as [_ H2]; eauto
  end.

Lemma mstep_mstep'__R: forall conf t1 t1' t2 t2',
  R conf t1 t1' ->
  step_normal_form_of t1 t2 ->
  step'_normal_form_of t1' t2' ->
  R conf t2 t2'.
Proof.
  intros conf t1 t1' t2 t2' HR [Hm1 Hnf1] [Hm2 Hnf2].
  generalize dependent t2'.
  generalize dependent t1'.
  induction Hm1 as [ t1 | t1 t3 t2 Hstep1 Hm1' IH ];
    intros t1' HR t2' Hm2 Hnf2.
  - inversion Hm2; subst.
    + assumption.
    + exfalso. apply Hnf1.
      eapply R_step'; eauto.
  - assert (Hex1' : exists t3', step' t1' t3')
      by (eapply R_step; eauto).
    destruct Hex1' as [t3' Hstep1'].
    assert (HR3 : R conf t3 t3') by (eapply step_R_step'; eauto).
    inversion Hm2; subst.
    + exfalso. apply Hnf2. exists t3'. assumption.
    + pose proof (determinism' t1' t3' y Hstep1' H).
      subst. eapply IH; eauto.
Qed.

(* derivation existance implies R *)
Lemma derive_R: forall conf n' n,
  derive n' conf = Some n ->
  R conf (const n) (const' n').
Proof.
  intros. constructor. assumption.
Qed.

(* R implies derivation existance *)
Lemma R_derive: forall conf n n',
  R conf (const n) (const' n') ->
  derive n' conf = Some n.
Proof.
  intros. inversion H. assumption.
Qed.

(* Both ways *)
Lemma derive_R_iff: forall conf n' n,
  derive n' conf = Some n <-> R conf (const n) (const' n').
Proof. split. apply derive_R. apply R_derive. Qed.


(* Lemmas about other implementations of derivation functions *)

(* derive' can derive both variational naturals and variational lists *)
Lemma derive'_R: forall conf t' t,
  derive' conf t' = Some t ->
  R conf t t'.
Proof.
  induction t'; intros;
  try discriminate.
  (* const *)
  - simpl in H.
    destruct (derive n conf) eqn:Heq;
    try discriminate.
    apply derive_R in Heq.
    injection H as H. subst.
    assumption.
  (* nil *)
  - simpl in H. injection H as H.
    subst. constructor.
  (* cons *)
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

(* The result of derive' can either be
   a natural, an empty list, or a populated list *)
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

(* The term_derivation function can derive any variational term
   it is not retricted to values of the language *)
Lemma term_derivation_R: forall conf t' t,
  term_derivation conf t' = Some t ->
  R conf t t'.
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

Lemma R_term_derivation: forall conf t' t,
  R conf t t' ->
  term_derivation conf t' = Some t.
Proof.
  intros. induction H; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR.
    rewrite ty_derivation_inv_of_lift_ty.
    reflexivity.
  - rewrite IHR. reflexivity.
  - rewrite H. reflexivity.
  - rewrite IHR. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2, IHR3. reflexivity.
Qed.

(* Trivially a term is always related to its lifted counterpart. *)

Lemma lift_R: forall conf t,
  R conf t (lift t).
Proof.
  induction t;
  try (constructor; assumption).
  - constructor. reflexivity.
Qed.

(* The main commutativity theorem *)

Theorem commutativity: forall conf analysis spl p r r',
  derive spl conf = Some p ->
  step_normal_form_of (app analysis (const p)) (const r) ->
  step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (derive_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__R _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply R_derive.
  assumption.
Qed.

(* Variations of the commutativity theorem *)

(* Using term derivation we can extend the commutativity theorem to
   reason about any enconding of Software Product Line, Products,
   Variational Results and Object Language Results *)
Theorem arbitrary_results_commutativity: forall conf analysis spl p r r',
  term_derivation conf spl = Some p ->
  step_normal_form_of (app analysis p) r ->
  step'_normal_form_of (app' (lift analysis) spl) r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (term_derivation_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__R _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply R_term_derivation.
  assumption.
Qed.

(* Using derive' we can extend the commutativity theorem to
   reason about enconding of SPls, Products and Results restricted
   to using Natural Values and Lists of Naturals Values *)
Theorem commutativity': forall conf analysis spl p r r',
  derive' conf spl = Some p ->
  step_normal_form_of (app analysis p) r ->
  step'_normal_form_of (app' (lift analysis) spl) r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf analysis spl p r r' Hd Hms Hms'.
  pose proof (derive'_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__R _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply R_term_derivation.
  assumption.
Qed.

(* Proving the Commutativity Theorem
    with only 2 given hypothesis *)

Lemma mstep__RL: forall conf t t' v,
  R conf t t' ->
  step_normal_form_of t v ->
  exists v', step'_normal_form_of t' v' /\
  R conf v v'.
Proof.
Admitted.

Lemma mstep__RR: forall conf t t' v',
  R conf t t' ->
  step'_normal_form_of t' v' ->
  exists v, step_normal_form_of t v /\
  R conf v v'.
Proof.
Admitted.

(* The Commutativity Theorem proven without assuming
   the existance of a normal form for the Lifted Language
   term  *)
Theorem commutativityL: forall conf analysis spl p r,
  derive spl conf = Some p ->
  step_normal_form_of (app analysis (const p)) (const r) ->
  exists r', step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') /\
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r Hd Hms.
  pose proof (derive_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep__RL _ _ _ _ H1 Hms) as [v' [H2 H3]].
  inversion H3; subst.
  eexists; split; eassumption.
Qed.

(* The Commutativity Theorem proven without assuming
   the existance of a normal form for the Object Language
   term  *)
Theorem commutativityR: forall conf analysis spl p r',
  derive spl conf = Some p ->
  step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
  exists r, step_normal_form_of (app analysis (const p)) (const r)  /\
  derive r' conf = Some r.
Proof.
  intros conf analysis spl p r' Hd Hms'.
  pose proof (derive_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep__RR _ _ _ _ H1 Hms') as [v [H2 H3]].
  inversion H3; subst.
  eexists; split; eassumption.
Qed.

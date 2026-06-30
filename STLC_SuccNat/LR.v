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

Lemma step_LR_step': forall conf t t',
  LR conf t t' -> LR conf (step t) (step' t').
Proof.
  induction t; intros;
  inversion H; subst.
  - constructor.
  - constructor. assumption.
  - destruct t1, t1';
    try solve_by_inverts 1;
    try (apply IHt1 in H2;
         constructor; assumption).
    simpl in *. inversion H2; subst.
    eapply subst_LR_subst'; assumption.
  - destruct t, t'0;
    try solve_by_inverts 1;
    try (apply IHt in H1;
         constructor; assumption).
    inversion H1; subst.
    eapply subst_LR_subst'; assumption.
  - constructor. assumption.
  - destruct t, t'0;
    try solve_by_inverts 1;
    try (apply IHt in H1;
         constructor; assumption).
    inversion H1; subst.
    simpl. constructor.
    apply mapping_not_change_deriving.
    assumption.
- destruct t1, t1';
    try solve_by_inverts 1;
    try (apply IHt1 in H2;
         constructor; assumption).
  destruct t2, t2';
    try solve_by_inverts 1;
    try (apply IHt2 in H4;
         constructor; assumption).
  simpl in *. 
  inversion H2; subst.
  inversion H4; subst.
  constructor.
  apply binop_not_change_deriving; assumption.
- constructor.
- destruct t1, t'0;
    try solve_by_inverts 1;
    try (apply IHt1 in H2;
         constructor; assumption).
  destruct t2, h';
    try solve_by_inverts 1;
    try (apply IHt2 in H4;
         constructor; assumption).
- destruct t1, t'0;
    try solve_by_inverts 1;
    try (simpl; assumption);
    try (apply IHt1 in H6;
         constructor; assumption).
    simpl. inversion H6; subst.
    repeat apply subst_LR_subst'; assumption.
Qed.

Lemma LR_is_terminal_eqv: forall conf t t',
  LR conf t t' ->
  is_terminal t = true <->
  is_terminal' t' = true.
Proof.
  intros conf t t' HLR.
  split; intro Ht;
  induction HLR;
  try reflexivity;
  try discriminate;
  inversion Ht;
  rewrite H0;
  apply Bool.andb_true_iff in H0 as [];
  apply IHHLR1 in H;
  apply IHHLR2 in H0;
  simpl; rewrite H, H0;
  reflexivity.
Qed.

Lemma mstep_mstep'__LR: forall conf i t t' v v',
  LR conf t t' ->
  mstep i t = Some v ->
  mstep' i t' = Some v' ->
  LR conf v v'.
Proof.
 induction i; intros t t' v v' HLR Hms Hms'.
  - simpl in Hms, Hms'.
    destruct (is_terminal t) eqn:Eqt;
    try discriminate.
    rewrite (LR_is_terminal_eqv _ _ _ HLR) in Eqt.
    rewrite Eqt in Hms'.
    injection Hms as Hms.
    injection Hms' as Hms'.
    subst. assumption.
  - eapply IHi.
    + eapply step_LR_step' in HLR.
      exact HLR.
    + pose proof (mstep_Si i t v) as [H _].
      apply H. assumption.
    + pose proof (mstep'_Si i t' v')as [H _].
      apply H. exact Hms'.
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

Theorem commutativity: forall conf i analysis spl p r r',
  derive spl conf = Some p ->
  mstep i (app analysis (const p)) = Some (const r) ->
  mstep' i (app' (lift analysis) (const' spl)) = Some (const' r') ->
  derive r' conf = Some r.
Proof.
  intros conf i analysis spl p r r' Hd Hms Hms'.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_derive.
  assumption.
Qed.

(* Variations of the commutativity theorem *)

Theorem arbitrary_results_commutativity: forall conf i analysis spl p r r',
  term_derivation conf spl = Some p ->
  mstep i (app analysis p) = Some r ->
  mstep' i (app' (lift analysis) spl) = Some r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf i analysis spl p r r' Hd Hms Hms'.
  pose proof (term_derivation_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_term_derivation.
  assumption.
Qed.

Theorem commutativity': forall conf i analysis spl p r r',
  derive' conf spl = Some p ->
  mstep i (app analysis p) = Some r ->
  mstep' i (app' (lift analysis) spl) = Some r' ->
  term_derivation conf r' = Some r.
Proof.
  intros conf i analysis spl p r r' Hd Hms Hms'.
  pose proof (derive'_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep_mstep'__LR _ _ _ _ _ _ H1 Hms Hms').
  clear - H2.
  apply LR_term_derivation.
  assumption.
Qed.

(* Proving the Commutativity Theorem
    with only 2 given hypothesis *)

Lemma mstep__LRL: forall conf i t t' v,
  LR conf t t' ->
  mstep i t = Some v ->
  exists v', mstep' i t' = Some v' /\
  LR conf v v'.
Proof.
 induction i; intros t t' v HLR Hms.
  - simpl in Hms.
    destruct (is_terminal t) eqn:Eqt;
    try discriminate.
    rewrite (LR_is_terminal_eqv _ _ _ HLR) in Eqt.
    exists t'. simpl.
    rewrite Eqt.
    split.
    reflexivity.
    injection Hms as Hms.
    subst. assumption.
  - eapply step_LR_step' in HLR.
    eapply IHi in HLR as [v' [H1 H2]].
    + exists v'. split.
      apply mstep'_Si.
      assumption. eassumption.
    + pose proof (mstep_Si i t v) as [H _].
      apply H. assumption.
Qed.

Lemma mstep__LRR: forall conf i t t' v',
  LR conf t t' ->
  mstep' i t' = Some v' ->
  exists v, mstep i t = Some v /\
  LR conf v v'.
Proof.
 induction i; intros t t' v' HLR Hms.
  - simpl in Hms.
    destruct (is_terminal' t') eqn:Eqt;
    try discriminate.
    rewrite <- (LR_is_terminal_eqv _ _ _ HLR) in Eqt.
    exists t. simpl.
    rewrite Eqt.
    split.
    reflexivity.
    injection Hms as Hms.
    subst. assumption.
  - eapply step_LR_step' in HLR.
    eapply IHi in HLR as [v [H1 H2]].
    + exists v. split.
      apply mstep_Si.
      assumption. eassumption.
    + pose proof (mstep'_Si i t' v') as [H _].
      apply H. assumption.
Qed.

Theorem commutativityL: forall conf i analysis spl p r,
  derive spl conf = Some p ->
  mstep i (app analysis (const p)) = Some (const r) ->
  exists r', mstep' i (app' (lift analysis) (const' spl)) = Some (const' r') /\
  derive r' conf = Some r.
Proof.
  intros conf i analysis spl p r Hd Hms.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep__LRL _ _ _ _ _ H1 Hms) as [v' [H2 H3]].
  inversion H3; subst.
  eexists; split.
  + rewrite H2. reflexivity.
  + assumption.
Qed.

Theorem commutativityR: forall conf i analysis spl p r',
  derive spl conf = Some p ->
  mstep' i (app' (lift analysis) (const' spl)) = Some (const' r') ->
  exists r, mstep i (app analysis (const p)) = Some (const r)  /\
  derive r' conf = Some r.
Proof.
  intros conf i analysis spl p r' Hd Hms'.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mstep__LRR _ _ _ _ _ H1 Hms') as [v [H2 H3]].
  inversion H3; subst.
  eexists; split.
  + rewrite H2. reflexivity.
  + assumption.
Qed.

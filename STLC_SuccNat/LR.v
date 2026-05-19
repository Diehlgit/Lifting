From STLC Require Import Ceval Lifted_Ceval.

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
    LR conf (succ t) (succ' t').

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
Qed.

Lemma cstep_LR_cstep': forall conf t t',
  LR conf t t' -> LR conf (cstep t) (cstep' t').
Proof.
  induction t; intros;
  inversion H; subst.
  - constructor.
  - destruct t1, t1';
    try solve_by_inverts 1;
    try (apply IHt1 in H2;
         constructor; assumption).
    simpl in *. inversion H2; subst.
    eapply subst_LR_subst'; assumption.
  - constructor. assumption.
  - destruct t, t'0;
    try solve_by_inverts 1;
    try (apply IHt in H1;
         constructor; assumption).
  - constructor. assumption.
  - destruct t, t'0;
    try solve_by_inverts 1;
    try (apply IHt in H1;
         constructor; assumption).
    inversion H1; subst.
    simpl. constructor.
    apply mapping_not_change_deriving.
    assumption.
Qed.

Lemma mcstep_mcstep'__LR: forall conf i t t' v v',
  LR conf t t' ->
  mcstep i t = Some v ->
  mcstep' i t' = Some v' ->
  LR conf v v'.
Proof.
 induction i; intros t t' v v' HLR Hmc Hmc'.
  - simpl in Hmc, Hmc'.
    destruct t, t'; subst;
    try discriminate;
    try (injection Hmc as Hmc;
    injection Hmc' as Hmc';
    subst; assumption).
  - eapply IHi.
    + eapply cstep_LR_cstep' in HLR.
      exact HLR.
    + pose proof (mcstep_Si i t v) as [H _].
      apply H. assumption.
    + pose proof (mcstep'_Si i t' v')as [H _].
      apply H. exact Hmc'.
Qed.

Lemma derive_LR: forall conf n' n,
  derive n' conf = Some n ->
  LR conf (const n) (const' n').
Proof.
  intros. constructor. assumption.
Qed.

Lemma lift_LR: forall conf t,
  LR conf t (lift t).
Proof.
  induction t;
  try (constructor; assumption).
  - constructor. reflexivity.
Qed.
 
Theorem commutativity: forall conf i analysis spl p r r',
  derive spl conf = Some p ->
  mcstep i (app analysis (const p)) = Some (const r) ->
  mcstep' i (app' (lift analysis) (const' spl)) = Some (const' r') ->
  derive r' conf = Some r.
Proof.
  intros conf i analysis spl p r r' Hd Hmc Hmc'.
  pose proof (derive_LR conf spl p Hd).
  pose proof (lift_LR conf analysis).
  pose proof (LR_app _ _ _ _ _ H0 H).
  pose proof (mcstep_mcstep'__LR _ _ _ _ _ _ H1 Hmc Hmc').
  clear - H2.
  inversion H2; subst.
  assumption.
Qed.
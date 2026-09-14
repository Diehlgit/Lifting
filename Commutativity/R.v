From Languages_Scheme Require Import PCFm_Base PCFm_Lifted.
Require Import Lifting.Lifting Derivation.Derivation.

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
    derive conf (const' n') = Some (const n) ->
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

(* Substituting related terms t2 and t2' in already related terms
   t1 and t1' yield related terms
   (The relation is preserved under substitution)*)
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
  (* app *)
  - inversion Hstep; subst.
    (* ST_App *)
    + rename t1'0 into t0.
      pose proof (R_redux_iff conf t1 t1' HR1) as [[t0' H] _]; eauto.
      pose proof (ST_App' t1' t0' t2' H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor; 
      [ apply IHHR1; assumption |
        assumption ].
    (* ST_AppAbs *)
    + inversion HR1; subst.
      inversion Hstep'; subst.
      inversion H2.
      apply subst_R_subst'; assumption.
  (* fixp *)
  - inversion Hstep; subst.
    (* ST_FixpAbs *)
    + inversion HR; subst.
      inversion Hstep'; subst; try solve_by_inverts 1.
      repeat constructor; assumption.
    (* ST_Fixp *)
    + pose proof (R_redux_iff conf t t' HR) as [[t0' H] _]; eauto.
      pose proof (ST_Fixp' t' t0' H).
      pose proof (determinism' _ _ _ Hstep' H1); subst.
      constructor.
      apply IHHR; assumption.
  (* succ *)
  - inversion Hstep; subst.
    (* ST_Succ *)
    + pose proof (R_redux_iff conf t t' HR) as [[t0' H] _]; eauto.
      pose proof (ST_Succ' t' t0' H).
      pose proof (determinism' _ _ _ Hstep' H1); subst.
      constructor. auto.
    (* ST_SuccConst *)
    + inversion HR; subst.
      inversion Hstep'; subst; try solve_by_inverts 1.
      constructor. simpl.
      rewrite mapping_not_change_deriving with (p:=n).
      reflexivity. simpl in H0. 
      destruct (derive_primitive n' conf); try discriminate.
      injection H0 as H0. subst. reflexivity.
  (* add *)
  - inversion Hstep; subst.
    (* ST_Add1 *)
    + rename t1'0 into t0.
      pose proof (R_redux_iff _ _ _ HR1) as [[t0' H] _]; eauto.
      pose proof (ST_Add1' _ _ t2' H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor;
      [ apply IHHR1; assumption |
        assumption ].
    (* ST_Add2 *)
    + apply (value_R_value' _ _ _ HR1) in H1.
      pose proof (R_redux_iff _ _ _ HR2) as [[t2'1' H] _]; eauto.
      pose proof (ST_Add2' _ _ _ H1 H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor;
      [ assumption |
        apply IHHR2; assumption].
    (* ST_AddConst *)
    + inversion HR1;
      inversion HR2; subst.
      inversion Hstep';
        try solve_by_inverts 1; subst.
      clear - HR1 HR2 H0 H3.
      constructor. simpl.
      rewrite binop_not_change_deriving with (p1:=n1) (p2:=n2).
      * reflexivity.
      * simpl in H0. destruct (derive_primitive n' conf).
        inversion H0; subst. reflexivity.
        discriminate.
      * simpl in H3. destruct (derive_primitive n'0 conf).
        inversion H3; subst. reflexivity.
        discriminate.
  (* cons *)
  - inversion Hstep; subst.
    (* ST_Cons1 *)
    + pose proof (R_redux_iff _ _ _ HR1) as [[t0' H] _]; eauto.
      pose proof (ST_Cons1' _ _ h' H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor;
      [ apply IHHR1; assumption |
        assumption].
    (* ST_Cons2 *)
    + apply (value_R_value' _ _ _ HR1) in H1.
      pose proof (R_redux_iff _ _ _ HR2) as [[t3' H] _]; eauto.
      pose proof (ST_Cons2' _ _ _ H1 H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor;
      [ assumption |
        apply IHHR2; assumption].
  (* case *)
  - inversion Hstep; subst.
    (* ST_Case1 *)
    + pose proof (R_redux_iff _ _ _ HR1) as [[t0' H] _]; eauto.
      pose proof (ST_Case1' x y _ _ tnil' tcons' H).
      pose proof (determinism' _ _ _ Hstep' H0); subst.
      constructor; try assumption.
      apply IHHR1; assumption.
    (* ST_CaseNil *)
    + inversion HR1; subst.
      inversion Hstep';
        subst; try solve_by_inverts 1.
      assumption.
    (* ST_CaseCons *)
    + inversion HR1; subst.
      rename t'0 into vh', h' into vt'.
      apply (value_R_value' _ _ _ H1) in H5.
      apply (value_R_value' _ _ _ H3) in H6.
      inversion Hstep';
        subst; try value'_no_step.
      repeat apply subst_R_subst'; assumption.
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
(* Lemma derive_R: forall conf n' n,
  derive conf (const' n') = Some (const n) ->
  R conf (const n) (const' n').
Proof.
  intros. constructor. assumption.
Qed. *)

(* R implies derivation existance *)
(* Lemma R_derive: forall conf n n',
  R conf (const n) (const' n') ->
  derive conf (const' n') = Some (const n).
Proof.
  intros. inversion H. assumption.
Qed. *)

(* Both ways *)
(* Lemma derive_R_iff: forall conf n' n,
  derive conf (const' n') = Some (const n) <-> R conf (const n) (const' n').
Proof. split. apply derive_R. apply R_derive. Qed. *)


(* Lemmas about other implementations of derivation functions *)

(* derive' can derive both variational naturals and variational lists *)
Lemma derive_R: forall conf t' t,
  derive conf t' = Some t ->
  R conf t t'.
Proof.
  induction t'; intros;
  try discriminate.
  (* const *)
  - simpl in H.
    destruct (derive_primitive n conf) eqn:Heq;
    try discriminate.
    injection H as H. subst.
    constructor.
    simpl. rewrite Heq.
    reflexivity.
  (* nil *)
  - simpl in H. injection H as H.
    subst. constructor.
  (* cons *)
  - simpl in H.
    destruct (derive conf t'1) eqn:Heq1;
    try discriminate.
    destruct (derive conf t'2) eqn:Heq2;
    try discriminate.
    injection H as H.
    rewrite <- H.
    constructor.
    + apply IHt'1; reflexivity.
    + apply IHt'2; reflexivity.
Qed.

(* Trivially a term is always related to its lifted counterpart. *)

Lemma lift_R: forall conf t,
  R conf t (lift t).
Proof.
  induction t;
  try (constructor; assumption).
  - constructor. reflexivity.
Qed.

(* Analyses results are limted to number and list values.
   An analysis function that returns functions as analysis results
   is out of the scope of this theory. Although it should be 
   possible to reason about by extending the notion of derivation. *)

Inductive analysis_result: tm -> Prop :=
  | v_nat : forall n, analysis_result (const n)
  | v_lnil : analysis_result nil
  | v_lcons : forall v1 v2, analysis_result v1 ->
                            analysis_result v2 ->
                            analysis_result (cons v1 v2).

Lemma analysis_result_derives: forall conf r r',
  analysis_result r ->
  R conf r r' ->
  derive conf r' = Some r.
Proof.
  intros conf r r' Hr HR.
  generalize dependent r'.
  induction Hr; intros;
  inversion HR; subst.
  - assumption.
  - reflexivity.
  - apply IHHr2 in H3.
    inversion HR; subst.
    apply IHHr1 in H4.
    simpl. rewrite H4, H3.
    reflexivity.
Qed.

Lemma mstep__RL: forall conf t t' v,
  R conf t t' ->
  step_normal_form_of t v ->
  exists v', step'_normal_form_of t' v' /\
  R conf v v'.
Proof.
  intros conf t t' v HR [Hms Hnf].
  generalize dependent t'.
  induction Hms; intros t' HR.
  - eexists t'. split; [split|].
    + apply multi_refl.
    + intros Hstep.
      apply Hnf; clear Hnf.
      apply R_redux_iff in HR as [_ HR].
      apply HR, Hstep.
    + assumption.
  - pose proof (R_step _ _ _ _ HR H) as [y' H1].
    pose proof (step_R_step' _ _ _ _ _ H H1 HR).
    apply (IHHms Hnf) in H0.
    destruct H0 as [v' [[Hms' Hnf'] HR']].
    exists v'. split; [split|]; try assumption.
    eapply (multi_step _ _ _ _ H1) in Hms'.
    assumption.
Qed.

Theorem commutativity': forall conf analysis spl p r,
  derive conf spl = Some p ->
  analysis_result r ->
  step_normal_form_of (app analysis p) r ->
  exists r', step'_normal_form_of (app' (lift analysis) spl) r' /\
  derive conf r' = Some r.
Proof.
  intros conf analysis spl p r Hd Hr Hms.
  pose proof (derive_R conf spl p Hd).
  pose proof (lift_R conf analysis).
  pose proof (R_app _ _ _ _ _ H0 H).
  pose proof (mstep__RL _ _ _ _ H1 Hms) as [r' [H2 H3]].
  clear - H2 H3 Hr.
  pose proof (analysis_result_derives conf r r' Hr H3).
  exists r'; split;
  assumption.
Qed.

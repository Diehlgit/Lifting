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
    R conf h h' ->
    R conf t t' ->
    R conf (cons h t) (cons' h' t')
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

(* A related term is a value iff their counterpart
   is also a value *)
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

(* The two next lemmas state that if a related term is reducible
   so is their counterpart  *)

Lemma R_step: forall conf t1 t1',
  R conf t1 t1' -> forall t2, step t1 t2 -> exists t2', step' t1' t2'.
Proof.
  intros conf t1 t1' HR.
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

Lemma R_step': forall conf t1 t1',
  R conf t1 t1' -> forall t2', step' t1' t2' -> exists t2, step t1 t2.
Proof.
  intros conf t1 t1' HR.
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

(* The next lemma states that reducing related terms
   yields related terms *)
Lemma step_R_step' : forall conf t1 t1',
  R conf t1 t1' ->
  forall t2, step t1 t2 -> exists t2', R conf t2 t2'.
Proof.
  intros conf t1 t1' HR.
  induction HR; intros t20 Hstep;
    try solve_by_inverts 1.
  (* app *)
  - inversion Hstep; subst.
    (* ST_App *)
    + apply IHHR1 in H2 as [t' H2].
      exists (app' t' t2').
      constructor; assumption.
    (* ST_AppAbs *)
    + inversion HR1; subst.
      exists (subst' x t2' t').
      apply subst_R_subst'; assumption.
  (* fixp *)
  - inversion Hstep; subst.
    (* ST_FixpAbs *)
    + inversion HR; subst.
      eexists; repeat econstructor; eassumption.
    (* ST_Fixp *)
    + apply IHHR in H0 as [t2' H0].
      exists (fixp' t2').
      constructor. assumption.
  (* succ *)
  - inversion Hstep; subst.
    (* ST_Succ *)
    + apply IHHR in H0 as [t2' H0].
      exists (succ' t2').
      constructor. assumption.
    (* ST_SuccConst *)
    + inversion HR; subst.
      apply derive_to_primitive in H0.
      apply mapping_not_change_deriving with (f:=S) in H0.
      eexists. econstructor.
      simpl. erewrite H0.
      reflexivity.
  (* add *)
  - inversion Hstep; subst.
    (* ST_Add1 *)
    + rename t1'0 into t0.
      apply IHHR1 in H2 as [t0' H2].
      exists (add' t0' t2').
      constructor; assumption.
    (* ST_Add2 *)
    + rename t2'0 into t3.
      apply IHHR2 in H3 as [t3' H3].
      exists (add' t1' t3').
      constructor; assumption.
    (* ST_AddConst *)
    + clear IHHR1 IHHR2.
      inversion HR1;
      inversion HR2; subst.
      exists (const' (app_binop Nat.add n' n'0)).
      apply derive_to_primitive in H0, H3.
      pose proof (binop_not_change_deriving _ _ _ _ _ Nat.add H0 H3).
      constructor. simpl.
      rewrite H. reflexivity.
  (* cons *)
  - inversion Hstep; subst.
    (* ST_Cons1 *)
    + apply IHHR1 in H2 as [t2' H].
      exists (cons' t2' t').
      constructor; assumption.
    (* ST_Cons2 *)
    + apply (value_R_value' _ _ _ HR1) in H1.
      apply IHHR2 in H3 as [t3' H].
      exists (cons' h' t3').
      constructor; assumption.
  (* case *)
  - inversion Hstep; subst.
    (* ST_Case1 *)
    + apply IHHR1 in H5 as [t2' H5].
    exists (case' t2' tnil' x y tcons').
    constructor; assumption.
    (* ST_CaseNil *)
    + exists tnil'. assumption.
    (* ST_CaseCons *)
    + inversion HR1; subst.
      exists (subst' y t'0 (subst' x h' tcons')).
      repeat apply subst_R_subst'; assumption.
Qed.

Lemma step_preservation: forall conf t1 t1',
  R conf t1 t1' ->
  forall t2, step t1 t2 ->
    exists t2', step' t1' t2' /\ R conf t2 t2'.
Proof.
  intros conf t1 t1' HR.
  induction HR; intros t20 Hstep;
    try solve_by_inverts 1.
  (* app *)
  - inversion Hstep; subst.
    (* ST_App *)
    + apply IHHR1 in H2 as [t' [Hstep' HR']].
      exists (app' t' t2'). split;
      constructor; assumption.
    (* ST_AppAbs *)
    + inversion HR1; subst.
      exists (subst' x t2' t'). split.
      constructor.
      apply subst_R_subst'; assumption.
  (* fixp *)
  - inversion Hstep; subst.
    (* ST_FixpAbs *)
    + inversion HR; subst.
      eexists; repeat econstructor; eassumption.
    (* ST_Fixp *)
    + apply IHHR in H0 as [t2' [Hstep' HR']].
      exists (fixp' t2').
      repeat constructor; assumption.
  (* succ *)
  - inversion Hstep; subst.
    (* ST_Succ *)
    + apply IHHR in H0 as [t2' [Hstep' HR']].
      exists (succ' t2').
      repeat constructor; assumption.
    (* ST_SuccConst *)
    + inversion HR; subst.
      apply derive_to_primitive in H0.
      apply mapping_not_change_deriving with (f:=S) in H0.
      eexists. split. 
      * apply ST_SuccConst'. 
      * econstructor.
        simpl. erewrite H0.
        reflexivity.
  (* add *)
  - inversion Hstep; subst.
    (* ST_Add1 *)
    + rename t1'0 into t0.
      apply IHHR1 in H2 as [t0' [Hstep' HR']].
      exists (add' t0' t2'). split;
      repeat constructor; assumption.
    (* ST_Add2 *)
    + rename t2'0 into t3.
      apply IHHR2 in H3 as [t3' [Hstep' HR']].
      exists (add' t1' t3'). split.
      * apply (value_R_value' _ _ _ HR1) in H1.
        apply (ST_Add2' _ _ _ H1). assumption.
      * repeat constructor; assumption.
    (* ST_AddConst *)
    + clear IHHR1 IHHR2.
      inversion HR1;
      inversion HR2; subst.
      exists (const' (app_binop Nat.add n' n'0)). split.
      constructor.
      apply derive_to_primitive in H0, H3.
      pose proof (binop_not_change_deriving _ _ _ _ _ Nat.add H0 H3).
      constructor. simpl.
      rewrite H. reflexivity.
  (* cons *)
  - inversion Hstep; subst.
    (* ST_Cons1 *)
    + apply IHHR1 in H2 as [t2' [Hstep' HR']].
      exists (cons' t2' t'). split;
      constructor; assumption.
    (* ST_Cons2 *)
    + apply (value_R_value' _ _ _ HR1) in H1.
      apply IHHR2 in H3 as [t3' [Hstep' HR']].
      exists (cons' h' t3'). split;
      constructor; assumption.
  (* case *)
  - inversion Hstep; subst.
    (* ST_Case1 *)
    + apply IHHR1 in H5 as [t2' [Hstep' HR']].
    exists (case' t2' tnil' x y tcons'). split;
    constructor; assumption.
    (* ST_CaseNil *)
    + inversion HR1.
      exists tnil'. split.
      apply ST_CaseNil'.
      assumption.
    (* ST_CaseCons *)
    + inversion HR1; subst.
      exists (subst' y t'0 (subst' x h' tcons')).
      split.
      * apply (value_R_value' _ _ _ H1) in H5.
        apply (value_R_value' _ _ _ H3) in H6.
        apply ST_CaseCons'; assumption.
      * repeat apply subst_R_subst'; assumption.
Qed.

(* A variational value (either a list or a number) is always
   related to its derivation *)
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

(* If a related term has a normal form then its counterpart also
   has a normal form and both normal forms are related with each other *)
Lemma R_mstep: forall conf t v,
  step_normal_form_of t v ->
  forall t', R conf t t' ->
  exists v', step'_normal_form_of t' v' /\
  R conf v v'.
Proof.
  intros conf t v [Hms Hnf].
  induction Hms; intros t' HR.
  - eexists t'. split; [split|].
    + apply multi_refl.
    + intros Hstep.
      apply Hnf; clear Hnf.
      apply R_redux_iff in HR as [_ HR].
      apply HR, Hstep.
    + assumption.
  - rename t' into x'.
    pose proof (step_R_step' _ _ _ HR _ H).
    pose proof (R_step _ _ _ HR _ H).
    (* fails because nothing guarantees that H0 and H1
       refer to the same term *)
Abort.

Lemma R_mstep: forall conf t v,
  step_normal_form_of t v ->
  forall t', R conf t t' ->
  exists v', step'_normal_form_of t' v' /\
  R conf v v'.
Proof.
  intros conf t v [Hms Hnf].
  induction Hms; intros t' HR.
  - eexists t'. split; [split|].
    + apply multi_refl.
    + intros Hstep.
      apply Hnf; clear Hnf.
      apply R_redux_iff in HR as [_ HR].
      apply HR, Hstep.
    + assumption.
  - rename t' into x'.
    pose proof (step_preservation _ _ _ HR _ H)
     as [y' [H' HR']].
    apply (IHHms Hnf) in HR' as [v' [[Hms' Hnf'] HR']].
    exists v'. split; [split|]; try assumption.
    eapply (multi_step _ _ _ _ H') in Hms'.
    assumption.
Qed.

(* The main commutativity theorem. 
   If the traditional analysis path yields an
   analysis result then the lifted path yields a
   variational result that can be derived into the
   same analysis result *)
Theorem commutativity: forall conf analysis spl p r,
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
  pose proof (R_mstep _ _ _ Hms _ H1) as [r' [H2 H3]].
  clear - H2 H3 Hr.
  pose proof (analysis_result_derives conf r r' Hr H3).
  exists r'; split;
  assumption.
Qed.

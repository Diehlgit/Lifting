Require Import List Maps Presence_Conditions.
Require Import STLC_SuccNat.
Require Import Lifted_STLC_SuccNat.
Import ListNotations.
Require Import Norm Lifted_Norm.

Fixpoint LR (cfg:feat_config) (T:ty) (t:tm) (t':tm') : Prop :=
  has_type empty t T /\ has_type' empty t' (lift_ty T) /\
  match T with
  | Nat => exists r r',
	          step_normal_form_of t (const r) /\
	          step'_normal_form_of t' (const' r') /\
	          derive r' cfg = Some r
  | (Arrow T1 T2) => forall arg arg',
            LR cfg T1 arg arg' ->
            LR cfg T2 (app t arg) (app' t' arg')
  end.

Lemma LR_typable_empty : forall {cfg} {T} {t} {t'},
  LR cfg T t t' ->
  has_type empty t T /\ has_type' empty t' (lift_ty T).
Proof.
  intros.
  destruct T; unfold LR in H; split;
    try (destruct H as [H _]; assumption);
    destruct H as [_ [H _] ]; assumption.
Qed.

(* This proof depends on normalization *)
Lemma LR_halts: forall {cfg} {T} {t} {t'},
  LR cfg T t t' -> halts t /\ halts' t'.
Proof.
  intros. split; [eapply normalization| eapply normalization'];
  eapply LR_typable_empty; eassumption.
Qed.

Lemma step_preserves_LR : forall T cfg t1 t2 t', (step t1 t2) -> LR cfg T t1 t' -> LR cfg T t2 t'.
Proof.
 induction T;  intros cfg t1 t2 t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H] ].
  (* Arrow *)
  - split; [|split].
    eapply preservation; eauto.
    assumption.
    clear Hty Hty'.
    intros.
    eapply IHT2.
    apply ST_App1. apply E.
    apply H. assumption.
  (* Nat *)
  - split; [|split]; auto.
    eapply preservation; eauto.
    destruct H as [r [r' [Hsnf [Hsnf' Hd] ] ] ].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms _].
    split; [|intros [x contra]; inversion contra].
    inversion Hms; subst;
      try solve_by_inverts 1.
    apply (determinism _ _ _ H) in E.
    rewrite E in *.
    assumption.
Qed.

Lemma step'_preserves_LR : forall T cfg t t1' t2', (step' t1' t2') -> LR cfg T t t1' -> LR cfg T t t2'.
Proof.
 induction T;  intros cfg t t1' t2' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H] ].
  (* Arrow *)
  - split; [|split].
    assumption.
    eapply preservation'; eauto.
    clear Hty Hty'.
    intros.
    eapply IHT2.
    apply ST_App1'. apply E.
    apply H. assumption.
  (* Nat *)
  - split; [|split]; auto.
    eapply preservation'; eauto.
    destruct H as [r [r' [Hsnf [Hsnf' Hd] ] ] ].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' _].
    split; [|intros [x contra]; inversion contra].
    inversion Hms'; subst;
      try solve_by_inverts 1.
    apply (determinism' _ _ _ H) in E.
    rewrite E in *.
    assumption.
Qed.

Lemma step_preserves_LR' : forall T cfg t1 t2 t',
  has_type empty t1 T -> 
  (step t1 t2) ->
  LR cfg T t2 t' -> LR cfg T t1 t'.
Proof.
 induction T;  intros cfg t1 t2 t' HT E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H] ].
  (* Arrow *)
  - split; [|split].
    auto.
    assumption.
    clear Hty'.
    intros.
    eapply IHT2.
    eapply T_App. eauto.
    eapply LR_typable_empty; eauto.
    apply ST_App1. apply E.
    apply H. assumption.
  (* Nat *)
  - split; [|split]; auto.
    destruct H as [r [r' [Hsnf [Hsnf' Hd] ] ] ].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms _].
    split; [|intros [x contra]; inversion contra].
    inversion Hms; subst; eauto.
Qed.

Lemma step'_preserves_LR' : forall T cfg t t1' t2',
  has_type' empty t1' (lift_ty T) -> 
  (step' t1' t2') ->
  LR cfg T t t2' -> LR cfg T t t1'.
Proof.
 induction T;  intros cfg t t1' t2' HT E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H] ].
  (* Arrow *)
  - split; [|split].
    auto.
    assumption.
    clear Hty'.
    intros.
    eapply IHT2.
    eapply T_App'. eauto.
    eapply LR_typable_empty; eauto.
    apply ST_App1'. apply E.
    apply H. assumption.
  (* Nat *)
  - split; [|split]; auto.
    destruct H as [r [r' [Hsnf [Hsnf' Hd] ] ] ].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' _].
    split; [|intros [x contra]; inversion contra].
    inversion Hms'; subst; eauto.
Qed.

Lemma mstep_preserves_LR': forall T cfg t1 t2 t',
  has_type empty t1 T ->
  multi step t1 t2 ->
  LR cfg T t2 t' -> LR cfg T t1 t'.
Proof.
  intros. induction H0.
  - assumption.
  - apply (preservation _ _ _ H) in H0 as H3.
    apply (IHmulti H3) in H1.
    eapply step_preserves_LR'; eauto.
Qed.

Lemma mstep_preserves_LR: forall T cfg t1 t2 t',
  multi step t1 t2 ->
  LR cfg T t1 t' -> LR cfg T t2 t'.
Proof.
  intros. induction H.
  - assumption.
  - apply IHmulti.
    eapply step_preserves_LR; eauto.
Qed.

Lemma mstep'_preserves_LR': forall T cfg t t1' t2',
  has_type' empty t1' (lift_ty T) ->
  multi step' t1' t2' ->
  LR cfg T t t2' -> LR cfg T t t1'.
Proof.
  intros. induction H0.
  - assumption.
  - apply (preservation' _ _ _ H) in H0 as H3.
    apply (IHmulti H3) in H1.
    eapply step'_preserves_LR'; eauto.
Qed.

Lemma mstep'_preserves_LR: forall T cfg t t1' t2',
  multi step' t1' t2' ->
  LR cfg T t t1' -> LR cfg T t t2'.
Proof.
  intros. induction H.
  - assumption.
  - apply IHmulti.
    eapply step'_preserves_LR; eauto.
Qed.

Lemma mstep_mstep'__preserves_LR: forall T cfg t1 t2 t1' t2',
  multi step t1 t2 ->
  multi step' t1' t2' ->
  LR cfg T t1 t1' -> LR cfg T t2 t2'.
Proof.
  intros.
  apply (mstep'_preserves_LR _ _ _ _ t2') in H1; auto.
  apply (mstep_preserves_LR _ _ _ t2) in H1; auto.
Qed.

Lemma soundness: forall cfg analysis,
  LR cfg (Arrow Nat Nat) analysis (lift analysis) ->
  (forall spl p r' r,
    derive spl cfg = Some p ->
    step_normal_form_of (app analysis (const p)) (const r) ->
    step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
    derive r' cfg = Some r
  ).
Proof.
  intros cfg analysis HLR spl p r' r Hd Hsnf Hsnf'.
  unfold LR in HLR. destruct HLR as [HT [HT' HLR] ].
  specialize HLR with (arg:=(const p)) (arg':=(const' spl)).
  destruct HLR.
  { split; [|split]; auto.
    exists p, spl; split; [|split];
      try (split;[apply multi_refl| intros [x contra]; inversion contra]);
      assumption. }
  destruct H0 as [_ [r0 [r0' [Hsnf0 [Hsnf0' Hd0'] ] ] ] ].

  apply (normal_forms_unique _ _ _ Hsnf0) in Hsnf.
  injection Hsnf as Hsnf; subst.

  apply (normal_forms'_unique _ _ _ Hsnf0') in Hsnf'.
  injection Hsnf' as Hsnf'; subst.

  assumption.
Qed.

Require Import Enviroments.

Inductive instantiation : feat_config -> tass -> env -> env' -> Prop :=
  | V_nil : forall cfg, instantiation cfg nil nil nil
  | V_cons : forall cfg x T v v' c e e',
    instantiation cfg c e e'->
    value v -> value' v' ->
    LR cfg T v v' ->
    instantiation cfg ((x,T)::c) ((x,v)::e) ((x,v')::e').

Lemma instantiation_domains_match: forall {cfg} {c} {e} {e'},
  instantiation cfg c e e'->
  forall {x} {T},
    lookup x c = Some T -> 
      exists t, lookup x e = Some t /\ 
      exists t', lookup x e' = Some t'.
Proof.
  intros cfg x e e' V. induction V; intros x0 T0 C.
    solve_by_inverts 1.
    simpl in *.
    destruct (eqb x x0); eauto.
Qed.

Lemma instantiation_LR : forall cfg c e e',
  instantiation cfg c e e' ->
  forall x t t' T,
    lookup x c = Some T ->
    lookup x e = Some t ->
    lookup x e' = Some t' ->
    LR cfg T t t'.
Proof.
  intros cfg c e e' V.
  induction V; intros x0 t t' T0 Hc He He'.
  - solve_by_inverts 1.
  - simpl in Hc, He, He'.
    destruct (eqb x x0).
    + injection Hc as HT.
      injection He as Hv.
      injection He' as Hv'.
      subst. assumption.
    + eauto.
Qed.

Lemma instantiation_env_closed: forall cfg c e e',
  instantiation cfg c e e' -> closed_env e /\ closed'_env' e'.
Proof.
  intros cfg c e e' Hinst.
  induction Hinst.
  - split; constructor.
  - destruct IHHinst as [He He'].
    split.
    + unfold closed_env; fold closed_env.
      split; [|assumption].
      eapply typable_empty__closed.
      eapply LR_typable_empty.
      eassumption.
    + unfold closed'_env'; fold closed'_env'.
      split; [|assumption].
      eapply typable_empty__closed'.
      eapply LR_typable_empty.
      eassumption.
Qed.

Lemma msubst_preserves_typing : forall cfg c e e',
  instantiation cfg c e e' ->
  forall Gamma t S, has_type (mupdate Gamma c) t S ->
  has_type Gamma (msubst e t) S.
Proof.
    intros cfg c e e' H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H3.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (LR_typable_empty H2).
Qed.

Fixpoint lift_tass (c:tass) : tass' :=
  match c with
  | [] => []
  | (x,T)::ts => (x,(lift_ty T)) :: (lift_tass ts)
  end.

Lemma lift_tass_drop: forall x c, lift_tass (drop x c) = drop x (lift_tass c).
Proof.
  intros. induction c; auto.
  simpl. destruct a. simpl.
  destruct (eqb_spec s x).
  assumption.
  simpl. f_equal. assumption.
Qed.

Lemma msubst'_preserves_typing : forall cfg c e e',
  instantiation cfg c e e' ->
  forall Gamma' t' S', has_type' (mupdate' Gamma' (lift_tass c)) t' S' ->
  has_type' Gamma' (msubst' e' t') S'.
Proof.
    intros cfg c e e' H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2. simpl.
    apply IHinstantiation.
    simpl in H3.
    eapply substitution_preserves_typing'; eauto.
    apply (LR_typable_empty H2).
Qed.

Lemma instantiation_drop : forall cfg c env env',
    instantiation cfg c env env' ->
    forall x, instantiation cfg (drop x c) (drop x env) (drop x env').
Proof.
  intros cfg c e e' V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop.
    destruct (String.eqb x x0); auto. constructor; eauto.
Qed.

Lemma completeness: forall c env env' t T cfg,
  has_type (mupdate empty c)  t T ->
  instantiation cfg c env env' ->
  LR cfg T (msubst env t) (msubst' env' (lift t)).
Proof.
  intros c env0 env0' t T cfg HT V.
  generalize dependent env0'.
  generalize dependent env0.
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. reflexivity.
  clear HeqGamma.
  generalize dependent c.
  induction HT; simpl; intros.
  - (* T_Var *)
    rewrite H0 in H.
    destruct (instantiation_domains_match V H) as [t [P [t' P'] ] ].
    eapply instantiation_LR; eauto.
    * rewrite msubst_var.
      rewrite P; reflexivity.
      eapply instantiation_env_closed; eauto.
    * rewrite msubst'_var'.
      rewrite P'; reflexivity.
      eapply instantiation_env_closed; eauto.
  - (* T_Abs *)
    rewrite msubst_abs, msubst'_abs'.
    assert (Hty: has_type empty (abs x T2 (msubst (drop x env0) t)) (Arrow T2 T1)).
    { apply T_Abs. eapply msubst_preserves_typing.
      apply instantiation_drop; eauto.
      eapply context_invariance. apply HT.
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a.  unfold update, t_update.
        destruct (String.eqb s x0); auto. }
     assert (Hty': has_type' empty (abs' x (lift_ty T2) (msubst' (drop x env0') (lift t)))
              (Arrow' (lift_ty T2) (lift_ty T1))).
     { apply T_Abs'. eapply msubst'_preserves_typing.
      apply instantiation_drop; eauto.
      eapply context'_invariance.
      apply lifting_types in HT. apply HT.
      intros.
      unfold lift_context.
      unfold update, t_update.
      rewrite lift_tass_drop, mupdate'_drop.
      destruct (eqb_spec x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a. simpl.
        unfold update, t_update.
        destruct (String.eqb s x0); auto. }
      split; [|split]; auto.
      intros.
      destruct (LR_halts H0) as [ [v [P Q] ] [v' [P' Q'] ] ].
      pose proof (mstep_mstep'__preserves_LR _ _ _ _ _ _ P P' H0).
      apply mstep_preserves_LR' with (msubst ((x,v)::env0) t).
      { eapply T_App; eauto.
        eapply LR_typable_empty; eauto. }
      { eapply multi_step_trans. eapply multistep_App2; eauto.
            eapply multi_step with (y:= (msubst ((x, v) :: env0) t)); [|apply multi_refl].
            simpl.  rewrite subst_msubst.
            eapply ST_AppAbs; eauto.
            eapply typable_empty__closed.
            apply (LR_typable_empty H1).
            eapply instantiation_env_closed; eauto. }
      apply mstep'_preserves_LR' with (msubst' ((x,v')::env0') (lift t)).
      { eapply T_App'; eauto.
        eapply LR_typable_empty; eauto. }
      { eapply multi_step'_trans. eapply multistep'_App2'; eauto.
            eapply multi_step with (y:= (msubst' ((x, v') :: env0') (lift t))); [|apply multi_refl].
            simpl.  rewrite subst'_msubst'.
            eapply ST_AppAbs'; eauto.
            eapply typable_empty__closed'.
            apply (LR_typable_empty H1).
            eapply instantiation_env_closed; eauto.  }
      eapply (IHHT ((x,T2)::c)).
        intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
      constructor; auto.
  - (* T_App *)
    rewrite msubst_app, msubst'_app'.
    pose proof (IHHT1 c H env0 env0' V).
    unfold LR in H0; fold LR in H0.
    destruct H0 as [HT [HT' HLR] ].
    pose proof (IHHT2 c H env0 env0' V).
    auto.
  - (* T_Const *)
    split; [|split].
    rewrite msubst_const. auto.
    rewrite msubst'_const'. auto.
    exists n, [(n,pc_True)].
    split; [|split].
    + rewrite msubst_const. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + rewrite msubst'_const'. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + reflexivity.
  - (* T_Succ *)
    destruct (IHHT c H env0 env0' V) as [HT0 [HT' [r [r' [ [Hms _] [ [Hms' _] Hd] ] ] ] ] ].
    split; [|split].
    rewrite msubst_succ. auto.
    rewrite msubst'_succ'. auto.
    eexists; eexists.
    split; [|split].
    + rewrite msubst_succ. split;
        [|intros [x contra]; inversion contra].
        eapply multi_step_trans.
        apply multistep_succ; eassumption.
        eauto.
    + rewrite msubst'_succ'. split;
        [|intros [x contra]; inversion contra].
        eapply multi_step'_trans.
        apply multistep'_succ'; eassumption.
        eauto.
    + apply mapping_not_change_deriving. assumption.
Qed.

Theorem commutation: forall cfg analysis spl p r r',
  has_type empty analysis (Arrow Nat Nat) ->
  derive spl cfg = Some p ->
  step_normal_form_of (app analysis (const p)) (const r) ->
  step'_normal_form_of (app' (lift analysis) (const' spl)) (const' r') ->
  derive r' cfg = Some r.
Proof.
  intros cfg analysis spl p r r' HLR.
  apply soundness.
  replace (lift analysis) with (msubst' nil (lift analysis)) by reflexivity.
  replace analysis with (msubst nil analysis) by reflexivity.
  apply (completeness nil); auto.
  apply V_nil.
Qed.
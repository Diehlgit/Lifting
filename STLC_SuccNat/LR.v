Require Import List Maps Presence_Conditions.
Require Import STLC_SuccNat.
Require Import Lifted_STLC_SuccNat.
Import ListNotations.
Require Import Norm Lifted_Norm Derivation.

Fixpoint LR `{NatOp} (cfg:feat_config) (T:ty) (t:tm) (t':tm') : Prop :=
  has_type empty t T /\ has_type' empty t' (lift_ty T) /\
  match T with
  | Nat => exists r r',
	          step_normal_form_of t r /\
	          step'_normal_form_of t' r' /\
	          derive' cfg r' = Some r
  | (Arrow T1 T2) => forall arg arg',
            LR cfg T1 arg arg' ->
            LR cfg T2 (app t arg) (app' t' arg')
  | NatList => exists r r',
	          step_normal_form_of t r /\
	          step'_normal_form_of t' r' /\
	          derive' cfg r' = Some r
  end.

Lemma LR_typable_empty `{NatOp}: forall {cfg} {T} {t} {t'},
  LR cfg T t t' ->
  has_type empty t T /\ has_type' empty t' (lift_ty T).
Proof.
  intros.
  destruct T; unfold LR in H0; split;
    try (destruct H0 as [H0 _]; assumption);
    destruct H0 as [_ [H0 _] ]; assumption.
Qed.

(* This proof depends on normalization
   Reasoning: Suppose we could prove LR_halts without
   using normalization theorem.
   Then we could alse prove completeness theorem without using
   the normalization theorem.
   But now we proved that every well typed term is in the relation
   (completeness)
   and we also proved that every term in the relation halts
   (LR_halts)
   This implies that ever well typed term halts
   (normalization)
*)
Lemma LR_halts `{NatOp}: forall {cfg} {T} {t} {t'},
  LR cfg T t t' -> halts t /\ halts' t'.
Proof.
  intros. split; [eapply normalization| eapply normalization'];
  eapply LR_typable_empty; eassumption.
Qed.

Lemma step_preserves_LR `{NatOp}: forall T cfg t1 t2 t',
  (step t1 t2) -> LR cfg T t1 t' -> LR cfg T t2 t'.
Proof.
 induction T;  intros cfg t1 t2 t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H0]].
  (* Arrow *)
  - split; [|split].
    eapply preservation; eauto.
    assumption.
    clear Hty Hty'.
    intros.
    eapply IHT2.
    apply ST_App1. apply E.
    apply H0. assumption.
  (* Nat *)
  - split; [|split]; auto.
    eapply preservation; eauto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd] ] ] ].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms Hv].
    split; auto.
    inversion Hms; subst.
    exfalso; apply Hv; eauto.
    apply (determinism _ _ _ H0) in E.
    rewrite E in *.
    assumption.
  (* NatList *)
  - split; [|split]; auto.
    eapply preservation; eauto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms Hv].
    split; auto.
    inversion Hms; subst.
    exfalso; apply Hv; eauto.
    apply (determinism _ _ _ H0) in E.
    rewrite E in *.
    assumption.
Qed.

Lemma step'_preserves_LR `{NatOp}: forall T cfg t t1' t2',
  (step' t1' t2') -> LR cfg T t t1' -> LR cfg T t t2'.
Proof.
 induction T;  intros cfg t t1' t2' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H0]].
  (* Arrow *)
  - split; [|split].
    assumption.
    eapply preservation'; eauto.
    clear Hty Hty'.
    intros.
    eapply IHT2.
    apply ST_App1'. apply E.
    apply H0. assumption.
  (* Nat *)
  - split; [|split]; auto.
    eapply preservation'; eauto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' Hv'].
    split; auto.
    inversion Hms'; subst.
    exfalso; apply Hv'; eauto.
    apply (determinism' _ _ _ H0) in E.
    rewrite E in *.
    assumption.
  (* NatList *)
  - split; [|split]; auto.
    eapply preservation'; eauto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' Hv'].
    split; auto.
    inversion Hms'; subst.
    exfalso; apply Hv'; eauto.
    apply (determinism' _ _ _ H0) in E.
    rewrite E in *.
    assumption.
Qed.

Lemma step_preserves_LR' `{NatOp}: forall T cfg t1 t2 t',
  has_type empty t1 T -> 
  (step t1 t2) ->
  LR cfg T t2 t' -> LR cfg T t1 t'.
Proof.
 induction T;  intros cfg t1 t2 t' HT E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H0]].
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
    apply H0. assumption.
  (* Nat *)
  - split; [|split]; auto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms Hv].
    split; auto.
    inversion Hms; subst; eauto.
  (* NatList *)
  - split; [|split]; auto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf' Hd Hty Hty'.
    destruct Hsnf as [Hms Hv].
    split; auto.
    inversion Hms; subst; eauto.
Qed.

Lemma step'_preserves_LR' `{NatOp}: forall T cfg t t1' t2',
  has_type' empty t1' (lift_ty T) -> 
  (step' t1' t2') ->
  LR cfg T t t2' -> LR cfg T t t1'.
Proof.
 induction T;  intros cfg t t1' t2' HT E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [Hty [Hty' H0]].
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
    apply H0. assumption.
  (* Nat *)
  - split; [|split]; auto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' Hv'].
    split; auto.
    inversion Hms'; subst; eauto.
  (* NatList *)
  - split; [|split]; auto.
    destruct H0 as [r [r' [Hsnf [Hsnf' Hd]]]].
    exists r, r'. split; [|split]; auto.
    clear Hsnf Hd Hty Hty'.
    destruct Hsnf' as [Hms' Hv'].
    split; auto.
    inversion Hms'; subst; eauto.
Qed.

Lemma mstep_preserves_LR' `{NatOp}: forall T cfg t1 t2 t',
  has_type empty t1 T ->
  multi step t1 t2 ->
  LR cfg T t2 t' -> LR cfg T t1 t'.
Proof.
  intros. induction H1.
  - assumption.
  - apply (preservation _ _ _ H0) in H1 as H4.
    apply (IHmulti H4) in H2.
    eapply step_preserves_LR'; eauto.
Qed.

Lemma mstep_preserves_LR `{NatOp}: forall T cfg t1 t2 t',
  multi step t1 t2 ->
  LR cfg T t1 t' -> LR cfg T t2 t'.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti.
    eapply step_preserves_LR; eauto.
Qed.

Lemma mstep'_preserves_LR' `{NatOp}: forall T cfg t t1' t2',
  has_type' empty t1' (lift_ty T) ->
  multi step' t1' t2' ->
  LR cfg T t t2' -> LR cfg T t t1'.
Proof.
  intros. induction H1.
  - assumption.
  - apply (preservation' _ _ _ H0) in H1 as H4.
    apply (IHmulti H4) in H2.
    eapply step'_preserves_LR'; eauto.
Qed.

Lemma mstep'_preserves_LR `{NatOp}: forall T cfg t t1' t2',
  multi step' t1' t2' ->
  LR cfg T t t1' -> LR cfg T t t2'.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti.
    eapply step'_preserves_LR; eauto.
Qed.

Lemma mstep_mstep'__preserves_LR `{NatOp}: forall T cfg t1 t2 t1' t2',
  multi step t1 t2 ->
  multi step' t1' t2' ->
  LR cfg T t1 t1' -> LR cfg T t2 t2'.
Proof.
  intros.
  apply (mstep'_preserves_LR _ _ _ _ t2') in H2; auto.
  apply (mstep_preserves_LR _ _ _ t2) in H2; auto.
Qed.

Lemma mstep_mstep'__preserves_LR' `{NatOp}: forall T cfg t1 t2 t1' t2',
  has_type empty t1 T ->
  has_type' empty t1' (lift_ty T) ->
  multi step t1 t2 ->
  multi step' t1' t2' ->
  LR cfg T t2 t2' -> LR cfg T t1 t1'.
Proof.
  intros.
  apply (preservation'_multi _ _ _ H1) in H3 as H5.
  apply (mstep'_preserves_LR' _ _ _ t1') in H4; auto.
  apply (preservation_multi _ _ _ H0) in H2 as H6.
  apply (mstep_preserves_LR' _ _ t1) in H4; auto.
Qed.

Definition commutes `{NatOp} T cfg analysis := forall spl p r r',
  has_type' empty spl (lift_ty T) ->
  derive' cfg spl = Some p ->
  step_normal_form_of (app analysis p) r ->
  step'_normal_form_of (app' (lift analysis) spl) r' ->
  derive' cfg r' = Some r.

Definition base_ty T := T = Nat \/ T = NatList.
(*TODO: A Software analysis function should be of type NatList -> T.
    This makes definitions easier to deal with without loosing
    expressiviness of the Lifted Language. A Variational Natural
    is represented by a List with only one value. *)

Lemma soundness `{NatOp}: forall T cfg analysis,
  LR cfg (Arrow NatList T) analysis (lift analysis) ->
    commutes NatList cfg analysis.
Proof.
  intros T conf analysis HLR spl p r r' Hty Hd Hsnf Hsnf'.
  unfold LR in HLR. fold LR in HLR.
  destruct HLR as [_ [_ HLR]].
  specialize HLR with (arg:=p) (arg':=spl).
  assert (LR conf T (app analysis p) (app' (lift analysis) spl)).
  { apply HLR. clear HLR.
    split; [|split].
    replace NatList with (type_derivation NatList') by reflexivity.
    eapply deriving'_types; eauto.
    eassumption.
    exists p, spl; split; [|split];
    pose proof (derive'_value _ _ _ Hd) as [Hv Hv'];
    apply value_is_nf in Hv; auto;
    apply value'_is_nf in Hv'; auto. }
  clear HLR. assert (LR conf NatList p spl).
  { split; [|split].
    replace NatList with (type_derivation NatList') by reflexivity.
    eapply deriving'_types; eassumption.
    assumption. exists p, spl.
    split;[|split].
    apply derive'_value in Hd as [].
    apply value_is_nf; assumption.
    apply derive'_value in Hd as [].
    apply value'_is_nf; assumption.
    assumption. }
Abort.


Lemma soundness `{NatOp}: forall T cfg analysis,
  base_ty T ->
  LR cfg (Arrow T T) analysis (lift analysis) ->
    commutes T cfg analysis.
Proof.
  intros T cfg analysis Hbt HLR spl p r r' Hty Hd Hsnf Hsnf'.
  unfold LR in HLR. destruct HLR as [_ [_ HLR]].
  specialize HLR with (arg:=p) (arg':=spl).
  destruct Hbt; subst; destruct HLR;
    try (destruct H1 as [_ [r0 [r0' [Hsnf0 [Hsnf0' Hd0']]]]];
         apply (normal_forms_unique _ _ _ Hsnf0) in Hsnf;
         apply (normal_forms'_unique _ _ _ Hsnf0') in Hsnf';
         subst; assumption).
  (* Nat *)
  { split; [|split].
    replace Nat with (type_derivation Nat') by reflexivity.
    eapply deriving'_types; eauto.
    assumption.
    exists p, spl; split; [|split];
    pose proof (derive'_value _ _ _ Hd) as [Hv Hv'];
    apply value_is_nf in Hv; auto;
    apply value'_is_nf in Hv'; auto. }

  (* NatList *)
  { split; [|split].
    replace NatList with (type_derivation NatList') by reflexivity.
    eapply deriving'_types; eauto.
    assumption.
    exists p, spl; split; [|split];
    pose proof (derive'_value _ _ _ Hd) as [Hv Hv'];
    apply value_is_nf in Hv; auto;
    apply value'_is_nf in Hv'; auto. }
Qed.
(*TODO: maybe prove:
         has_type' empty spl (lift_ty Nat) ->
         derive' conf spl = Some p ->o
         has_type empty p Nat.
        to automate Nat and NatList cases.*)

Require Import Environments.

Inductive instantiation `{NatOp}: feat_config -> tass -> env -> env' -> Prop :=
  | V_nil : forall cfg, instantiation cfg [] [] []
  | V_cons : forall cfg x T v v' c e e',
    instantiation cfg c e e'->
    value v -> value' v' ->
    LR cfg T v v' ->
    instantiation cfg ((x,T)::c) ((x,v)::e) ((x,v')::e').

Lemma instantiation_domains_match `{NatOp}: forall {cfg} {c} {e} {e'},
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

Lemma instantiation_LR `{NatOp}: forall cfg c e e',
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

Lemma instantiation_env_closed `{NatOp}: forall cfg c e e',
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

Lemma msubst_preserves_typing `{NatOp}: forall cfg c e e',
  instantiation cfg c e e' ->
  forall Gamma t S, has_type (mupdate Gamma c) t S ->
  has_type Gamma (msubst e t) S.
Proof.
    intros cfg c e e' H0. induction H0; intros.
    simpl in H0. simpl. auto.
    simpl in H4.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (LR_typable_empty H3).
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

Lemma msubst'_preserves_typing `{NatOp}: forall cfg c e e',
  instantiation cfg c e e' ->
  forall Gamma' t' S', has_type' (mupdate' Gamma' (lift_tass c)) t' S' ->
  has_type' Gamma' (msubst' e' t') S'.
Proof.
    intros cfg c e e' H0. induction H0; intros.
    simpl in H0. simpl. auto.
    simpl in H3. simpl.
    apply IHinstantiation.
    simpl in H4.
    eapply substitution_preserves_typing'; eauto.
    apply (LR_typable_empty H3).
Qed.

Lemma instantiation_drop `{NatOp}: forall cfg c env env',
    instantiation cfg c env env' ->
    forall x, instantiation cfg (drop x c) (drop x env) (drop x env').
Proof.
  intros cfg c e e' V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop.
    destruct (String.eqb x x0); auto. constructor; eauto.
Qed.

Lemma related_canonical_forms_list: forall v v',
  has_type empty v NatList ->
  has_type' empty v' NatList' ->
  value v -> value' v' ->
  (exists cfg, derive' cfg v' = Some v) ->
    (v = nil /\ v' = nil') \/
    (exists v1 v2 v1' v2',
      value' v1' /\ value' v2' /\
      value v1 /\ value v2 /\
      v' = cons' v1' v2' /\ v = cons v1 v2).
Proof.
  intros v v' Hty Hty' Hv Hv' [cfg Hd].
  apply (canonical_forms_list v Hty) in Hv.
  apply (canonical_forms_list' v' Hty') in Hv'.
  destruct Hv; destruct Hv'.
  - left. split; auto.
  - destruct H0 as [v1' [v2' [Hv1' [Hv2' Heq]]]].
    subst. simpl in Hd.
    destruct (derive' cfg v1');
    destruct (derive' cfg v2');
      try solve_by_inverts 1.
  - destruct H as [v1 [v2 [Hv1 [Hv2 Heq]]]].
    subst. simpl in Hd.
    inversion Hd.
  - destruct H0 as [v1' [v2' [Hv1' [Hv2' Heq]]]].
    subst.
    destruct H as [v1 [v2 [Hv1 [Hv2 Heq]]]].
    subst. right.
    exists v1, v2, v1', v2'.
    repeat split; auto.
Qed.

(* Pattern matching acts like lambda abstraction because
   evaluating it envolves beta reduction. *)
Lemma completeness `{NatOp}: forall c env env' t T cfg,
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
    rewrite H1 in H0.
    destruct (instantiation_domains_match V H0) as [t [P [t' P'] ] ].
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
      + rewrite H0.
        clear - c n. induction c.
        simpl. apply eqb_neq in n; rewrite n; auto.
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
      + rewrite H0.
        clear - c n. induction c.
        simpl. apply eqb_neq in n; rewrite n; auto.
        simpl. destruct a. simpl.
        unfold update, t_update.
        destruct (String.eqb s x0); auto. }
      split; [|split]; auto.
      intros.
      destruct (LR_halts H1) as [ [v [P Q] ] [v' [P' Q'] ] ].
      pose proof (mstep_mstep'__preserves_LR _ _ _ _ _ _ P P' H1).
      apply mstep_mstep'__preserves_LR' with (msubst ((x,v)::env0) t) (msubst' ((x,v')::env0') (lift t)).
      { eapply T_App; eauto.
        eapply LR_typable_empty; eauto. }
      { eapply T_App'; eauto.
        eapply LR_typable_empty; eauto. }
      { eapply multi_step_trans. eapply multistep_app2; eauto.
            eapply multi_step with (y:= (msubst ((x, v) :: env0) t));
              [|apply multi_refl].
            simpl.  rewrite subst_msubst.
            eapply ST_AppAbs; eauto.
            eapply typable_empty__closed.
            apply (LR_typable_empty H2).
            eapply instantiation_env_closed; eauto. }
      { eapply multi_step'_trans. eapply multistep'_app2'; eauto.
            eapply multi_step with (y:= (msubst' ((x, v') :: env0') (lift t)));
              [|apply multi_refl].
            simpl.  rewrite subst'_msubst'.
            eapply ST_AppAbs'; eauto.
            eapply typable_empty__closed'.
            apply (LR_typable_empty H2).
            eapply instantiation_env_closed; eauto.  }
      eapply (IHHT ((x,T2)::c)).
        intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
      constructor; auto.
  - (* T_App *)
    rewrite msubst_app, msubst'_app'.
    pose proof (IHHT1 c H0 env0 env0' V).
    unfold LR in H1; fold LR in H1.
    destruct H1 as [_ [_ HLR]].
    pose proof (IHHT2 c H0 env0 env0' V).
    auto.
  - (* T_Const *)
    split; [|split].
    rewrite msubst_const. auto.
    rewrite msubst'_const'. auto.
    exists (const n), (const' [(n,pc_True)]).
    split; [|split].
    + rewrite msubst_const. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + rewrite msubst'_const'. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + reflexivity.
  - (* T_Succ *)
    destruct (IHHT c H0 env0 env0' V) as [HT0 [HT' [r [r' [ [Hms Hnf] [ [Hms' _] Hd]]]]]].
    split; [|split].
    rewrite msubst_succ. auto.
    rewrite msubst'_succ'. auto.
    apply (preservation_multi _ _ _ HT0) in Hms as Hty.
    pose proof (derive'_value _ _ _ Hd) as [Hv Hv'].
    apply (preservation'_multi _ _ _ HT') in Hms' as Hty'.
    apply (canonical_forms_nat _ Hty) in Hv as [n H1].
    apply (canonical_forms_nat' _ Hty') in Hv' as [n' H2].
    subst; clear Hty Hty'.
    eexists; eexists.
    split; [|split].
    + rewrite msubst_succ. split.
        eapply multi_step_trans.
        apply multistep_succ; eassumption.
        eapply multi_step. apply ST_SuccConst.
        apply multi_refl.
        intros []; solve_by_inverts 1.
    + rewrite msubst'_succ'. split.
        eapply multi_step'_trans.
        apply multistep'_succ'; eassumption.
        eapply multi_step. apply ST_SuccConst'.
        apply multi_refl.
        intros []; solve_by_inverts 1.
    + simpl. simpl in Hd.
      erewrite mapping_not_change_deriving;
      auto. destruct (derive n' cfg) eqn:Heq;
      try solve_by_inverts 1.
      injection Hd as Hd; auto.
  - (* T_Add *)
    rewrite msubst_op, msubst'_op'.
    destruct (IHHT1 c H0 env0 env0' V) as [HT11 [HT1' [r1 [r1' [[Hms1 _] [[Hms1' _] Hd1]]]]]].
    destruct (IHHT2 c H0 env0 env0' V) as [HT22 [HT2' [r2 [r2' [[Hms2 _] [[Hms2' _] Hd2]]]]]].
    split; [|split]; auto.
    pose proof (preservation_multi _ _ _ HT11 Hms1).
    pose proof (preservation'_multi _ _ _ HT1' Hms1').
    pose proof (derive'_value _ _ _ Hd1) as [].
    apply (canonical_forms_nat _ H1) in H3 as [n1]; subst.
    apply (canonical_forms_nat' _ H2) in H4 as [n1']; subst.
    clear H1 H2.
    pose proof (preservation_multi _ _ _ HT22 Hms2).
    pose proof (derive'_value _ _ _ Hd2) as [].
    pose proof (preservation'_multi _ _ _ HT2' Hms2').
    apply (canonical_forms_nat _ H1) in H2 as [n2]; subst.
    apply (canonical_forms_nat' _ H4) in H3 as [n2']; subst.
    clear H1 H4.
    exists (const (nat_op n1 n2)), (const' (app_binop nat_op n1' n2'));
    repeat split.
    + eapply multi_step_trans.
      apply multistep_op1; eassumption.
      eapply multi_step_trans.
      apply multistep_op2; eauto.
      eapply multi_step. apply ST_OpConst.
      apply multi_refl.
    + intros [x contra]; inversion contra.
    + eapply multi_step'_trans.
      apply multistep'_op1'; eassumption.
      eapply multi_step'_trans.
      apply multistep'_op2'; eauto.
      eapply multi_step. apply ST_OpConst'.
      apply multi_refl.
    + intros [x contra]; inversion contra.
    + simpl.
      erewrite binop_not_change_deriving.
      reflexivity.
      simpl in Hd1. destruct (derive n1' cfg);
      try solve_by_inverts 1.
      injection Hd1 as []; auto.
      simpl in Hd2. destruct (derive n2' cfg);
      try solve_by_inverts 1.
      injection Hd2 as []; auto.
  - (* T_Nil *)
    split; [|split].
    rewrite msubst_nil. auto.
    rewrite msubst'_nil'. auto.
    exists nil, nil'.
    split; [|split].
    + rewrite msubst_nil. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + rewrite msubst'_nil'. split;
        [eapply multi_refl
        | intros [x contra]; inversion contra].
    + reflexivity.
  - (* T_Cons *)
    rewrite msubst_cons, msubst'_cons'.
    pose proof (IHHT1 c H0 env0 env0' V).
    unfold LR in H1; fold LR in H1.
    destruct H1 as [Hty1 [Hty1' HLR]].
    pose proof (IHHT2 c H0 env0 env0' V).
    clear IHHT1 IHHT2.
    split; [|split];
    try (constructor; auto;
    destruct (LR_typable_empty H1) as [H2 H3]; auto).
    destruct HLR as [r1 [r1' [[Hms1 Hnf1] [[Hms1' Hnf1'] Hd1]]]].
    unfold LR in H1.
    destruct H1 as [_ [_ [r2 [r2' [[Hms2 Hnf2] [[Hms2' Hnf2'] Hd2]]]]]].
    eexists; eexists.
    split; [|split].
    + split. eapply multi_step_trans.
      eapply multistep_cons1.
      eassumption.
      eapply multi_step_trans.
      eapply multistep_cons2.
      eapply derive'_value; eauto.
      eassumption.
      apply multi_refl.
      intros [x contra];
      inversion contra;
        try solve_by_inverts 1;
        subst; [apply Hnf1|apply Hnf2];
        eexists; eassumption.
    + split. eapply multi_step'_trans.
      eapply multistep'_cons1'.
      eassumption.
      eapply multi_step'_trans.
      eapply multistep'_cons2'.
      eapply derive'_value; eauto.
      eassumption.
      apply multi_refl.
      intros [x contra];
      inversion contra;
        try solve_by_inverts 1;
        subst; [apply Hnf1'|apply Hnf2'];
        eexists; eassumption.
    + clear - Hd1 Hd2. simpl.
      rewrite Hd1, Hd2.
      reflexivity.
  - (* T_Case *)
    rewrite msubst_case, msubst'_case'.
    assert (Hty: has_type empty (case (msubst env0 t1) (msubst env0 tnil) x y
     (msubst (drop y (drop x env0)) tcons)) (T)).
    { apply T_Case.
      eapply msubst_preserves_typing. eassumption.
      eapply context_invariance. apply HT1.
      intros. rewrite <- mupdate_lookup. auto.
      eapply msubst_preserves_typing. eassumption.
      eapply context_invariance. apply HT2.
      intros. rewrite <- mupdate_lookup. auto.
      eapply msubst_preserves_typing.
      repeat (apply instantiation_drop); eauto.
      eapply context_invariance. apply HT3.
      intros.
      unfold update, t_update. repeat (rewrite mupdate_drop).
      destruct (eqb_spec x x0); destruct (eqb_spec y x0);
        try auto.
        rewrite H0.
        clear - c n n0. induction c.
        simpl. apply eqb_neq in n, n0; try rewrite n, n0; auto.
        simpl. destruct a.  unfold update, t_update.
        destruct (String.eqb s x0); auto. }
     assert (Hty': has_type' empty (case' (msubst' env0' (lift t1)) (msubst' env0' (lift tnil)) x y
     (msubst' (drop y (drop x env0')) (lift tcons))) (lift_ty T)).
     { apply T_Case'.
       eapply msubst'_preserves_typing. eassumption.
       eapply context'_invariance. apply (lifting_types _ _ _ HT1).
       intros. rewrite <- mupdate'_lookup.
       unfold lift_context. unfold lift_tass.
       rewrite H0. clear - c. induction c. auto.
         destruct a. simpl.
         destruct (String.eqb s x0); auto.
       eapply msubst'_preserves_typing. eassumption.
       eapply context'_invariance. apply (lifting_types _ _ _ HT2).
       intros. rewrite <- mupdate'_lookup.
       unfold lift_context. unfold lift_tass.
       rewrite H0. clear - c. induction c. auto.
       destruct a. simpl.
       destruct (String.eqb s x0); auto.
       eapply msubst'_preserves_typing.
       repeat (apply instantiation_drop); eauto.
       eapply context'_invariance. apply (lifting_types _ _ _ HT3).
       intros.
       unfold update, t_update, lift_context.
       repeat (rewrite lift_tass_drop, mupdate'_drop).
       destruct (eqb_spec x x0); destruct (eqb_spec y x0);
        try auto.
        rewrite H0.
        clear - c n n0. induction c.
        simpl. apply eqb_neq in n, n0; try rewrite n, n0; auto.
        destruct a. simpl. unfold update, t_update.
        destruct (String.eqb s x0); auto. }

      pose proof (IHHT1 c H0 env0 env0' V).
      unfold LR in H1. destruct H1 as [_ [_ [v1 [v1' [Hsnf [Hsnf' Hdv1]]]]]].
      inversion Hty; inversion Hty'; subst.
      pose proof (wt_nf_is_value _ _ _ H8 Hsnf); clear H9 H10.
      pose proof (wt_nf_is_value' _ _ _ H18 Hsnf'); clear H19 H20.
      destruct Hsnf as [Hms _]. destruct Hsnf' as [Hms' _].
      eapply mstep_mstep'__preserves_LR'.
      exact Hty. exact Hty'.
      eapply multistep_case1; eassumption.
      eapply multistep'_case1'; eassumption.
      pose proof (preservation_multi _ _ _ H8 Hms).
      pose proof (preservation'_multi _ _ _ H18 Hms').
      clear H8 H18.

      pose proof (related_canonical_forms_list v1 v1' H3 H4 H1 H2).
      destruct H5. exists cfg; auto. clear H3 H4.
      (* Case Nil *)
      { destruct H5; subst. clear H1 H2 Hdv1 Hms Hms'.
        eapply mstep_mstep'__preserves_LR'.
        inversion Hty; subst.
        constructor; eauto.
        inversion Hty'; subst.
        constructor; eauto.
        eapply multi_step.
        apply ST_CaseNil.
        apply multi_refl.
        eapply multi_step.
        apply ST_CaseNil'.
        apply multi_refl.
        eapply IHHT2; auto. }
      (* Case Cons *)
      { destruct H5 as [v2 [v3 [v2' [v3' [Hv2' [Hv3' [Hv2 [Hv3 [Heq Heq']]]]]]]]].
        subst. eapply mstep_mstep'__preserves_LR'.
        inversion Hty; subst.
        constructor; eauto.
        inversion Hty'; subst.
        constructor; eauto.
        eapply multi_step.
        apply ST_CaseCons; auto.
        apply multi_refl.
        eapply multi_step.
        apply ST_CaseCons'; auto.
        apply multi_refl.
        rewrite drop_comm.
        repeat rewrite <- subst_msubst.
        repeat rewrite msubst_subst.
        rewrite drop_comm.
        repeat rewrite <- subst'_msubst'.
        repeat rewrite msubst'_subst'.
        apply IHHT3 with (c:= ((x,Nat) :: (y, NatList) :: c)).
        - intros s. unfold update, t_update, lookup.
          destruct (String.eqb x s); auto;
          destruct (String.eqb y s); auto.
        - repeat constructor; auto.
          inversion H3; subst; auto.
          inversion H4; subst; auto.
          apply simpl_derive'_list in Hdv1 as [Hdv2 Hdv3].
          exists v3, v3'. repeat split; auto.
          apply value_is_nf; auto.
          apply value'_is_nf; auto.
          inversion H3; subst; auto.
          inversion H4; subst; auto.
          apply simpl_derive'_list in Hdv1 as [Hdv2 Hdv3].
          exists v2, v2'. repeat split; auto.
          apply value_is_nf; auto.
          apply value'_is_nf; auto.
        - eapply typable_empty__closed'.
          inversion H4; subst; eauto.
        - eapply instantiation_env_closed. eassumption.
        - eapply typable_empty__closed'.
          inversion H4; subst; eauto.
        - eapply instantiation_env_closed.
          eapply instantiation_drop. eassumption.
        - eapply typable_empty__closed.
          inversion H3; subst; eauto.
        - eapply instantiation_env_closed. eassumption.
        - eapply typable_empty__closed.
          inversion H3; subst; eauto.
        - eapply instantiation_env_closed.
          eapply instantiation_drop. eassumption. }
Qed.

Theorem commutativity `{NatOp}: forall T cfg analysis,
  base_ty T ->
  has_type empty analysis (Arrow T T) ->
  commutes T cfg analysis.
Proof.
  intros T cfg analysis Hbt HLR.
  apply soundness. assumption.
  replace (lift analysis) with (msubst' [] (lift analysis)) by reflexivity.
  replace analysis with (msubst [] analysis) by reflexivity.
  apply (completeness []); auto.
  apply V_nil.
Qed.


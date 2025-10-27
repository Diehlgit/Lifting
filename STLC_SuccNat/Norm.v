Require Import String List Maps.
Import ListNotations.
Require Import STLC_SuccNat.
Require Import Enviroments.

Hint Constructors multi : core.
Hint Constructors value : core.
Hint Constructors step : core.
Hint Constructors has_type : core.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

Definition halts t : Prop := exists t', multi step t t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  - apply multi_refl.
  - assumption.
Qed.

Inductive appears_free_in : string -> tm -> Prop :=
  |afi_var : forall (x:string), appears_free_in x (var x)
  |afi_app1 : forall x t1 t2,
    appears_free_in x t1 -> appears_free_in x (app t1 t2)
  |afi_app2 : forall x t1 t2,
    appears_free_in x t2 -> appears_free_in x (app t1 t2)
  |afi_abs : forall x y T11 t12,
    y <> x -> appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  (* nats*)
  |afi_succ : forall x t1, appears_free_in x t1 -> appears_free_in x (succ t1).

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance: forall Gamma Gamma' t S,
  has_type Gamma t S ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  has_type Gamma' t S.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; eauto 12.
  - (* T_Var *)
    apply T_Var. rewrite <- H0; auto.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... *)
    destruct (eqb_spec x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      auto.
Qed.

Ltac false_eqb_string :=
  try match goal with
      | [ H: (?x <> ?y)%string |- _ ] => apply eqb_neq in H; rewrite H in *
      | [ H: ?x <> ?y |- _ ] => apply eqb_neq in H; rewrite H in *
  end.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    false_eqb_string...
Qed.

Corollary typable_empty__closed : forall t T,
    has_type empty t T  -> closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Fixpoint R (T:ty) (t:tm) : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
    | Nat => True
    | Arrow T1 T2 => (forall s, R T1 s -> R T2 (app t s))
    end).

(* Proving that the relation has the wanted property *)
Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [_ [H _] ]; assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.

(* Proving some lemmas about relation preservation under
   language evaluation *)
Lemma step_preserves_halting :
  forall t t', (step t t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V] ].
  destruct STM.
   + value_no_step.
   + rewrite (determinism _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V] ].
  exists t'0. split; auto.
  apply multi_step with (y:= t'); auto.
Qed.

Lemma step_preserves_R : forall T t t', (step t t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt] ].
  (* Arrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  (* Nat *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
Qed.

Lemma multistep_preserves_R : forall T t t',
  (multi step t t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

Lemma step_preserves_R' : forall T t t',
  has_type empty t T -> (step t t') -> R T t' -> R T t.
Proof.
  induction T; intros t t' typable_empty_t E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t' [halts_t' RRt] ].
  (* Arrow *)
  split. auto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  eapply T_App; eauto.
  apply R_typable_empty; auto.
  eapply ST_App1. apply E.
  apply RRt; auto.
  (* Nat *)
  split. auto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
Qed.

Lemma multistep_preserves_R' : forall T t t',
  has_type empty t T -> (multi step t t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', subst x t' t = t.
Proof with eauto.
  induction t; intros x Hnafi t';
    simpl; eauto.
  - (* Var *)
    rename s into y. destruct (eqb_spec x y); simpl.
    exfalso. subst...
    reflexivity.
  - (* App *)
    rewrite IHt1, IHt2.
    reflexivity.
    intros H; eauto.
    intros H; eauto.
  - (* Abs *)
    rename s into y. destruct (eqb_spec x y); simpl.
    reflexivity.
    f_equal. apply IHt.
    intros H. apply Hnafi.
    apply afi_abs...
  - (* Succ *)
    rewrite IHt...
Qed.

Lemma subst_closed: forall t,
  closed t -> forall x t', subst x t' t = t.
Proof.
  intros. apply vacuous_substitution. apply H.
Qed.

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

Lemma subst_not_afi : forall t x v,
    closed v ->  ~ appears_free_in x (subst x v t).
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
    - (* var *)
     destruct (eqb_spec x s)...
     inversion A; subst. auto.
    - (* app *)
     inversion A; subst...
    - (* abs *)
     destruct (eqb_spec x s)...
     + inversion A; subst...
     + inversion A; subst...
    - (* const *)
     inversion A.
    - (* succ *)
     inversion A; subst...
Qed.

Lemma duplicate_subst : forall t' x t v,
  closed v -> (subst x t (subst x v t')) = (subst x v t').
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi. assumption.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    (subst x1 v1 (subst x v t)) = (subst x v(subst x1 v1 t)).
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite String.eqb_refl. apply subst_closed...
   + subst. simpl. rewrite String.eqb_refl. rewrite subst_closed...
   + simpl. apply eqb_neq in n, n0. rewrite n, n0...
  - (* app *)
   rewrite IHt1, IHt2...
  - (* abs *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite eqb_refl. apply eqb_neq in n; rewrite n...
   + subst. simpl. rewrite eqb_refl. apply eqb_neq in n; rewrite n...
   + simpl. apply eqb_neq in n, n0; rewrite n, n0...
     rewrite IHt...
  - (* const *)
   reflexivity.
  - (* succ *)
   rewrite IHt...
Qed.

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env (subst x v t) = subst x v (msubst (drop x env) t) .
Proof.
  induction env; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (eqb_spec s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.

Inductive instantiation : tass -> env -> Prop :=
  | V_nil : instantiation nil nil
  | V_cons : forall x T v c e,
      value v -> R T v ->
      instantiation c e ->
      instantiation ((x,T)::c) ((x,v)::e).

Lemma instantiation_domains_match: forall {c} {e},
  instantiation c e ->
  forall {x} {T},
    lookup x c= Some T -> exists t, lookup x e = Some t.
Proof.
  intros x e V. induction V; intros x0 T0 C.
    solve_by_inverts 1.
    simpl in *.
    destruct (eqb x x0); eauto.
Qed.

Lemma instantiation_env_closed :forall c e,
  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split; [|assumption].
    eapply typable_empty__closed. eapply R_typable_empty. eauto.
Qed.

Lemma instantiation_R : forall c e,
  instantiation c e ->
  forall x t T,
    lookup x c = Some T ->
    lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve_by_inverts 1.
    unfold lookup in *. destruct (eqb x x').
      inversion G; inversion E; subst. auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop.
    destruct (String.eqb x x0); auto. constructor; eauto.
Qed.

Lemma msubst_var: forall ss x, closed_env ss ->
  msubst ss (var x) =
  match lookup x ss with
  | Some t => t
  | None => var x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (eqb s x).
        apply msubst_closed. inversion H; auto.
        apply IHss. inversion H; auto.
Qed.

Lemma msubst_preserves_typing : forall c e,
  instantiation c e->
  forall Gamma t S, has_type (mupdate Gamma c) t S ->
  has_type Gamma (msubst e t) S.
Proof.
    intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.

Lemma msubst_R : forall c env t T,
  has_type (mupdate empty c) t T ->
  instantiation c env ->
  R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. reflexivity.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.

  - (*T_Var*)
    rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
    eapply instantiation_R; eauto.
    rewrite msubst_var. rewrite P. auto. eapply instantiation_env_closed; eauto.
  - (*T_Abs*)
    rewrite msubst_abs.
    assert (WT: has_type empty (abs x T2 (msubst (drop x env0) t)) (Arrow T2 T1)).
    { eapply T_Abs. eapply msubst_preserves_typing.
          { eapply instantiation_drop; eauto. }
          eapply context_invariance.
          { apply HT. }
          intros.
          unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).
          + auto.
          + rewrite H.
            clear - c n. induction c.
            simpl. false_eqb_string; auto.
            simpl. destruct a.  unfold update, t_update.
            destruct (String.eqb s x0); auto. }
        unfold R. fold R. split.
           auto.
         split. apply value_halts. apply v_abs.
         intros.
         destruct (R_halts H0) as [v [P Q] ].
         pose proof (multistep_preserves_R _ _ _ P H0).
         apply multistep_preserves_R' with (msubst ((x,v)::env0) t).
            eapply T_App. eauto.
            apply R_typable_empty; auto.
            eapply multi_step_trans. eapply multistep_App2; eauto.
            eapply multi_step with (y:= (msubst ((x, v) :: env0) t)); [|apply multi_refl].
            simpl.  rewrite subst_msubst.
            eapply ST_AppAbs; eauto.
            eapply typable_empty__closed.
            apply (R_typable_empty H1).
            eapply instantiation_env_closed; eauto.
            eapply (IHHT ((x,T2)::c)).
               intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
            constructor; auto.
  - (* T_App *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1] ].
    pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.
  - (* T_Const *)
     rewrite msubst_const.
     split. auto. split. apply value_halts; auto. auto.
  - (* T_Succ *)
    rewrite msubst_succ.
    apply (IHHT c H env0) in V as IH.
    clear IHHT.
    destruct (R_halts IH) as [v [Hm Hv] ].
    apply R_typable_empty in IH as H1.
    eapply multistep_preserves_R'.
      eauto.
      eapply multistep_succ. exact Hm.
    eapply (multistep_preserves_R _ _ _ Hm) in IH.
    destruct IH as [A [B C] ].
    split; [|split].
      eauto.
      apply (canonical_forms_nat v A) in Hv as [n Hv].
      rewrite Hv. exists (const (S n)); eauto.
      auto.
Qed.

Theorem normalization : forall t T, has_type empty t T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.

Corollary analysis_normalization: forall analysis T1 T2,
  has_type empty analysis (Arrow T1 T2) ->
  exists v, multi step analysis v /\ (exists x body, v = abs x T1 body).
Proof.
  intros.
  assert (H0: halts analysis).
  { eapply normalization. exact H. }
  destruct H0 as [v [H1 H2] ].
  exists v. split.
  - exact H1.
  - apply (preservation_multi _ _ _ H) in H1.
    apply (canonical_forms_fun _ _ _ H1 H2).
Qed.


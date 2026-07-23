From Stdlib Require Import String List.

Import List.ListNotations.
Open Scope list_scope.
From STLC Require Import STLC_SuccNat Presence_Conditions.
Require Export Presence_Conditions.

(* Automatic lifting *)
Inductive ty' : Type :=
  | Arrow' : ty' -> ty' -> ty'
  | Nat' : ty'
  | NatList' : ty'.

Fixpoint lift_ty (T : ty) : ty' :=
  match T with
    | Nat => Nat'
    | Arrow T1 T2 => Arrow' (lift_ty T1) (lift_ty T2)
    | NatList => NatList'
  end.

Definition nat' := variational_value nat.

Inductive tm' :=
  | var' : string -> tm'
  | abs' : string ->  ty' -> tm' -> tm'
  | app' : tm' -> tm' -> tm'
  | fixp' : tm' -> tm'

  | const' : nat' -> tm'
  | succ' : tm' -> tm'
  | add' : tm' -> tm' -> tm'

  | nil' :  tm'
  | cons' : tm' -> tm' -> tm'
  | case' : tm' -> tm' -> string -> string -> tm' -> tm'.

Fixpoint lift (t:tm) : tm':=
  match t with
  | var s => (var' s)
  | abs s T t => (abs' s (lift_ty T) (lift t))
  | app t1 t2 => (app' (lift t1) (lift t2))
  | fixp t => (fixp' (lift t))

  | const n => (const' [(n, pc_True)])
  | succ t => (succ' (lift t))
  | add t1 t2 => (add' (lift t1) (lift t2))

  | nil => nil'
  | cons t1 t2 => cons' (lift t1) (lift t2)
  | case t1 tnil x y tcons => case' (lift t1) (lift tnil) x y (lift tcons)
  end.

Inductive value' : tm' -> Prop :=
  | v_abs' : forall x T' t', value' (abs' x T' t')
  | v_nat' : forall n', value' (const' n')
  | v_lnil' : value' nil'
  | v_lcons' : forall v1' v2', value' v1' -> value' v2' -> value' (cons' v1' v2').

Fixpoint subst' (x:string) (s' t': tm'): tm' :=
  match t' with
  | var' y => if String.eqb x y then s' else t'
  | abs' y T' t1' => if String.eqb x y then t' else abs' y T' (subst' x s' t1')
  | app' t1' t2' => app' (subst' x s' t1') (subst' x s' t2')
  | fixp' t1' => fixp' (subst' x s' t1')

  | const' _ => t'
  | succ' t1' => succ' (subst' x s' t1')
  | add' t1' t2' => add' (subst' x s' t1') (subst' x s' t2')

  | nil' => nil'
  | cons' t1' t2' => cons' (subst' x s' t1') (subst' x s' t2')
  | case' t1' t2' y z t3' => case' (subst' x s' t1') (subst' x s' t2') y z
                                        (if (orb (eqb x y) (eqb x z)) then t3' else (subst' x s' t3'))
  end.

Inductive step': tm' -> tm' -> Prop :=
  | ST_App': forall t1' t1'' t2',
    step' t1' t1'' ->
      step' (app' t1' t2') (app' t1'' t2')
  | ST_AppAbs': forall x T' t' v',
    step' (app' (abs' x T' t') v') (subst' x v' t')
  | ST_FixpAbs': forall x T' t',
    step' (fixp' (abs' x T' t')) (app' (abs' x T' t') (fixp' (abs' x T' t')))
  | ST_Fixp' : forall t1' t2',
    step' t1' t2' ->
    step' (fixp' t1') (fixp' t2')

  | ST_Succ': forall t' t'',
    step' t' t'' ->
      step' (succ' t') (succ' t'')
  | ST_SuccConst': forall n',
      step' (succ' (const' n'))
      (const' (List.map (fun '(n,pc) => ((S n), pc)) n'))
  
  | ST_Add1' : forall t1' t1'' t2',
      step' t1' t1'' ->
        step' (add' t1' t2') (add' t1'' t2')
  | ST_Add2' : forall v1' t2' t2'',
      value' v1' ->
      step' t2' t2'' ->
        step' (add' v1' t2') (add' v1' t2'')
  | ST_AddConst' : forall n1' n2',
      step' (add' (const' n1') (const' n2')) (const' (app_binop Nat.add n1' n2'))

  | ST_Cons1': forall t1' t2' t3',
    step' t1' t2' ->
    step' (cons' t1' t3') (cons' t2' t3')
  | ST_Cons2': forall v1' t2' t3',
    value' v1' ->
    step' t2' t3' ->
    step' (cons' v1' t2') (cons' v1' t3')
  | ST_Case1': forall x y t1' t2' tnil' tcons',
    step' t1' t2' ->
    step' (case' t1' tnil' x y tcons') (case' t2' tnil' x y tcons')
  | ST_CaseNil': forall x y tnil' tcons',
    step' (case' nil' tnil' x y tcons') tnil'
  | ST_CaseCons': forall x y vh' vt' tnil' tcons',
    value' vh' ->
    value' vt' ->
    step' (case' (cons' vh' vt') tnil' x y tcons') (subst' y vt' (subst' x vh' tcons')).

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
  | T_Fixp' : forall Gamma' T1' t1',
    has_type' Gamma' t1' (Arrow' T1' T1') ->
      has_type' Gamma' (fixp' t1') T1'

  | T_Nat' : forall Gamma' (n' : nat'),
    has_type' Gamma' (const' n') Nat'
  | T_Succ' : forall Gamma' t',
    has_type' Gamma' t' Nat' ->
      has_type' Gamma' (succ' t') Nat'
  | T_Add' : forall Gamma' t1' t2',
    has_type' Gamma' t1' Nat' ->
    has_type' Gamma' t2' Nat' ->
      has_type' Gamma' (add' t1' t2') Nat'

  | T_Nil' : forall Gamma',
    has_type' Gamma' nil' NatList'
  | T_Cons' : forall Gamma' t1' t2',
    has_type' Gamma' t1' Nat' ->
    has_type' Gamma' t2' NatList' ->
      has_type' Gamma' (cons' t1' t2') NatList'
  | T_Case' : forall Gamma' x y T' t1' tnil' tcons',
    has_type' Gamma' t1' NatList' ->
    has_type' Gamma' tnil' T' ->
    has_type' (x |-> Nat'; y |-> NatList'; Gamma') tcons' T' ->
    has_type' Gamma' (case' t1' tnil' x y tcons') T'.

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
  destruct HVal as [x ? t1'| | |] ; inversion HT; subst.
  exists x, t1'. reflexivity.
Qed.

Lemma canonical_forms_list' : forall t',
  has_type' empty t' NatList' ->
  value' t' ->
    t' = nil' \/
    (exists v1' v2',
      value' v1' /\ value' v2' /\ t' = (cons' v1' v2')).
Proof.
  intros t HT Hv.
  destruct Hv; inversion HT; subst; eauto 7.
(*- auto.
  - right. exists v1, v2.
    split; [auto|split;auto]. *)
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
    destruct (eqb_spec x s); subst; simpl; try (constructor).
    + rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty'. assumption.
    + rewrite update_neq in H2; auto.
    + rewrite update_shadow in H5. assumption.
    + apply IHt'. eapply update_permute in n.
      rewrite n in H5. assumption.
    + destruct (eqb_spec s s0); subst.
      * repeat rewrite update_shadow in H9.
        rewrite update_shadow. assumption.
      * rewrite update_permute in H9; auto.
        rewrite update_shadow in H9.
        rewrite update_permute; auto.
    + destruct (eqb_spec x s0); subst.
      * rewrite update_shadow in H9. assumption.
      * apply IHt'3. assert (
          (x) |-> U'; (s) |-> Nat'; (s0) |-> NatList'; Gamma' =
          (s) |-> Nat'; (s0) |-> NatList'; (x) |-> U'; Gamma').
        { rewrite update_permute; auto. f_equal.
          rewrite update_permute; auto. }
        rewrite H. assumption.
Qed.

(* Auxialiary Mapping theorems *)
Theorem mapping_not_change_deriving: forall (spl:nat') (cfg:feat_config) (p:nat) (analysis:nat->nat),
  derive spl cfg = Some p ->
  derive (List.map (fun '(n, pc) => (analysis n, pc)) spl) cfg = Some (analysis p).
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

Theorem binop_not_change_deriving: forall (spl1 spl2:nat') (conf:feat_config) (p1 p2:nat) (binop:nat->nat->nat),
  derive spl1 conf = Some p1 ->
  derive spl2 conf = Some p2 ->
  derive (app_binop binop spl1 spl2) conf = Some (binop p1 p2).
Proof.
  induction spl1; intros.
  - inversion H.
  - destruct a.
    rewrite app_binop_distributive.
    simpl in H.
    destruct (pc_eval conf p) eqn:EQ1.
    + apply derive_l.
      induction spl2. inversion H0.
      destruct a. simpl in H0.
      destruct (pc_eval conf p0) eqn:EQ2.
      { simpl. rewrite EQ1, EQ2. simpl.
        inversion H. inversion H0.
        reflexivity. }
      { simpl. rewrite EQ1, EQ2. simpl.
        simpl in IHspl2. apply IHspl2.
        assumption. }
    + apply derive_r.
      { apply derive_binop_none. assumption. }
      { apply IHspl1; assumption. }
Qed.

Lemma map_map_fst: forall {A B: Type} (l: list (A*B)) (f g: A -> A),
  List.map (fun '(v2, pc2) => (g v2, pc2)) (List.map (fun '(v1, pc1) => (f v1, pc1)) l) =
  List.map (fun '(v3, pc3) => (g (f v3), pc3)) l.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    f_equal. destruct a.
    reflexivity.
Qed.

(* Language Theorems *)

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
  - (* T_Fixp' *)
    eapply T_Fixp'.
    apply IHH_type. exact H_equiv.
  - (* T_Nat' *)
    apply T_Nat'.
  - (* T_Succ' *)
    apply T_Succ'.
    apply IHH_type. exact H_equiv.
  - (* T_Add' *)
    apply T_Add'.
    + apply IHH_type1. exact H_equiv.
    + apply IHH_type2. exact H_equiv.
  - (* T_Nil' *)
    apply T_Nil'.
  - (* T_Cons' *)
    eapply T_Cons'.
    + apply IHH_type1. exact H_equiv.
    + apply IHH_type2. exact H_equiv.
  - (* T_Case' *)
    eapply T_Case'.
    + apply IHH_type1. assumption.
    + apply IHH_type2. assumption.
    + apply IHH_type3. intro z.
      unfold update.
      destruct (eqb x z) eqn:Heq;
        unfold t_update;
        rewrite Heq; auto.
      destruct (eqb y z) eqn:Heq0; auto.
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
  - apply has_type'_lookup_equiv with (lift_context (x) |-> Nat; (y) |-> NatList; Gamma).
    + intro z. repeat rewrite lift_context_update.
      destruct (eqb_spec x z), (eqb_spec y z);
        subst; unfold update;
        try (rewrite t_update_eq; auto);
        try (rewrite t_update_neq; auto).
        rewrite t_update_eq; auto.
        rewrite t_update_neq; auto.
    + exact IHhas_type3.
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
  - (* Var *)
    destruct (eqb_spec x s);
    reflexivity.
  - (* Abs *)
    destruct (eqb_spec x s).
    + reflexivity.
    + simpl. rewrite IHbody.
      reflexivity.
  - (* App *)
    rewrite IHbody1.
    rewrite IHbody2.
    reflexivity.
  - (* Fixp *)
    rewrite IHbody. reflexivity.
  - (* Const *)
    reflexivity.
  - (* Succ *)
    rewrite IHbody.
    reflexivity.
  - (* Add *)
    rewrite IHbody1, IHbody2.
    reflexivity.
  - (* Nil *)
    reflexivity.
  - (* Cons *)
    rewrite IHbody1.
    rewrite IHbody2.
    reflexivity.
  - (* Case *)
    destruct (eqb_spec x s), (eqb_spec x s0);
    rewrite IHbody1, IHbody2;
     simpl; auto.
    rewrite IHbody3; reflexivity.
Qed.

Lemma value_value': forall v,
  value v -> value' (lift v).
Proof.
  induction v; intros Hv;
    try solve_by_inverts 2;
    constructor;
    try inversion Hv; auto.
Qed.

Lemma value'_is_nf: forall t',
  value' t' -> step'_normal_form_of t' t'.
Proof.
  induction t'; intros Hv;
  split;
    try inversion Hv; subst;
    try (intros [t1' Hc]; inversion Hc);
    try constructor.
  - subst. apply IHt'1 in H1.
    apply H1. exists t2'. assumption.
  - subst. apply IHt'2 in H2.
    apply H2. exists t3'. assumption.
Qed.
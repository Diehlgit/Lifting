From Stdlib Require Import String List.

Import List.ListNotations.
Open Scope list_scope.
Require Import Languages_Scheme.PCFm_Base.
Require Export Languages_Scheme.Presence_Conditions.

(* Automatic lifting *)
Inductive ty' : Type :=
  | Arrow' : ty' -> ty' -> ty'
  | Nat' : ty'
  | NatList' : ty'.

Notation "S ->' T" := (Arrow' S T) (at level 99, right associativity).

Definition nat' := variational_primitive_type nat.

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

(* Language Theorems *)
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

Ltac value'_no_step :=
	match goal with
	| [ H1: value' ?t, H2: step' ?t  _ |- _ ] =>
		exfalso; apply value'_is_nf in H1 as [_ H1]; eauto
  | [ H1: value' ?vh, H2: value' ?vt, H3: step' (cons' ?vh ?vt) _ |- _ ] =>
      exfalso;
      let Hv := fresh "Hv" in
      pose proof (v_lcons' vh vt H1 H2) as Hv;
      apply value'_is_nf in Hv as [_ Hv]; eauto
end.

Theorem preservation': forall t1' t2' T',
  has_type' empty t1' T' ->
  step' t1' t2' ->
  has_type' empty t2' T'.
Proof.
  intros t1' t2' T' Ht';
  generalize dependent t2'.
  remember empty as Gamma'.
  induction Ht'; intros t3' H0;
    inversion H0; subst;
      try (econstructor; eauto).
  - inversion Ht'1; subst.
    apply (T_App' _ _ _ _ _ Ht'1) in Ht'2.
      eapply substitution_preserves_typing'.
      eassumption.
      inversion Ht'2; inversion H4; subst;
      try eassumption.
  - inversion Ht'; subst.
    constructor. assumption.
  - assumption.
  - inversion Ht'1; subst.
    repeat eapply substitution_preserves_typing';
    eassumption.
Qed.

Lemma preservation'_multi: forall t1' t2' T',
  has_type' empty t1' T' ->
  multi step' t1' t2' ->
  has_type' empty t2' T'.
Proof.
  intros t1' t2' T' Htype' Hmulti'.
  induction Hmulti'.
  - assumption.
  - apply (preservation' _ _ _ Htype') in H.
    apply IHHmulti'. apply H.
Qed.

Theorem progress' : forall t1' T',
    has_type' empty t1' T' ->
      value' t1' \/ exists t2', step' t1' t2'.
Proof.
  intros t1' T' Ht1'.
  remember empty as Gamma.
  induction Ht1'; subst Gamma';
    try (left; solve [constructor]).
  - inversion H.
  - right. destruct IHHt1'1;
    destruct IHHt1'2; unfold_exists; eauto using ST_App', ST_AppAbs';
      eapply canonical_forms_fun' in Ht1'1 as [x0 [u Ht1']]; subst;
      eauto; eexists; econstructor; assumption.
  - right. destruct IHHt1'; auto.
    + eapply canonical_forms_fun' in Ht1' as [x [u Ht1']]; subst;
      eauto; eexists; econstructor; assumption.
    + destruct H; eexists; eapply ST_Fixp'; eauto.
  - right. destruct IHHt1'; eauto.
    + eapply canonical_forms_nat' in H as [n H]; subst; eauto.
      eexists. apply ST_SuccConst'.
    + destruct H; eexists; eapply ST_Succ'; eauto.
  - right. destruct IHHt1'2;
    destruct IHHt1'1; unfold_exists; eauto using ST_Add1', ST_Add2'.
    eapply canonical_forms_nat' in H as [n2 H]; subst; auto.
    eapply canonical_forms_nat' in H0 as [n1 H0]; subst; auto.
    exists (const' (app_binop Nat.add n1 n2)). apply ST_AddConst'.
  - destruct IHHt1'1, IHHt1'2;
      try reflexivity.
    + left. constructor; assumption.
    + right. destruct H0 as [t3' H0].
      exists (cons' t1' t3'). apply ST_Cons2'; assumption.
    + right. destruct H as [t3' H].
      exists (cons' t3' t2'). apply ST_Cons1'; assumption.
    + right. destruct H as [t3' H]. 
      exists (cons' t3' t2'). apply ST_Cons1'; assumption.
  - right. destruct IHHt1'1; try reflexivity.
    + apply canonical_forms_list' in H as [H | [v1' [v2' [Hv1' [Hv2' H]]]]];
      subst.
      * exists tnil'. apply ST_CaseNil'; assumption.
      * exists (subst' y v2' (subst' x v1' tcons')).
        apply ST_CaseCons'; assumption.
      * assumption.
    + destruct H as [t2' H]. exists (case' t2' tnil' x y tcons').
      apply ST_Case1'; assumption.
Qed.

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

Theorem normal_forms'_unique: forall t1' t2' t3',
  step'_normal_form_of t1' t2' ->
  step'_normal_form_of t1' t3' ->
  t2' = t3'.
Proof.
  intros t1' t2' t3' P1 P2.
  destruct P1 as [P12 Pnf2].
  destruct P2 as [P13 Pnf3].
  induction P12; subst;
    inversion P13; subst;
    try (apply (IHP12 Pnf2)).
  - reflexivity.
  - destruct Pnf2. eauto.
  - destruct y; destruct Pnf3; eauto.
  - remember (determinism' _ _ _ H H0) as e. congruence.
Qed.

Theorem types'_unique: forall Gamma t' T1' T2',
  has_type' Gamma t' T1' ->
  has_type' Gamma t' T2' ->
  T1' = T2'.
Proof.
  intros Gamma t'.
  generalize dependent Gamma.
  induction t'; intros Gamma T1' T2' HT1' HT2';
    inversion HT1'; subst;
    inversion HT2'; subst;
    try reflexivity.
  - rewrite H1 in H2.
    injection H2 as H2.
    assumption.
  - f_equal. eapply IHt'; eassumption.
  - pose proof (IHt'1 Gamma (T2'0 ->' T1') (T2'1 ->' T2') H2 H3).
    inversion H. reflexivity.
  - pose proof (IHt' Gamma (T1' ->' T1') (T2' ->' T2') H1 H2).
    inversion H. reflexivity.
  - pose proof (IHt'2 Gamma T1' T2' H7 H10).
    assumption.
Qed.
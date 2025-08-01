Require Import STLC_SuccNat.
Require Import String List Maps.
Import ListNotations.

Open Scope string_scope.
(* A Feature is represented by a string *)
Definition Feature := string.

(*A Feature Configuration is a list of features *)
Definition FeatureConfig := list Feature.

(* A Presence Condition is a Boolean expression over features *)
Inductive PresenceCondition : Type :=
  | PC_Feature : Feature -> PresenceCondition
  | PC_And     : PresenceCondition -> PresenceCondition -> PresenceCondition
  | PC_Or      : PresenceCondition -> PresenceCondition -> PresenceCondition
  | PC_Not     : PresenceCondition -> PresenceCondition
  | PC_True    : PresenceCondition
  | PC_False   : PresenceCondition.

Declare Custom Entry pc_syntax.

Notation "x" := x (in custom pc_syntax at level 0, x constr).
Notation "'FEATURE' f" := (PC_Feature f)
  (in custom pc_syntax at level 0, f constr).
Notation "x '/\' y" := (PC_And x y)
  (in custom pc_syntax at level 40, left associativity).
Notation "x '\/' y" := (PC_Or x y)
  (in custom pc_syntax at level 50, left associativity).
Notation "'~' x" := (PC_Not x)
  (in custom pc_syntax at level 35, right associativity).
Notation "'TRUE'" := PC_True (in custom pc_syntax at level 0).
Notation "'FALSE'" := PC_False (in custom pc_syntax at level 0).
Notation "'(' x ')'" := x
  (in custom pc_syntax, x at level 0).
Notation "'[[' x ']]'" := x
  (at level 0, x custom pc_syntax at level 99).

(* Function that evaluates a Presence Condition given a Feature Configuration *)
Fixpoint pc_eval (cfg : FeatureConfig) (pc : PresenceCondition) : bool :=
  match pc with
  | PC_Feature f => if in_dec String.string_dec f cfg then true else false
  | PC_And p1 p2 => pc_eval cfg p1 && pc_eval cfg p2
  | PC_Or  p1 p2 => pc_eval cfg p1 || pc_eval cfg p2
  | PC_Not p1   => negb (pc_eval cfg p1)
  | PC_True => true
  | PC_False => false
  end.

(* Automatic lifting *)
Inductive ty' : Type :=
  | Arrow' : ty' -> ty' -> ty'
  | Nat' : ty'.

Fixpoint lift_ty (T : ty) : ty' :=
  match T with
    | Nat => Nat'
    | Arrow T1 T2 => Arrow' (lift_ty T1) (lift_ty T2)
  end.

Definition nat' := list (nat * PresenceCondition).

Inductive tm' :=
  | var' : string -> tm'
  | abs' : string ->  ty' -> tm' -> tm'
  | app' : tm' -> tm' -> tm'

  | const' : nat' -> tm'
  | succ' : tm' -> tm'.

Fixpoint lift (t:tm) : tm':=
  match t with
  | var s => (var' s)
  | abs s T t => (abs' s (lift_ty T) (lift t))
  | STLC_SuccNat.app t1 t2 => (app' (lift t1) (lift t2))

  | const n => (const' [(n, [[TRUE]])])
  | succ t => (succ' (lift t))
  end.

Fixpoint derive (n' : nat') (cfg : FeatureConfig) : option nat :=
  match n' with
  | [] => None
  | (n, pc) :: rest =>
    if pc_eval cfg pc then Some n
    else derive rest cfg
  end.

Definition disjoint (pc1 pc2 : PresenceCondition) : Prop :=
  forall (cfg : FeatureConfig), ~(pc_eval cfg pc1 = true /\ pc_eval cfg pc2 = true).

Fixpoint disjointness (l : nat') : Prop :=
  match l with
  | [] => True
  | (_, pc) :: rest =>
      (forall t' pc', In (t', pc') rest -> disjoint pc pc') /\ disjointness rest
  end.

Inductive value' : tm' -> Prop :=
  | v_abs' : forall x T' t', value' (abs' x T' t')
  | v_nat' : forall n', value' (const' n').

Fixpoint subst' (x:string) (s' t': tm'): tm' :=
  match t' with
  | var' y => if String.eqb x y then s' else t'
  | abs' y T' t1' => if String.eqb x y then t' else abs' y T' (subst' x s' t1')
  | app' t1' t2' => app' (subst' x s' t1') (subst' x s' t2')
  | const' _ => t'
  | succ' t1' => succ' (subst' x s' t1')
  end.

Inductive step': tm' -> tm' -> Prop :=
  | ST_App1': forall t1' t1'' t2',
    step' t1' t1'' ->
      step' (app' t1' t2') (app' t1'' t2')
  | ST_App2': forall v' t2' t2'',
    value' v' ->
    step' t2' t2'' ->
      step' (app' v' t2') (app' v' t2'')
  | ST_AppAbs': forall x T' t' v',
    value' v' ->
      step' (app' (abs' x T' t') v') (subst' x v' t')
  | ST_Succ': forall t' t'',
    step' t' t'' ->
      step' (succ' t') (succ' t'')
  | ST_SuccConst': forall n',
      step' (succ' (const' n'))
      (const' (map (fun '(n,pc) => ((S n), pc)) n')).

Definition step'_normal_form_of t' t'':=
  (multi step' t' t'' /\ normal_form step' t'').

Theorem mapping_not_change_deriving: forall (spl:nat') (cfg:FeatureConfig) (p:nat) (analisys:nat->nat),
  derive spl cfg = Some p ->
  derive (map (fun '(n, pc) => (analisys n, pc)) spl) cfg = Some (analisys p).
Proof.
  induction spl;
  intros cfg p analisys Hd.
  - inversion Hd.
  - destruct a. simpl in Hd.
    destruct (pc_eval cfg p0) eqn: EQ.
    + simpl. rewrite EQ in *.
      f_equal. injection Hd as Hd.
      f_equal. assumption.
    + simpl. rewrite EQ in *.
      apply IHspl. assumption.
Qed.

Lemma map_map_pairs: forall {A B: Type} (l: list (A*B)) (f g: A -> A),
  map (fun '(v2, pc2) => (g v2, pc2)) (map (fun '(v1, pc1) => (f v1, pc1)) l) =
  map (fun '(v3, pc3) => (g (f v3), pc3)) l.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    f_equal. destruct a.
    reflexivity.
Qed.

Lemma succ'_arg_normalizes: forall t1' t2',
  step'_normal_form_of t1' t2' ->
  multi step' (succ' t1') (succ' t2').
Proof.
  intros t1' t2' [Hms' Hnf'].
  induction Hms'; subst.
  - apply multi_refl.
  - apply IHHms' in Hnf'.
    eapply multi_step.
    + apply ST_Succ'. exact H.
    + exact Hnf'.
Qed.

Lemma multi_step'_trans: forall t1' t2' t3',
  multi step' t1' t2' ->
  multi step' t2' t3' ->
  multi step' t1' t3'.
Proof.
  intros t1' t2' t3' H12 H23.
  induction H12.
  - exact H23.
  - apply IHmulti in H23.
    eapply multi_step.
    + exact H.
    + exact H23.
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
Qed.

Ltac value'_no_step :=
	match goal with
	| [ H1: value' ?t, H2: step' ?t  _ |- _ ] =>
		exfalso; apply value'_is_nf in H1 as [_ H1]; eauto
	end.

Theorem determinism' : forall t1' t2' t3',
  step' t1' t2' -> step' t1' t3' -> t2' = t3'.
Proof.
  intros t1' t2' t3' Ht.
  generalize dependent t3'.
  induction Ht; intros t3' Ht';
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


(*
On the correctness of lifting:
  Given an analisys and a Software product Line spl.
  We say that the lifting of this analisys (analisys') is correct if
  for all derivations of spl (spl|cfg), analisys (spl|cfg) = r => (analisys' spl)|cfg = r.
*)

Theorem lifting_correctness: forall (analisys:tm) (cfg:FeatureConfig) (spl r':nat') (p r:nat),
  (derive spl cfg) = Some p ->
  step_normal_form_of (STLC_SuccNat.app analisys (const p)) (const r) ->
  step'_normal_form_of (app' (lift analisys) (const' spl)) (const' r') ->
  (derive r' cfg) = Some r.
Proof.
  intros analisys cfg spl r' p r Hd [Hmstep Hnf] [Hmstep' Hnf'].
  Abort.

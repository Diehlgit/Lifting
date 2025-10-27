Require Import List String.
Require Import Presence_Conditions.

Import ListNotations.

Open Scope string_scope.

(* Presence Condition Evaluation Examples *)
                               (* A /\ B *)
Example pc: pc_eval ["A"; "B"] (pc_And (pc_Feature "A") (pc_Feature "B")) = true.
Proof. reflexivity. Qed.
                                (* ~ C *)
Example pc2: pc_eval [] (pc_Not (pc_Feature "C")) = true.
Proof. reflexivity. Qed.
                                     (* A /\ (~B \/ C) *)
Example pc3: pc_eval ["A"; "B"; "C"] (pc_And (pc_Feature "A") (pc_Or (pc_Not (pc_Feature "B")) (pc_Feature "C"))) = true.
Proof. reflexivity. Qed.
                           (* TRUE /\ A *)
Example pc4: pc_eval ["A"] (pc_And pc_True (pc_Feature "A")) = true.
Proof. reflexivity. Qed.
                           (* FALSE /\ A *)
Example pc5: pc_eval ["A"] (pc_And pc_False (pc_Feature "A")) = false.
Proof. reflexivity. Qed.

Require Import STLC_SuccNat Maps.
(*Example functions plusone and plustwo*)
Definition plusone := abs "n" Nat (succ (var "n")).

Definition plustwo := abs "n" Nat (succ (succ (var "n"))).

Example ty_plusone: has_type empty plusone (Arrow Nat Nat).
Proof.
  apply T_Abs.
  apply T_Succ.
  apply T_Var.
  reflexivity.
Qed.

Example ty_plustwo: has_type empty plustwo (Arrow Nat Nat).
Proof.
  apply T_Abs.
  apply T_Succ. apply T_Succ.
  apply T_Var. reflexivity.
Qed.

Example plusone_0_is_1:
  step_normal_form_of (STLC_SuccNat.app plusone (const 0)) (const 1).
Proof.
  split.
  - eapply multi_step.
    + apply ST_AppAbs. apply v_nat.
    + eapply multi_step.
      * simpl. eapply ST_SuccConst.
      * apply multi_refl.
  - intros [t' Contra]. inversion Contra.
Qed.

Example plustwo_3_is_5:
  step_normal_form_of (STLC_SuccNat.app plustwo (const 3)) (const 5).
Proof.
  split.
  - eapply multi_step.
    + apply ST_AppAbs. apply v_nat.
    + eapply multi_step.
      * simpl. eapply ST_Succ. apply ST_SuccConst.
      * eapply multi_step.
        ** apply ST_SuccConst.
        ** apply multi_refl.
  - intros [t' Contra]. inversion Contra.
Qed.

Require Import Lifted_STLC_SuccNat.

(*Automatic Lifting Examples*)
Example const1': lift (const 1) = const' [(1, pc_True)].
Proof. simpl. reflexivity. Qed.

Example plusone': lift plusone = abs' "n" Nat' (succ' (var' "n")).
Proof. simpl. reflexivity. Qed.

(*Some SPLs examples*)
Definition x':= [
       (* A *)
   (1, pc_Feature "A");
       (* (~ A) /\ B *)
   (2, pc_And (pc_Not (pc_Feature "A")) (pc_Feature "B"));
       (*  (~ A) /\ (~B) *)
   (3, pc_And (pc_Not (pc_Feature "A")) (pc_Not (pc_Feature "B")) )
  ].

Definition y' := [
        (* A /\ (~B) *)
    (5, pc_And (pc_Feature "A") (pc_Not (pc_Feature "B")));
        (* B *)
    (4, pc_Feature "B");
        (* (~A) /\ (~B) *)
    (3, pc_And (pc_Not (pc_Feature "A")) (pc_Not (pc_Feature "B")) )
  ].

Definition z' := [ (19, pc_True) ].

Ltac solve_by_inverts n :=
	match goal with | H : ?T  |-  _  =>
	match type of T with Prop =>
		solve [ inversion H;
		match n with S (S (?n')) =>
			subst; solve_by_inverts (S n') end ]
	end end.

(* plusone(x'|p) = (plusone'(x'))|p *)
Example comm_plusone_x': forall (cfg:feat_config) (x n:nat) (n':nat'),
  (derive x' cfg ) = Some x ->
  step_normal_form_of (STLC_SuccNat.app plusone (const x)) (const n) ->
  step'_normal_form_of (app' (lift plusone) (const' x')) (const' n') ->
  (derive n' cfg) = Some n.
Proof.
  unfold step_normal_form_of, step'_normal_form_of.
  intros cfg x n n' Hd [Hmstep Hnf] [Hmstep' Hnf'].

  (*Trying to simplify Hmstep*)
  inversion Hmstep; subst.
  inversion H; subst;
    try (solve_by_inverts 1).
  simpl in H0. inversion H0; subst.
  inversion H1; subst;
    try (solve_by_inverts 1).
  inversion H2; subst;
    try (solve_by_inverts 1).
  clear Hmstep H0 H H6 H2 H1.

  (*Trying to simplify Hmstep'*)
  inversion Hmstep'; subst.
  inversion H; subst;
    try (solve_by_inverts 1);
    clear Hmstep' H.
  inversion H0; subst.
  inversion H; subst;
    try (solve_by_inverts 1);
    clear H0 H.
  inversion H1; subst;
    try (solve_by_inverts 1).

  (* Case analysis on the feature configuration *)
  simpl; simpl in Hd.
  destruct in_dec.
  - injection Hd as Hd;
    subst; reflexivity.
  - destruct in_dec;
    injection Hd as Hd;
    subst; reflexivity.
Qed.

(* plusone(y'|p) = (plusone'(y'))|p *)
Example comm_plusone_y: forall (cfg:feat_config) (y n: nat) (n':nat'),
  (derive y' cfg) = Some y ->
  step_normal_form_of (STLC_SuccNat.app plusone (const y)) (const n) ->
  step'_normal_form_of (app' (lift plusone) (const' y')) (const' n') ->
  (derive n' cfg) = Some n.
Proof.
  unfold step_normal_form_of, step'_normal_form_of.
  intros cfg y n n' Hd [Hmstep _] [Hmstep' _].

  (*Simplifying Hmstep to find value of n*)
  inversion Hmstep; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H Hmstep.
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H H0.
  inversion H1; subst;
    try solve_by_inverts 1.
  clear H1 H6.

  (*Simplifying Hmstep' to find value of n'*)
  inversion Hmstep'; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H Hmstep'.
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 2;
    clear H H0.
  simpl in H1.
  inversion H1; subst;
    try solve_by_inverts 1.

  (* Case analysis on the feature configuration *)
  simpl; simpl in Hd.
  destruct in_dec; (*destruct in_dec as many times as there are features*)
  destruct in_dec;
    injection Hd as Hd;
    subst; reflexivity.
Qed.

(* plusone(z'|p) = (plusone'(z'))|p *)
Example comm_plusone_z: forall (cfg:feat_config) (z n: nat) (n':nat'),
  (derive z' cfg) = Some z ->
  step_normal_form_of (STLC_SuccNat.app plusone (const z)) (const n) ->
  step'_normal_form_of (app' (lift plusone) (const' z')) (const' n') ->
  (derive n' cfg) = Some n.
Proof.
  unfold step_normal_form_of, step'_normal_form_of.
  intros cfg z n n' Hd [Hmstep _] [Hmstep' _].
  simpl in Hd; injection Hd as Hz.

  (*Simplifying Hmstep to find value of n*)
  inversion Hmstep; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H Hmstep.
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H H0.
  inversion H1; subst;
    try solve_by_inverts 1.
  clear H1 H6.

  (*Simplifying Hmstep' to find value of n'*)
  inversion Hmstep'; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H Hmstep'.
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 2;
    clear H H0.
  simpl in H1.
  inversion H1; subst;
    try solve_by_inverts 1.

  simpl. reflexivity.
Qed.

Example lift_plusone_correct: forall spl cfg p r r',
  derive spl cfg = Some p ->
  step'_normal_form_of (app' (lift plusone) (const' spl)) (const' r') ->
  step_normal_form_of (app plusone (const p)) (const r) ->
  derive r' cfg = Some r.
Proof.
  intros spl cfg p r r' Hd [Hmstep' _] [Hmstep _].

  inversion Hmstep; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H6.
  simpl in H.
  inversion H0; subst.
  inversion H1; subst;
    try solve_by_inverts 1.
    clear H1 H0.
  inversion H2; subst;
    try solve_by_inverts 1;
    clear H H2.

  inversion Hmstep'; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H H6.
    simpl in H0.
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H H0.
  inversion H1; subst;
    try solve_by_inverts 1;
    clear H1.

  apply mapping_not_change_deriving.
  assumption.
Qed.

Ltac normalize :=
	(eapply multi_step;
		[ econstructor; econstructor 
		| try (eapply multi_refl; econstructor); normalize]).

Example lift_plustwo_correct: forall spl cfg p r r',
  derive spl cfg = Some p ->
  step'_normal_form_of (app' (lift plustwo) (const' spl)) (const' r') ->
  step_normal_form_of (app plustwo (const p)) (const r) ->
  derive r' cfg = Some r.
Proof.
  intros spl cfg p r r' Hd Hnf' Hnf.

  assert (Hr: step_normal_form_of (app plustwo (const p)) (const (S(S p)))).
  { split.
    - eapply multi_step.
      + econstructor; econstructor.
      + eapply multi_step.
        * econstructor. simpl. eapply ST_SuccConst.
        * normalize.
    - intros [t' contra]. inversion contra.
  }

  apply (normal_forms_unique _ _ _ Hnf) in Hr.
  injection Hr as Hr.

  assert (Hr': step'_normal_form_of (app' (lift plustwo) (const' spl))
                    (const' (map (fun '(n, pc) => (S n, pc)) (map (fun '(n, pc) => (S n, pc)) spl)))).
  { split.
    - eapply multi_step.
      + econstructor; econstructor.
      + eapply multi_step.
        * econstructor. eapply ST_SuccConst'.
        * normalize.
    - intros [t' contra]. inversion contra.
  }

  apply (normal_forms'_unique _ _ _ Hnf') in Hr'.
  injection Hr' as Hr'.

  subst.
  apply mapping_not_change_deriving.
  apply mapping_not_change_deriving.
  assumption.
Qed.

(* Trying to work with a general plus_n function *)

Fixpoint gen_plusn (n:nat) (t:tm) : tm :=
  match n with
  | O => t
  | S m => succ (gen_plusn m t)
  end.

Fixpoint gen_plusn' (n:nat) (t':tm') : tm' :=
  match n with
  | 0 => t'
  | S m => succ' (gen_plusn' m t')
  end.

Definition plusn (n:nat) : tm := abs "n" Nat (gen_plusn n (var "n")).

(* Compute subst "n" (const 0) (gen_plusn 1 (var "n")).
Compute plusn 0.
 *)

Lemma subst_gen_plusn: forall n s t,
  subst s t (gen_plusn n (var s)) = gen_plusn n t.
Proof.
  induction n; intros; simpl.
  - rewrite eqb_refl. reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma subst'_gen_plusn: forall n s t',
  subst' s t' (lift (gen_plusn n (var s))) = gen_plusn' n t'.
Proof.
  induction n; intros; simpl.
  - rewrite eqb_refl. reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(* Auxiliary proofs stating that the application of plusn and plusn'
   have closed forms.
*)

Lemma normal_form_plusn: forall n k,
    step_normal_form_of (app (plusn n) (const k)) (const (n + k)).
Proof.
  intros. induction n;
  split; try (intros [t contra]; inversion contra).
  - normalize.
  - unfold plusn in *.
    inversion IHn. clear H0.
    inversion H; subst.
    inversion H0; subst;
      try solve_by_inverts 1.
    clear H7 H0 H IHn.
    rewrite subst_gen_plusn in H1.

    eapply multi_step.
    + apply ST_AppAbs. apply v_nat.
    + rewrite subst_gen_plusn. simpl.
      assert (H: step_normal_form_of (gen_plusn n (const k)) (const (n + k))).
      { split. exact H1. intros [t contra]; inversion contra. }
      clear H1.
      assert (H0: multi step (succ (const (n + k))) (const (S (n + k)))).
      { normalize. }
      apply succ_arg_normalizes in H.
      apply (multi_step_trans _ _ _ H H0).
Qed.

Lemma normal_form'_lift_plusn: forall n k,
  step'_normal_form_of (app' (lift (plusn n)) (const' k))
    (const' (map (fun '(n0, pc) => (n + n0, pc)) k)).
Proof.
  intros. induction n;
  split; try (intros [t contra]; inversion contra).
  - eapply multi_step; simpl.
    + apply ST_AppAbs'. apply v_nat'.
    + simpl. assert(Hk: (map (fun '(n0, pc0) => (n0, pc0)) k) = k).
      { induction k. reflexivity.
        simpl. f_equal.
        - destruct a. reflexivity.
        - exact IHk. }
      rewrite Hk. apply multi_refl.
  - unfold plusn in *.
    inversion IHn. clear H0.
    inversion H; subst.
    inversion H0; subst;
      try solve_by_inverts 1.
    clear H7 H0 H IHn.
    rewrite subst'_gen_plusn in H1.

    eapply multi_step.
    + apply ST_AppAbs'. apply v_nat'.
    + rewrite subst'_gen_plusn. simpl.
      assert (H: step'_normal_form_of (gen_plusn' n (const' k))
        (const' (map (fun '(n0, pc0) => ((n + n0), pc0)) k))).
      { split. exact H1. intros [t contra]; inversion contra. }
      clear H1.
      assert (H0: multi step' (succ' (const' (map (fun '(n0, pc0) => ((n + n0), pc0)) k)))
        (const' (map (fun '(n0, pc0) => (S (n + n0), pc0)) k))).
      { eapply multi_step.
        - apply ST_SuccConst'.
        - rewrite map_map_fst. apply multi_refl. }
      apply succ'_arg_normalizes in H.
      apply (multi_step'_trans _ _ _ H H0).
Qed.

(* Proving that the commutation diagram holds for
   any (+ n) function.
 *)

Theorem lift_plusn_correct: forall n spl cfg p r r',
  derive spl cfg = Some p ->
  step'_normal_form_of (app' (lift (plusn n)) (const' spl)) (const' r') ->
  step_normal_form_of (app (plusn n) (const p)) (const r) ->
  derive r' cfg = Some r.
Proof.
  intros n spl cfg p r r' Hd Hsnf' Hsnf.
  (* Showing that r = const (n + p) *)
  assert (Hr: const r = const (n + p)).
  { apply normal_forms_unique with (t1:= (app (plusn n) (const p))).
    - exact Hsnf.
    - apply normal_form_plusn. }
  injection Hr as Hr; subst.
  (* assert (Hf: n + p = (fun k => n + k) p). reflexivity. *)

  (* Showing that r' = const' (map (fun '(n0, pc) => (n + n0, pc)) spl) *)
  assert (Hr': const' r' = const' (map (fun '(n0, pc) => (n + n0, pc)) spl)).
  { apply normal_forms'_unique with (t1':= (app' (lift (plusn n)) (const' spl))).
    - exact Hsnf'.
    - apply normal_form'_lift_plusn. }
  injection Hr' as Hr'; subst.

  apply mapping_not_change_deriving.
  exact Hd.
Qed.

Require Import Norm Lifted_Norm LR.

(* LR examples *)

Example LR_plusone: forall cfg, LR cfg (Arrow Nat Nat) plusone (lift plusone).
Proof.
  intros. unfold plusone, LR;
  split; [|split]; simpl; eauto.
  intros arg arg' [Hty [Hty' [r [r' [ [Hms _] [ [Hms' _] Hd] ] ] ] ] ].
  split; [eauto|split]; eauto.
  eexists; eexists.
  split; [|split].
  - split; [|intros [x contra]; inversion contra].
    eapply multi_step_trans.
      eapply multistep_App2; eauto.
      normalize.
  - split; [|intros [x contra]; inversion contra].
    eapply multi_step'_trans.
      eapply multistep'_App2'; eauto.
      normalize.
  - eapply mapping_not_change_deriving. assumption.
Qed.

Example LR_plustwo: forall cfg, LR cfg (Arrow Nat Nat) plustwo (lift plustwo).
Proof.
  intros. unfold plustwo, LR;
  split; [|split]; simpl; eauto.
  intros arg arg' [Hty [Hty' [r [r' [ [Hms _] [ [Hms' _] Hd] ] ] ] ] ].
  split; [eauto|split]; eauto.
  eexists; eexists.
  split; [|split].
  - split; [|intros [x contra]; inversion contra].
    eapply multi_step_trans.
      eapply multistep_App2; eauto.
      eapply multi_step.
      auto. simpl. eapply multi_step.
      auto. eapply multi_step.
      auto. apply multi_refl.
  - split; [|intros [x contra]; inversion contra].
    eapply multi_step'_trans.
      eapply multistep'_App2'; eauto.
      eapply multi_step.
      auto. simpl. eapply multi_step.
      auto. eapply multi_step.
      auto. apply multi_refl.
  - eapply mapping_not_change_deriving.
    eapply mapping_not_change_deriving.
    assumption.
Qed.

Example LR_plusn: forall n cfg, LR cfg (Arrow Nat Nat) (plusn n) (lift (plusn n)).
Proof.
  intros. unfold LR.
  split; [|split;
  [| intros arg arg' [Hty [Hty' [r [r' [Hsnf [Hsnf' Hd] ] ] ] ] ];
     split; [|split; [|eexists;eexists;split; [|split] ] ]
  ] ].
  - unfold plusn. constructor.
    induction n; simpl; auto.
  - unfold plusn. simpl. constructor.
    induction n; simpl; auto.
  - unfold plusn. econstructor; eauto.
    induction n; simpl; auto.
    constructor. constructor.
    inversion IHn; subst. auto.
  - unfold plusn. simpl.
    econstructor; eauto.
    induction n; simpl; auto.
    constructor; constructor.
    inversion IHn; subst. auto.
  - assert (Hms: multi step (app (plusn n) arg) (app (plusn n) (const r))).
    { eapply multistep_App2.
      induction n; unfold plusn; auto.
      destruct Hsnf. assumption. }
    pose proof (normal_form_plusn n r) as [Hms0 _].
    pose proof (multi_step_trans _ _ _ Hms Hms0).
    split; [|intros [x contra]; inversion contra].
    eassumption.
  - assert (Hms': multi step' (app' (lift (plusn n)) arg') (app' (lift (plusn n)) (const' r'))).
    { eapply multistep'_App2'.
      induction n; unfold plusn; simpl; auto.
      destruct Hsnf'. assumption. }
    pose proof (normal_form'_lift_plusn n r') as [Hms0' _].
    pose proof (multi_step'_trans _ _ _ Hms' Hms0').
    split; [|intros [x contra]; inversion contra].
    eassumption.
  - apply mapping_not_change_deriving. assumption.
Qed.
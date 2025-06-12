Require Import STLC_SuccNat.
Require Import String List Maps.
Import ListNotations.
Require Import Lifted_STLC_SuccNat.

(* Presence Condition Evaluation Examples *)
Example pc: pc_eval ["A"; "B"] [[ (FEATURE "A") /\ (FEATURE "B") ]] = true.
Proof. reflexivity. Qed.

Example pc2: pc_eval [] [[ ~ FEATURE "C" ]] = true.
Proof. reflexivity. Qed.

Example pc3: pc_eval ["A"; "B"; "C"] [[ (FEATURE "A") /\ ~ (FEATURE "B") \/ (FEATURE "C") ]] = true.
Proof. reflexivity. Qed.

Example pc4: pc_eval ["A"] [[ TRUE /\ (FEATURE "A") ]] = true.
Proof. reflexivity. Qed.

Example pc5: pc_eval ["A"] [[ FALSE /\ (FEATURE "A") ]] = false.
Proof. reflexivity. Qed.

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

(*Automatic Lifting Examples*)
Example const1': lift (const 1) = const' [(1, [[TRUE]])].
Proof. simpl. reflexivity. Qed.

Example plusone': lift plusone = abs' "n" Nat' (succ' (var' "n")).
Proof. simpl. reflexivity. Qed.

(*Some SPLs examples*)
Definition x':= [
   (1, [[FEATURE "A"]]);
   (2, [[~ (FEATURE "A") /\ (FEATURE "B")]]);
   (3, [[~ (FEATURE "A") /\ ~ (FEATURE "B")]])
  ].

Definition y' := [
    (5, [[(FEATURE "A") /\ ~ (FEATURE "B")]]);
    (4, [[FEATURE "B"]]);
    (3, [[~(FEATURE "A") /\ ~(FEATURE "B")]])
  ].

Definition z' := [ (19, [[TRUE]]) ].

(*Disjointness Invariant Exapmles*)
Lemma disjointness_x': disjointness x'.
Proof.
  unfold disjointness.
  simpl. split.
  - intros t' pc' [].
    + injection H as []. rewrite <- H.
      unfold disjoint; intros cfg [].
      simpl in H0, H1.
      destruct in_dec; discriminate.
    + destruct H.
      * injection H as []. rewrite <- H.
        intros cfg []. simpl in H0, H1.
        destruct in_dec; discriminate.
      * destruct H.
  - split.
    + intros t' pc' [].
      * injection H as []. rewrite <- H.
        intros cfg []. simpl in H0, H1.
        destruct in_dec; destruct in_dec; discriminate.
      * destruct H.
    + split.
      * intros. destruct H.
      * apply I.
Qed.

Ltac solve_by_inverts n :=
	match goal with | H : ?T  |-  _  =>
	match type of T with Prop =>
		solve [ inversion H;
		match n with S (S (?n')) =>
			subst; solve_by_inverts (S n') end ]
	end end.

(* plusone(x'|p) = (plusone'(x'))|p *)
Example comm_plusone_x': forall (cfg:FeatureConfig) (x n:nat) (n':nat'),
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

  (* Case analisys on the feature configuration *)
  simpl; simpl in Hd.
  destruct in_dec.
  - injection Hd as Hd;
    subst; reflexivity.
  - destruct in_dec;
    injection Hd as Hd;
    subst; reflexivity.
Qed.

(* plusone(y'|p) = (plusone'(y'))|p *)
Example comm_plusone_y: forall (cfg:FeatureConfig) (y n: nat) (n':nat'),
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

  (* Case analisys on the feature configuration *)
  simpl; simpl in Hd.
  destruct in_dec; (*destruct in_dec as many times as there are features*)
  destruct in_dec;
    injection Hd as Hd;
    subst; reflexivity.
Qed.

(* plusone(z'|p) = (plusone'(z'))|p *)
Example comm_plusone_z: forall (cfg:FeatureConfig) (z n: nat) (n':nat'),
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
  step_normal_form_of (STLC_SuccNat.app plusone (const p)) (const r) ->
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
  inversion H0; subst.
  inversion H; subst;
    try solve_by_inverts 1;
    clear H H0.

  inversion H1; subst.
    2:{ inversion H. }
  apply mapping_not_change_deriving.
  assumption.
Qed.





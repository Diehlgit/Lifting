From Stdlib Require Import List String.
Import List.ListNotations.
Require Import Presence_Conditions.

Open Scope list_scope.
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
  exists i, mstep i (app plusone (const 0)) = Some (const 1).
Proof.
  exists 2.
  simpl. reflexivity.
Qed.

Example plustwo_3_is_5:
 exists i, mstep i (app plustwo (const 3)) = Some (const 5).
Proof.
  exists 3.
  simpl. reflexivity.
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


(* plusone(x'|p) = (plusone'(x'))|p *)
Example comm_plusone_x': forall (i:nat) (conf:feat_config) (x n:nat) (n':nat'),
  (derive x' conf ) = Some x ->
  mstep i (app plusone (const x)) = Some (const n) ->
  mstep' i (app' (lift plusone) (const' x')) = Some (const' n') ->
  (derive n' conf) = Some n.
Proof.
  intros i conf x n n' Hd Hmstep Hmstep'.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i.
  discriminate.
  simpl in Hmstep.
  rewrite mstep'_Si in Hmstep'.
  unfold step' in Hmstep'.
  remember (map (fun '(n, pc0) => (S n, pc0)) x') as x1'.
  destruct i;
    simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    apply mapping_not_change_deriving;
    assumption.
Qed.

(* plusone(y'|p) = (plusone'(y'))|p *)
Example comm_plusone_y: forall (i:nat) (conf:feat_config) (y n: nat) (n':nat'),
  (derive y' conf) = Some y ->
  mstep i (app plusone (const y)) = Some (const n) ->
  mstep' i (app' (lift plusone) (const' y')) = Some (const' n') ->
  (derive n' conf) = Some n.
Proof.
  intros i conf y n n' Hd Hmstep Hmstep'.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i.
  discriminate.
  simpl in Hmstep.
  rewrite mstep'_Si in Hmstep'.
  unfold step' in Hmstep'.
  remember (map (fun '(n, pc0) => (S n, pc0)) y') as y1'.
  destruct i;
    simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    apply mapping_not_change_deriving;
    assumption.
Qed.

(* plusone(z'|p) = (plusone'(z'))|p *)
Example comm_plusone_z: forall (i:nat) (conf:feat_config) (z n: nat) (n':nat'),
  (derive z' conf) = Some z ->
  mstep i (app plusone (const z)) = Some (const n) ->
  mstep' i (app' (lift plusone) (const' z')) = Some (const' n') ->
  (derive n' conf) = Some n.
Proof.
  intros i conf z n n' Hd Hmstep Hmstep'.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i.
  discriminate.
  simpl in Hmstep.
  rewrite mstep'_Si in Hmstep'.
  unfold step' in Hmstep'.
  remember (map (fun '(n, pc0) => (S n, pc0)) z') as z1'.
  destruct i;
    simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    apply mapping_not_change_deriving;
    assumption.
Qed.

Example lift_plusone_correct: forall i spl conf p r r',
  derive spl conf = Some p ->
  mstep' i (app' (lift plusone) (const' spl)) = Some (const' r') ->
  mstep i (app plusone (const p)) = Some (const r) ->
  derive r' conf = Some r.
Proof.
  intros i spl conf p r r' Hd Hmstep' Hmstep.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  remember (map (fun '(n, pc0) => (S n, pc0)) spl) as spl'.
  destruct i;
    simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    apply mapping_not_change_deriving;
    assumption.
Qed.

Example lift_plustwo_correct: forall i spl conf p r r',
  derive spl conf = Some p ->
  mstep' i (app' (lift plustwo) (const' spl)) = Some (const' r') ->
  mstep i (app plustwo (const p)) = Some (const r) ->
  derive r' conf = Some r.
Proof.
  intros i spl conf p r r' Hd Hmstep' Hmstep.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  remember (map (fun '(n, pc0) => (S n, pc0)) spl) as spl'.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  remember (map (fun '(n, pc0) => (S n, pc0)) spl') as spl''.
  destruct i;
    simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    repeat apply mapping_not_change_deriving;
    assumption.
Qed.

(* Trying to work with a general plusn function *)

Definition plusn (n:nat): tm := abs "n" Nat (add (const n) (var "n")).

(* Proving that the commutativity diagram holds for
   any (+ n) function.
 *)

Theorem lift_plusn_correct: forall i n spl conf p r r',
  derive spl conf = Some p ->
  mstep' i (app' (lift (plusn n)) (const' spl)) = Some (const' r') ->
  mstep i (app (plusn n) (const p)) = Some (const r) ->
  derive r' conf = Some r.
Proof.
  intros i n spl conf p r r' Hd Hmstep' Hmstep.
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  destruct i; [
    discriminate |
    simpl in Hmstep, Hmstep'].
  assert ((map (fun '(v2, pc2) => (n + v2, pc_And pc_True pc2)) spl ++ []) =
          (app_binop Nat.add [(n, pc_True)] spl))
          by reflexivity.
  rewrite H in Hmstep'.
  remember (app_binop Nat.add [(n, pc_True)] spl) as spl'.
  destruct i;
    (simpl in Hmstep;
    simpl in Hmstep';
    injection Hmstep as Hmstep;
    injection Hmstep' as Hmstep';
    subst;
    apply binop_not_change_deriving;
    [ auto | assumption ]).
Qed.

(* Extending the plusn function to "count lines"*)
From STLC Require Import Presence_Conditions_Notations
  Lifted_Notations Notations.

Definition lc_body :=
  <{ \"f" : NatList -> Nat,
     \"l" : NatList, 
       case '"l" of
       | nil => 0
       | "h" :: "t" => '"h" + ('"f" '"t")
  }>.

Definition line_count := (<{ `fixp lc_body` }>).

Example line_count_wt: has_type empty line_count <{{NatList -> Nat}}>.
Proof.
  repeat (econstructor; try reflexivity).
Qed.

Compute mstep 3 <{`line_count` nil}>.

Compute mstep 7 <{`line_count` [1]}>.

Compute mstep 11 <{`line_count` [1; 2]}>.

Compute mstep 15 <{`line_count` [1 ; 2; 2]}>.

Compute mstep 19 <{`line_count` [1; 2; 2; 4]}>.

Check (lift line_count).

Definition spl1 := cons' (const' [(1,<["A"]>);(0, <[~"A"]>)]) nil'.
Print spl1.
Compute mstep' 7 (app' (lift line_count) spl1).

Definition spl2 := cons' (const' [(1,<[T]>)]) (cons' (const' [(1,<["A"]>);(0, <[~"A"]>)]) nil').
Print spl2.
Compute mstep' 11 (app' (lift line_count) spl2).

Definition spl3 := cons' (const' [(1,<[T]>)]) (cons' (const' [(1,<["A"]>);(0, <[~"A"]>)]) (cons' (const' [(1,<[T]>)]) nil')).
Print spl3.
Compute mstep' 15 (app' (lift line_count) spl3).

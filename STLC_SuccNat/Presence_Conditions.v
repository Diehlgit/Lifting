From Stdlib Require Import String List.
Import List.ListNotations.

(* A Feature is represented by a string *)
Definition feature := string.

(*A Feature Configuration is a list of features *)
Definition feat_config := list feature.

(* A Presence Condition is a Boolean expression over features *)
Inductive pc : Type :=
  | pc_Feature : feature -> pc
  | pc_And     : pc -> pc -> pc
  | pc_Or      : pc -> pc -> pc
  | pc_Not     : pc -> pc
  | pc_True    : pc
  | pc_False   : pc.

(* Function that evaluates a Presence Condition given a Feature Configuration *)
Fixpoint pc_eval (cfg : feat_config) (pc : pc) : bool :=
  match pc with
  | pc_Feature f => if in_dec String.string_dec f cfg then true else false
  | pc_And p1 p2 => pc_eval cfg p1 && pc_eval cfg p2
  | pc_Or  p1 p2 => pc_eval cfg p1 || pc_eval cfg p2
  | pc_Not p1   => negb (pc_eval cfg p1)
  | pc_True => true
  | pc_False => false
  end.

(* A Nat Variational Value is a list of pairs of a
   base type (T) with their corresponding presence conditions. *)
Definition variational_value T : Type := list (T * pc).

(* deriving works by finding the first presence condition that
   is truthfull under evaluation given a configuration.
   This definition might have consequences in regards to the
   necessity of the Invariants needed in the article. *)
Fixpoint derive {T} (v' : variational_value T) (cfg : feat_config) : option T :=
  match v' with
  | [] => None
  | (v, pc) :: rest =>
    if pc_eval cfg pc then Some v
    else derive rest cfg
  end.

(* A binary operator like addition over variational natural values
   would need to operate over all combinations of naturals and
   presence conditions pairs. Much like vector product.
   For example:
      [(1,A);(0,~A)] + [(2,B);(3,~B)]
  ==> [(1+2,A/\B);(1+3,A/\~B);(0+2,~A/\B);(0+3,~A/\~B)]
  ==> [(3,A/\B);(4,A/\~B);(2,~A/\B);(3,~A/\~B)]*)

Fixpoint app_binop {T} (op : T -> T -> T)
  (v1' : variational_value T) (v2' : variational_value T) : (variational_value T) :=
  match v1' with
  | [] => []
  | (v1, pc1) :: rest => (map (fun '(v2, pc2) => ((op v1 v2), (pc_And pc1 pc2))) v2') ++
                         (app_binop op rest v2')
  end.

Compute app_binop Nat.add [(1,pc_True);(0,pc_False)]
                          [(2,pc_True);(3,pc_False)].

Compute app_binop Nat.add [(1,pc_True);(0,pc_False)] [].

Compute app_binop Nat.add [] [(2,pc_True);(3,pc_False)].

Lemma app_binop_distributive {T} : forall (op:T->T->T) (v1' v2':variational_value T) (v:T) (p:pc),
  app_binop op ((v, p) :: v1') v2' =
  (app_binop op [(v, p)] v2') ++ (app_binop op v1' v2').
Proof.
  intros. destruct v1'.
  - simpl. f_equal.
    rewrite app_nil_r.
    reflexivity.
  - destruct p0; simpl.
    f_equal. rewrite app_nil_r.
    reflexivity.
Qed.

Lemma derive_l {T} : forall (conf:feat_config) (v1' v2':variational_value T) (v:T),
  derive v1' conf = Some v ->
  derive (v1' ++ v2') conf = Some v.
Proof.
  intros. induction v1'; simpl.
  - inversion H.
  - destruct a, (pc_eval conf p) eqn:Eq;
      simpl in H; rewrite Eq in H.
    + assumption.
    + apply IHv1', H.
Qed.

Lemma derive_binop_none {T} : forall (conf:feat_config) (op:T->T->T)
                              (v':variational_value T) (n:T) (p:pc),
  pc_eval conf p = false ->
  derive (app_binop op [(n, p)] v') conf = None.
Proof.
  intros. simpl.
  rewrite app_nil_r.
  induction v'.
  - reflexivity.
  - destruct a. simpl.
    rewrite H. simpl.
    auto.
Qed.

Lemma derive_r {T} : forall (conf:feat_config) (v1' v2':variational_value T) (r:option T),
  derive v1' conf = None ->
  derive v2' conf = r ->
  derive (v1' ++ v2') conf = r.
Proof.
  intros. induction v1'; simpl.
  - auto.
  - destruct a; simpl.
    simpl in H.
    destruct (pc_eval conf p).
    inversion H.
    apply IHv1'.
    assumption.
Qed.
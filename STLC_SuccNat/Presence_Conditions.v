Require Import String List.
Import ListNotations.

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

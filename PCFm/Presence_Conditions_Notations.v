Require Import String Presence_Conditions.

Print pc.

Declare Custom Entry pc.

Notation "<[ e ]>" := e (e custom pc at level 99).

Notation "( e )" := e
  (in custom pc at level 0, e custom pc at level 99).

Notation "x" := (pc_Feature x)
  (in custom pc at level 0, x constr at level 0).

(* Constants *)
Notation "'T'" := pc_True (in custom pc at level 0).
Notation "'F'" := pc_False (in custom pc at level 0).

(* Operators *)
Notation "t1 '/\' t2" := (pc_And t1 t2)
  (in custom pc at level 40, left associativity).

Notation "t1 '\/' t2" := (pc_Or t1 t2)
  (in custom pc at level 50, left associativity).

Notation "'~' t" := (pc_Not t)
  (in custom pc at level 30).

Open Scope string_scope.

Check <["A"]>.
Check <["A" /\ "B"]>.
Check <[~ "A" \/ T]>.
Check <[~T /\ (F \/ "A") \/ ~"A"]>.
Require Import String Lifted_PCFm List.
Import ListNotations.
Require Import Presence_Conditions_Notations.

Declare Custom Entry ty'.
Notation "'<{{ e }}>'" := e (e custom ty' at level 99).
Notation "T" := T (in custom ty' at level 0, T constr at level 0).
Notation "( T )" := T (in custom ty' at level 0, T custom ty' at level 99).
Notation "T1 -> T2" := (Arrow' T1 T2)
  (in custom ty' at level 50, right associativity,
   T1 custom ty', T2 custom ty' at level 50).
Notation "'Nat''" := Nat' (in custom ty' at level 0).
Notation "'NatList''" := NatList' (in custom ty' at level 0).

Check '<{{ Nat' }}>'. (* Nat' : ty' *)
Check '<{{ NatList' }}>'. (* NatList' : ty' *)
Check '<{{ Nat' -> Nat' }}>'. (* Arrow' Nat' Nat' : ty' *)
Check '<{{ Nat' -> Nat' -> NatList' }}>'. (* Arrow' Nat' (Arrow' Nat' NatList') : ty' *)
Check '<{{ (Nat' -> Nat') -> NatList' }}>'. (* Arrow' (Arrow' Nat' Nat') NatList' : ty' *)

Declare Custom Entry tm'.

Notation "'<{ e }>'" := e (e custom tm' at level 99).

Notation "( e )" := e
  (in custom tm' at level 0, e custom tm' at level 99).

Notation "` e `" := e
  (in custom tm' at level 0, e constr at level 99).

Notation "n" := (const' n)
  (in custom tm' at level 0, n constr at level 0).

Coercion var' : string >-> tm'.
Notation "' x" := (var' x)
  (in custom tm' at level 1, x constr at level 0).

Check '<{ [(42,<[T]>)] }>'.       (* const' [(42,pc_True)] : tm' *)
Check '<{ '"f" }>'.     (* var "f" : tm' *)
Check '<{ ('"f") }>'.   (* var "f" : tm' — constr escape still works *)
Check '<{ ([(42,<[T]>)]) }>'.     (* const 42 : tm' — constr escape still works *)

Notation "t1 t2" := (app' t1 t2)
  (in custom tm' at level 20, left associativity,
   t1 custom tm', t2 custom tm' at level 19).

Check '<{ '"f" '"x" }>'.
(* app' (var' "f") (var' "x") : tm' *)
Check '<{ '"f" '"x" '"y" }>'.
(* app' (app' (var' "f") (var' "x")) (var' "y") : tm' *)
Check '<{ '"f" ('"x" '"y") }>'.
(* app' (var' "f") (app' (var' "x") (var' "y")) : tm' *)
Check '<{ '"f" [(42,<["A"]>)] }>'.
(* app' (var' "f") (const'[(42,"A")] ) : tm' *)

Notation "\ x : T , t" := (abs' x T t)
  (in custom tm' at level 90, right associativity,
   x constr at level 0,
   T custom ty' at level 99,
   t custom tm' at level 99).

Check '<{ \"f" : Nat' , '"f" }>'. 
(* abs' "f" Nat' (var' "f") : tm' *)

Check '<{ \"f" : Nat' -> Nat' , '"f" [(42, <[~"A"]>)] }>'.
(* abs' "f" (Arrow' Nat' Nat') (app' (var' "f") (const' 42)) : tm' *)

Check '<{ \"f" : Nat' , \"x" : Nat' , '"f" '"x" }>'.
(* abs' "f" Nat' (abs' "x" Nat' (app' (var' "f") (var' "x"))) : tm' *)

Check '<{ (\"f" : Nat' , '"f") [(42, <[~"A"]>)] }>'.
(* app' (abs' "f" Nat' (var' "f")) (const' [(42,~"A")]) : tm' *)

Notation "'s' t" := (succ' t)
  (in custom tm' at level 89,
   t custom tm' at level 89).

Check '<{ s [(42,<["A"]>)] }>'.
(* succ' (const' [(42,<["A"]>)]) : tm' *)
Check '<{ s '"f" }>'.
(* succ' (var' "f") : tm' *)
Check '<{ s s [(42,<["A"]>)] }>'.
(* succ' (succ' (const' 42)) : tm' *)
Check '<{ (\"f" : Nat' , s '"f") [(42,<["A"]>)] }>'.
(* app' (abs' "f" Nat' (succ' (var' "f"))) (const' [(42,<["A"]>)]) : tm' *)

Notation "t1 + t2" := (add' t1 t2)
  (in custom tm' at level 50, left associativity,
   t1 custom tm', t2 custom tm' at level 49).

Check '<{ [(42,<[T]>)] + [(1,<[T]>)] }>'.                     (* add (const 42) (const 1) : tm' *)
Check '<{ s [(1,<[T]>)] + [(2,<[T]>)] }>'.              (* add (succ (const 1)) (const 2) : tm' *)

Notation "'nil'" := nil' (in custom tm' at level 0).

Notation "t1 :: t2" := (cons' t1 t2)
  (in custom tm' at level 60, right associativity,
   t1 custom tm', t2 custom tm' at level 60).

Check '<{ nil }>'.
(* nil' : tm' *)
Check '<{ ([(1,<[T]>)] :: [(2,<[F]>)] :: nil) }>'.
(*Removed because creates conflicts with variational values notations. *)
(*Notation "[ t ]" := (cons' t nil')
  (in custom tm' at level 0, t custom tm' at level 60).
Notation "[ t1 ; t2 ; .. ; tn ]" := (cons' t1 (cons' t2 .. (cons' tn nil') ..))
  (in custom tm' at level 0,
   t1 custom tm' at level 60,
   t2 custom tm' at level 60,
   tn custom tm' at level 60).*)

(*Check <{ [1] }>.         (* cons (const 1) nil : tm' *)
Check <{ [1 ; 2] }>.     (* cons (const 1) (cons (const 2) nil) : tm' *)
Check <{ [1 ; 2 ; 3] }>. (* cons (const 1) (cons (const 2) (cons (const 3) nil)) : tm' *)
 *)

Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' h :: t '=>' t3" := (case' t1 t2 h t t3)
  (in custom tm' at level 89,
   t1 custom tm' at level 99,
   t2 custom tm' at level 99,
   h constr at level 0,
   t constr at level 0,
   t3 custom tm' at level 99,
   format "'[hv' 'case'  t1  'of' '//' '|'  'nil'  '=>'  t2 '//' '|'  h  '::'  t  '=>'  t3 ']'").

Check '<{ case nil of | nil => [(0,<[T]>)] | "h" :: "t" => s '"h" }>'.

Check '<{ case ([(1,<[T]>)] :: [(2,<[F]>)] :: nil) of
          | nil => [(0,<[T]>)]
          | "h" :: "t" => '"h" + '"t" }>'.
(* case (cons (const 1) (cons (const 2) nil)) (const 0) "h" "t" (add (var "h") (var "t")) : tm' *)


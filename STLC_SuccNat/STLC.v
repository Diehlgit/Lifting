Require Import Maps.

Variables var tm ty : Type.

Class STLC_Syntax := {
  ty_arrow : ty -> ty -> ty;
  tm_var : string -> tm;
  tm_abs : string -> ty -> tm -> tm;
  tm_app : tm -> tm -> tm;
}.

Definition context := partial_map ty.

Class STLC_Typing {Syntax_inst : STLC_Syntax} := {
  has_type : context -> tm -> ty -> Prop;

  (* Axioms defining the typing rules *)
  ax_t_var : forall Gamma x T,
    Gamma x = Some T ->
    has_type Gamma (tm_var x) T;

  ax_t_abs : forall Gamma x T1 T2 t,
    has_type (x |-> T2 ; Gamma) t T1 ->
      has_type Gamma (tm_abs x T2 t) (ty_arrow T2 T1);

  ax_t_app : forall Gamma T1 T2 t1 t2,
    has_type Gamma t1 (ty_arrow T2 T1) ->
    has_type Gamma t2 T2 ->
      has_type Gamma (tm_app t1 t2) T1;
}.

Class STLC_Ops {Syntax_inst : STLC_Syntax} := {
  value : tm -> Prop;
  subst : string -> tm -> tm -> tm;
  step : tm -> tm -> Prop;

  (* Axioms defining what a value is *)
  ax_v_abs : forall x T t, value (tm_abs x T t);

  (* Axioms defining the step relation *)
  ax_st_app1 : forall t1 t1' t2,
    step t1 t1' -> step (tm_app t1 t2) (tm_app t1' t2);
  ax_st_app2 : forall v t2 t2',
    value v -> step t2 t2' -> step (tm_app v t2) (tm_app v t2');
  ax_st_appabs : forall x T t v,
    value v -> step (tm_app (tm_abs x T t) v) (subst x v t);
}.

(* STLC SUCC NAT DEFINITIONS *)
Class STLC_SuccNat_Syntax `{STLC_Syntax} := {
  ty_nat : ty;
  tm_const : nat -> tm;
  tm_succ : tm -> tm
}.

Class STLC_SuccNat_Ops `{STLC_Ops} {Syntax_inst : STLC_SuccNat_Syntax} := {
  (* Axioms defining what a value is *)
  ax_v_nat : forall n, value (tm_const n);

  (* Axioms defining the step relation *)
  ax_st_succ : forall t1 t1',
    step t1 t1' -> step (tm_succ t1) (tm_succ t1');
  ax_st_succconst : forall n,
    step (tm_succ (tm_const n)) (tm_const (S n))
}.

Class STLC_SuccNat_Typing `{STLC_Typing} {Syntax_inst : STLC_SuccNat_Syntax} := {
  (* Axioms deinfing the typing rules *)
    ax_t_nat : forall Gamma n,
    has_type Gamma (tm_const n) ty_nat;

  ax_t_succ : forall Gamma t,
    has_type Gamma t ty_nat ->
    has_type Gamma (tm_succ t) ty_nat;
}.

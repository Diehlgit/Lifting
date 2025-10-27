Require Import String List Maps.
Import ListNotations.
Require Import Lifted_STLC_SuccNat.
Require Import STLC_SuccNat.


Definition env := list (string * tm).
Definition env' := list (string * tm').

Definition tass := list (string * ty).
Definition tass' := list (string * ty').


Fixpoint msubst (ss:env) (t:tm) : tm :=
  match ss with
  | nil => t
  | ((x,s)::ss') => msubst ss' (subst x s t)
  end.

Fixpoint msubst' (ss:env') (t':tm') : tm' :=
  match ss with
  | nil => t'
  | ((x,s)::ss') => msubst' ss' (subst' x s t')
  end.


Fixpoint mupdate (Gamma:context) (xts:tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.

Fixpoint mupdate' (Gamma':context') (xts:tass') :=
  match xts with
  | nil => Gamma'
  | ((x,v)::xts') => update (mupdate' Gamma' xts') x v
  end.


Fixpoint lookup {X} (k:string) (l:list(string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if eqb j k then Some x else lookup k l'
  end.

Lemma mupdate_lookup : forall (c:tass) (x:string),
  lookup x c = (mupdate empty c) x.
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mupdate, update, t_update. destruct (eqb s x);
 auto.
Qed.

Lemma mupdate'_lookup : forall (c:tass') (x:string),
  lookup x c = (mupdate' empty c) x.
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mupdate', update, t_update. destruct (eqb s x);
 auto.
Qed.


Fixpoint drop {X} (n:string) (nxs:list (string * X))
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c; intros.
  - destruct (eqb_spec x x'); auto.
  - destruct a. simpl.
    destruct (eqb_spec s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_spec x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_spec s x'); auto.
      subst. rewrite eqb_sym. apply eqb_neq in n. rewrite n; auto.
Qed.

Lemma mupdate'_drop : forall (c: tass') Gamma' x x',
      mupdate' Gamma' (drop x c) x'
    = if String.eqb x x' then Gamma' x' else mupdate' Gamma' c x'.
Proof.
  induction c; intros.
  - destruct (eqb_spec x x'); auto.
  - destruct a. simpl.
    destruct (eqb_spec s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_spec x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_spec s x'); auto.
      subst. rewrite eqb_sym. apply eqb_neq in n. rewrite n; auto.
Qed.





Lemma msubst_abs: forall ss x T t,
  msubst ss (abs x T t) = (abs x T (msubst (drop x ss) t)).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (String.eqb s x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss (app t1 t2) = app (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. reflexivity.
Qed.

Lemma msubst_const : forall ss n,
  msubst ss (const n) = const n.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
    simpl. apply IHss.
Qed.

Lemma msubst_succ : forall ss t,
  msubst ss (succ t) = succ (msubst ss t).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
    simpl. apply IHss.
Qed.

Lemma msubst'_abs': forall ss x T' t',
  msubst' ss (abs' x T' t') = (abs' x T' (msubst' (drop x ss) t')).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (String.eqb s x); simpl; auto.
Qed.

Lemma msubst'_app' : forall ss t1' t2',
    msubst' ss (app' t1' t2') = app' (msubst' ss t1') (msubst' ss t2').
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. reflexivity.
Qed.

Lemma msubst'_const' : forall ss n,
  msubst' ss (const' n) = const' n.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
    simpl. apply IHss.
Qed.

Lemma msubst'_succ' : forall ss t',
  msubst' ss (succ' t') = succ' (msubst' ss t').
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
    simpl. apply IHss.
Qed.





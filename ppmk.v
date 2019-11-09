(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* To be PRed in mathcomp *)
Lemma unbump0S i : unbump 0 i.+1 = i. 
Proof. by rewrite /unbump lt0n /= subn1. Qed.


Inductive fsub_type : Set :=
 | FsubTvar (i : nat)
 | FsubTop
 | FsubProd (bounded : bool) (dom codom : fsub_type).

Fixpoint eq_fsubt (s t : fsub_type) {struct t} : bool :=
  match s, t with
  | FsubTvar i, FsubTvar j => i == j
  | FsubTop, FsubTop => true
  | FsubProd b s1 s2, FsubProd b' t1 t2 =>
     [&& (b == b'), (eq_fsubt s1 t1) & (eq_fsubt s2 t2) ]
  | _, _ => false
  end.

Lemma fsub_eqP : Equality.axiom eq_fsubt.
Proof.
elim=> [i||b s1 Hrec1 s2 Hrec2] [j||c t1 t2] //=; try by constructor.
  by apply: (iffP eqP) => [<- | [<-]].
apply: (iffP and3P).
  by case; move/eqP=> <-; move/(Hrec1 _)=> ->; move/(Hrec2 _)=> ->.
by case=> <- <- <-; split; [exact: eqxx | apply/(Hrec1 _) | apply/(Hrec2 _)].
Qed.

Definition fsub_eqMixin := Equality.Mixin fsub_eqP.
Canonical Structure fsub_eqType := EqType fsub_type fsub_eqMixin.

Section FsubTypeTheory.

Implicit Type (h : nat) (t : fsub_type).

Fixpoint lift h t {struct t} : fsub_type :=
  match t with
  | FsubTvar i => FsubTvar (bump h i)
  | FsubTop => FsubTop
  | FsubProd b t1 t2 => FsubProd b (lift h t1) (lift (b + h) t2)
  end.

Lemma lift_top h t : (lift h t == FsubTop) = (t == FsubTop).
Proof. by case: t. Qed.

Lemma liftC h1 h2 t :
  lift h1 (lift h2 t) = lift (bump h1 h2) (lift (unbump h2 h1) t).
Proof.
elim: t h1 h2 => //= [i|b t1 Hrec1 t2 Hrec2] h1 h2; first by rewrite -bumpC.
by rewrite Hrec1 -!bump_addl Hrec2 unbump_addl.
Qed.

Fixpoint wf_type h t {struct t} : bool :=
  match t with
  | FsubTvar i => i < h
  | FsubTop => true
  | FsubProd b t1 t2 => wf_type h t1 && wf_type (b + h) t2
  end.

Lemma wf_lift h1 h2 t : wf_type h1 (lift h2 t) = wf_type (unbump h2 h1) t.
Proof.
elim: t h1 h2 => //= [i|b t1 Hrec1 t2 Hrec2] h1 h2.
  by rewrite !ltnNge leq_bump.
by rewrite Hrec1 Hrec2 unbump_addl.
Qed.

Lemma wf_lift0 h t : wf_type (S h) (lift 0 t) = wf_type h t.
Proof. by rewrite wf_lift unbump0S. Qed.

End FsubTypeTheory.

Definition type_env := seq fsub_eqType.

Section TypeEnvTheory.

Implicit Type (h i : nat) (s t : fsub_type) (e : type_env).

Fixpoint lookup i e {struct e} : fsub_type :=
  if e is cons t e' then lift 0 (if i is S i' then lookup i' e' else t)
  else FsubTop.

Fixpoint env_insert t0 h e {struct h} : type_env :=
  match h, e with
  | S h', cons t e' => cons (lift h' t) (env_insert t0 h' e')
  | _, _ => cons t0 e
  end.


Lemma size_env_insert t0 h e : size (env_insert t0 h e) = S (size e).
Proof. by elim: h e=> //= [h ih] [|t e] //=; congr S. Qed.

Lemma lookup_env_insert t0 h e i : h <= size e ->
  lookup (bump h i) (env_insert t0 h e) = lift h (lookup i e).
Proof.
by elim: h e i=> [|h ih] [|t e] [|i] //= ?; rewrite ?bumpS liftC // ih ?unbump0S. 
Qed.

Fixpoint wf_env e : bool :=
  if e is cons t e' then wf_type (size e') t && wf_env e' else true.

Lemma wf_env_adds e t : wf_env (cons t e) = wf_type (size e) t && wf_env e.
Proof. by []. Qed.

Lemma wf_lookup e i : wf_env e -> wf_type (size e) (lookup i e).
Proof.
elim: e i=> // t e Hrec i /=; move/andP=> [Ht He].
rewrite wf_lift0; case: i => //= i; exact: Hrec.
Qed.

Lemma env_insert_adds t0 h e t :
  env_insert t0 (S h) (cons t e) = cons (lift h t) (env_insert t0 h e).
Proof. by []. Qed.

Lemma wf_env_insert t0 h e : h <= size e ->
  wf_env (env_insert t0 h e) = wf_type (size e - h) t0 && wf_env e.
Proof.
elim: h e=> [|h Hrec] [|t e] //= Hh.
by rewrite size_env_insert wf_lift Hrec // /unbump andbCA Hh subn1.
Qed.

Fixpoint subt e s t n {struct n} : bool :=
  if n is S n' then
     (t == FsubTop)
  || match s, t with
     | FsubTvar i, _ => (s == t) || subt e (lookup i e) t n'
     | FsubProd b s1 s2, FsubProd b' t1 t2 =>
       [&& (b == b') , (subt e t1 s1 n') & (subt (ncons b t1 e) s2 t2 n') ]
     | _, _ => false
    end
  else false.

Lemma subt_addr e s t m n : subt e s t m -> subt e s t (m + n).
Proof.
elim: m => //= [m Hrec] in e s t |- *; case: eqP => // _.
case: s => //= [i|b s1 s2]; rewrite ?plusE; first by case/orP=> Ht; apply/orP; auto.
by case: t => // c t1 t2; case/and3P; move/eqP=> <- {c} *; rewrite eqxx !Hrec.
Qed.

Lemma subt_addl e s t m n : subt e s t m -> subt e s t (n + m).
Proof. rewrite addnC; exact: subt_addr. Qed.

Definition sub_ftype e t1 t2 := exists n, subt e t1 t2 n.

Lemma fsubtI e s t n : subt e s t n -> sub_ftype e s t.
Proof. by exists n. Qed.

Lemma sub_ftype_refl e t : sub_ftype e t t.
Proof.
elim: t e => [i||b t1 Hrec1 t2 Hrec2] e; try by exists 1.
  by exists 1; rewrite /= eqxx.
move: {Hrec1}(Hrec1 e) {Hrec2}(Hrec2 (ncons b t1 e)) => [n1 Hn1] [n2 Hn2].
exists (S (n1 + n2)); rewrite /= eqxx /=; apply/andP.
split; [exact: subt_addr | exact: subt_addl].
Qed.

Lemma sub_ftype_insert t0 h e s t : h <= size e ->
  sub_ftype e s t -> sub_ftype (env_insert t0 h e) (lift h s) (lift h t).
Proof.
move=> Hh [n Hn]; exists n.
elim: n e s t h Hh Hn => //= n Hrec e s t h Hh; rewrite lift_top /=.
case: eqP => //= _; case: s => //= [i|b s1 s2].
  case: eqP => [<-|_] /= Ht; first by rewrite eqxx.
  by rewrite orbC lookup_env_insert // Hrec.
case: t => //= c t1 t2; case/and3P; move/eqP=> <- {c} Ht1 Hs2.
rewrite eqxx Hrec //=; case: b Hs2 => /=; last exact: Hrec.
rewrite -env_insert_adds; exact: Hrec.
Qed.

Definition elift e := iter (size e) (lift 0).

Lemma sub_ftype_weak e s t e' :
  sub_ftype e s t -> sub_ftype (cat e' e) (elift e' s) (elift e' t).
Proof.
by elim: e'=> //= [u e' Hrec]; move/Hrec; apply: (@sub_ftype_insert _ 0).
Qed.

Definition env_join e t e' : type_env := cat e' (cons t e).

Lemma lookup_env_join e t e' i :
  lookup i (env_join e t e') =
    if i == size e' then elift (rcons e' t) t else
    lookup i (env_join e FsubTop e').
Proof.
by elim: e' i => [|s e' Hrec] [|i] //=; rewrite Hrec (fun_if (lift 0)).
Qed.

Fixpoint tsize t : nat :=
  if t is FsubProd _ t1 t2 then S (tsize t1 + tsize t2) else 0.

Lemma tsize_lift h t : tsize (lift h t) = tsize t.
Proof. by elim: t h => //= *; congr S; congr addn. Qed.

Lemma sub_trans_narrow t :
   (forall e s u, sub_ftype e s t -> sub_ftype e t u -> sub_ftype e s u)
/\ (forall e s e' u v, sub_ftype e s t ->
    sub_ftype (env_join e t e') u v -> sub_ftype (env_join e s e') u v).
Proof.
elim: {t}(S (tsize t)) {-2}t (ltnSn (tsize t)) => //= r Hrec.
have Htrans: forall e s t u, tsize t <= r ->
    sub_ftype e s t -> sub_ftype e t u-> sub_ftype e s u.
- move=> e s t u Hr Hs [[|m] //=]; case: eqP => [-> | _]; first by exists 1.
  case: eqP => [<- | _] //= Ht; case: Hs => n; elim: n s => //= n Hrecn s Hs.
  case: eqP Hs Ht => [->|_] //; case: s => //= [i|b s1 s2].
    case/orP; first by move/eqP=> <-; exists (S m); rewrite /= Ht !orbT.
    by case/Hrecn {n Hrecn}=> n Ht _; exists (S n); rewrite /= Ht !orbT.
  case: t {Hrecn} Hr => //= [b' t1 t2] Hr; case/and3P; move/eqP=> <- {b'}.
  move/fsubtI=> Ht1; move/fsubtI {n} => Ht2.
  case: u => //= [b' u1 u2]; case/and3P; move/eqP=> <- {b'}.
  move/fsubtI=> Hu1; move/fsubtI {m} => Hu2.
  case: (Hrec t2) => [|Tt2 _]; first by apply: leq_trans Hr; rewrite ltnS leq_addl.
  case: {Hrec}(Hrec t1) => [|Tt1 Nt1].
    by apply: leq_trans Hr; rewrite ltnS leq_addr.
  case: {Tt2 Hu2}(Tt2 _ s2 _ _ Hu2) => [|n2 Hu2].
    by case: b Ht2 => //=; apply: (Nt1 e _ nil).
  move: {Tt1 Hu1 Ht1}(Tt1 _ _ _ Hu1 Ht1) {Ht2} => [n1 Ht1].
  by exists (S (n1 + n2)); rewrite /= eqxx subt_addr //= subt_addl.
move=> t; rewrite ltnS => Hr; split; eauto => e s e' u v Ht [n Hv].
elim: n e' u v Hv => //= n Hrecn e' u v.
case: eqP => [->|_]; first by exists 1.
case: eqP => [-> _| _ /=]; first exact: sub_ftype_refl.
case: u => // [i|b u1 u2].
  move/Hrecn {n Hrecn}; rewrite lookup_env_join; case Hi: (i == _);
    last by move=> [n Hv]; exists (S n); rewrite /= lookup_env_join Hi Hv !orbT.
  apply: {v}Htrans.
    by rewrite /elift; elim: (size _) => //= *; rewrite tsize_lift.
  move/(sub_ftype_weak (rcons e' s)): Ht => [n Ht].
  exists (S n); rewrite /= lookup_env_join Hi /env_join -cat_rcons orbA orbC.
  by move: Ht; rewrite /elift !size_rcons /= => ->.
case: v => //= [c v1 v2]; case/and3P; move/eqP=> <- {c}; move/Hrecn=> [n1 Hv1].
have De': forall t', ncons b v1 (env_join e t' e') = env_join e t' (ncons b v1 e').
  by case b.
rewrite De'; case/Hrecn {n Hrecn} => n2; rewrite -De' => Hv2.
by exists (S (n1 + n2)); rewrite /= eqxx subt_addr // subt_addl.
Qed.

Lemma sub_ftype_trans e s t u :
  sub_ftype e s t -> sub_ftype e t u-> sub_ftype e s u.
Proof. by case: (sub_trans_narrow t); auto. Qed.

Lemma sub_ftype_narrow e s t e' u v : sub_ftype e s t ->
  sub_ftype (env_join e t e') u v -> sub_ftype (env_join e s e') u v.
Proof. by case: (sub_trans_narrow t); auto. Qed.

End TypeEnvTheory.

Module NaturalFsubNotation.

Delimit Scope nfsub_scope with Fsub.

Reserved Notation "'Top'".
Reserved Notation "t1 '-->' t2" (at level 90).
Reserved Notation "'\A' x '<:' t1 , t2"
  (at level 92, x at level 0, t1 at level 90, right associativity).

Reserved Notation "'<>'" (at level 140, left associativity).
Reserved Notation "x '<:' t" (at level 95, t at level 92).
Reserved Notation "e ; x '<:' t" (at level 140, x at level 0, t at level 92).
Reserved Notation "x '<:>' y" (at level 140).

(* Well-formedness cum binding test *)
Reserved Notation "e '|-' t" (at level 150, t at level 92, no associativity).

(* Subtype relation *)
Reserved Notation "e '|-' s '<:' t" (at level 150, s, t at level 92).

(* Substitution cum lookup function *)
Reserved Notation "e '|-' s '~>' t" (at level 150, s, t at level 92).

(* Alpha conversion *)
Reserved Notation "'|-' s '<->' t" (at level 150, s, t at level 92).

End NaturalFsubNotation.

Section NaturalFsub.

Import NaturalFsubNotation.
Local Open Scope nfsub_scope.

Variables (name : Set) (gen_name : nat -> name).

Hypotheses (Hname : comparable name) (Hgen_name : injective gen_name).

Canonical Structure name_eqType := EqType name (comparableMixin Hname).

Inductive nfsub_type : Set :=
| NFsubTvar (x : name)
| NFsubTop
| NFsubArrow (t1 t2 : nfsub_type)
| NFsubAll (x : name) (t1 t2 : nfsub_type).

Bind Scope nfsub_scope with nfsub_type.
Arguments NFsubArrow (_ _)%nfsub_scope.
Arguments NFsubAll _ (_ _)%nfsub_scope.

Notation "/ x" := (NFsubTvar x) : nfsub_scope. (* for patterns *)
Coercion NFsubTvar : name >-> nfsub_type.      (* for terms *)

Notation "'Top'" := NFsubTop : nfsub_scope.

Notation "t1 '-->' t2" := (NFsubArrow t1 t2) : nfsub_scope.

Notation "'\A' x '<:' t1 , t2" := (NFsubAll x t1 t2) : nfsub_scope.

(* We could use the standard list type for environments, but this *)
(* make it more difficult to get good notations -- defeating the  *)
(* main purpose of this section, which displaying the technical   *)
(* results established above as clearly as possible.              *)
Inductive nfsub_env : Set :=
| NFsubNil
| NFsubDecl (e : nfsub_env) (x : name) (t : nfsub_type).

Bind Scope nfsub_scope with nfsub_env.
Arguments NFsubDecl _%nfsub_scope _ _%nfsub_scope.

Notation "'<>'" := NFsubNil (at level 140) : nfsub_scope.
Notation "e ; x '<:' t" := (NFsubDecl e x t) : nfsub_scope.
Notation "x '<:' t" := (<> ; x <: t) : nfsub_scope.
Notation "x '<:>' y" := (x <: /y; y <: /x) : nfsub_scope.

(* We also regard environments as substitutions. *)
(* Note that e |- x ~> t doubles as a lookup judgement,        *)
(* and that e |- x ~> x means x is free in e for well formed e *)
Inductive nfsub_subst : forall (e : nfsub_env) (s t : nfsub_type), Prop :=
| SUBST_Decl_Tvar : forall e x t,
  (e; x <: t |- x ~> t)
| SUBST_Skip_Tvar : forall e x y s t,
     x <> y ->
    (e |- /x ~> t) ->
  (e; y <: s |- x ~> t)
| SUBST_Empty_Tvar : forall x,
  (<> |- /x ~> x)
| SUBST_Top : forall e,
  (e |- Top ~> Top)
| SUBST_Arrow : forall e s1 s2 t1 t2,
     (e |- s1 ~> t1) ->
     (e |- s2 ~> t2) ->
  (e |- s1 --> s2 ~> t1 --> t2)
| SUBST_All : forall e (x : name) s1 s2 (y : name) t1 t2,
     (e |- x ~> y) ->
     (e |- s1 ~> t1) ->
     (e |- s2 ~> t2) ->
  (e |- \A x <: s1, s2 ~> \A y <: t1, t2)
where "e '|-' s '~>' t" := (nfsub_subst e s t) : nfsub_scope.

(* The e |- Top judgement means e is well-formed.              *)
(* The e |- x judgement means x is bound in a well-formed e.   *)
(* We impose the Barendregt convention on terms, because this  *)
(* is in keeping with the context hygiene condition, and       *)
(* because it allows for a simpler definition of alpha         *)
(* conversion below.                                           *)

Inductive nfsub_wf : forall (e : nfsub_env) (t : nfsub_type), Prop :=
| WF_Tvar : forall e x t,
    (e |- Top) ->
    (e |- /x ~> t) ->
     t <> x ->
  (e |- x)
| WF_Decl_Top : forall e x t,
    (e |- /x ~> x) ->
    (e |- t) ->
  (e; x <: t |- Top)
| WF_Empty_Top :
  (<> |- Top)
| WF_Arrow : forall e t1 t2,
    (e |- t1) ->
    (e |- t2) ->
  (e |- t1 --> t2)
| WF_All : forall e x t1 t2,
    (e |- t1) ->
    (e; x <: t1 |- t2) ->
  (e |- \A x <: t1, t2)
where "e '|-' t" := (nfsub_wf e t) : nfsub_scope.

(* Alpha-conversion is needed to meet the Barendregt *)
(* condition after variable lookup.                  *)
Inductive nfsub_alpha : forall s t : nfsub_type, Prop :=
| ALPHA_Top :
  (|- Top <-> Top)
| ALPHA_Tvar : forall x,
  (|- /x <-> x)
| ALPHA_Arrow : forall s1 s2 t1 t2,
    (|- s1 <-> t1) ->
    (|- s2 <-> t2) ->
  (|- s1 --> s2 <-> t1 --> t2)
| ALPHA_All : forall x s1 s2 y t1 t2 t2',
    (|- s1 <-> t1) ->
    (x <:> y |- t2 ~> t2') ->
    (|- s2 <-> t2') ->
  (|- \A x <: s1, s2 <-> \A y <: t1, t2)
where "'|-' s '<->' t" := (nfsub_alpha s t) : nfsub_scope.

(* The subtype rules, with well-formedness checks folded in. *)
(* We provide for simple alpha-conversion As with the WF judgement rules, we need to provide for    *)
(* alpha-conversion the All-bound variables.                 *)
Inductive nfsub_subtype : forall (e : nfsub_env) (s t : nfsub_type), Prop :=
| SA_Top : forall e s,
    (e |- s) -> (* WF *)
  (e |- s <: Top)
| SA_Refl_Tvar : forall e x,
    (e |- /x) -> (* WF *)
  (e |- x <: x)
| SA_Trans_Tvar : forall e x s s' t,
    (e |- /x ~> s) -> 
    (|- s <-> s') -> (* ALPHA *)
    (e |- s' <: t) ->
  (e |- x <: t)
| SA_Arrow : forall e s1 s2 t1 t2,
    (e |- t1 <: s1) ->
    (e |- s2 <: t2) ->
  (e |- s1 --> s2 <: t1 --> t2)
| SA_All : forall e x s1 s2 y t1 t2 t2',
    (e |- t1 <: s1) ->
    (e |- /y ~> y) ->         (* WF *)
    (x <:> y |- t2 ~> t2') -> (* ALPHA *)
    (e; x <: t1 |- s2 <: t2') ->
  (e |- \A x <: s1, s2 <: \A y <: t1, t2)
where "e '|-' s '<:' t" := (nfsub_subtype e s t) : nfsub_scope.

(* Deciding term equality. *)

Lemma compare_nfsub_type : comparable nfsub_type.
Proof. rewrite /comparable/decidable; decide equality; apply: Hname. Qed. 

Canonical Structure nfsub_eqType := EqType nfsub_type (comparableMixin compare_nfsub_type).

(* Computable equivalents of the subst and wf predicates. *)

(* Substitution is used in two ways in the the WF and SA rules: *)
(* for variable lookup and alpha-conversion; the general form   *)
(* will be used for type-checking, so we also give it, however  *)
(* its correctess depends on the WF predicate (in general, the  *)
(* SUBST judgement only defines a partial function).            *)

Fixpoint subst_var (e : nfsub_env) (x : name) {struct e} : nfsub_type :=
  if e is (e'; y <: t) then if x == y then t else subst_var e' x else x.

Lemma subst_varPx : forall e x t, reflect (e |- /x ~> t) (subst_var e x == t).
Proof.
move=> e x t; elim De: e => [|e' Hrec y s].
  apply: (iffP eqP); first by move=> /= <-; constructor.
  by rewrite -De; move Dy: {1}(/x) => y He; case: e y t / He Dy De.
rewrite -{1}De /=; case: (x =P y) => [Dx|Hxy].
  rewrite -{y}Dx in De; apply: (iffP eqP); first by rewrite De => ->; constructor.
  move Dy: (/x) => y He; case: e y t / He Dy De {Hrec} => // [_ _ _ _ [] // |].
  by move=> e z y _ t Hzy _ [->] [_ Dz _]; case Hzy.
apply: {Hrec}(iffP Hrec); first by rewrite {e}De; constructor.
move Dz: (/x) => z He; case: e z t / He De Dz => //.
  by move=> e _ _ [_ -> ->] [Dx]; case Hxy.
by move=> _ _ _ _ _ _ _ [<- //].
Qed.

Notation subst_varP := (subst_varPx _ _ _).

Fixpoint subst_type (e : nfsub_env) (t : nfsub_type) {struct t} : nfsub_type :=
  match t with
  | /x             => subst_var e x
  | Top            => Top
  | t1 --> t2      =>  subst_type e t1 --> subst_type e t2
  | \A x <: t1, t2 => \A x <: subst_type e t1, subst_type e t2
  end.

Definition swap_var (x y z : name) :=
  if z == x then y else if z == y then x else z.

Lemma swap_varC : forall x y, swap_var x y =1 swap_var y x.
Proof. by move=> x y z; rewrite /swap_var; do 2 case: eqP => // <-. Qed.

Lemma swap_varI : forall x y, cancel (swap_var x y) (swap_var x y).
Proof.
move=> x y z; rewrite /swap_var.
case Hzx: (z == x); first by rewrite (eqP Hzx) eqxx; case: eqP.
by case Hzy: (z == y); [rewrite (eqP Hzy) eqxx | rewrite Hzx Hzy].
Qed.

Lemma swap_swap_var : forall x1 y1 x2 y2 z,
  let s1 := swap_var x1 y1 in
  s1 (swap_var x2 y2 z) = swap_var (s1 x2) (s1 y2) (s1 z).
Proof.
move=> x1 y1 x2 y2 z s1; rewrite /swap_var -!(fun_if s1); congr s1.
by rewrite /s1 !(can_eq (swap_varI _ _)).
Qed.

Lemma subst_swap_var : forall x y z, subst_var (x <:> y) z = swap_var x y z.
Proof. by move=> x y z /=; rewrite -2!(fun_if NFsubTvar) swap_varC. Qed.

Fixpoint swap_type (x y : name) (t : nfsub_type) {struct t} : nfsub_type :=
  match t with
  | /z             => swap_var x y z
  | Top            => Top
  | t1 --> t2      => swap_type x y t1 --> swap_type x y t2
  | \A z <: t1, t2 => \A (swap_var x y z) <: swap_type x y t1, swap_type x y t2
  end.

Lemma swap_typeC : forall x y, swap_type x y =1 swap_type y x.
Proof.
by move=> x y; elim=> //= [z|t1 -> t2 ->|z t1 -> t2 ->] //; rewrite swap_varC.
Qed.

Lemma swap_typeI : forall x y, cancel (swap_type x y) (swap_type x y).
Proof.
by move=> x y; elim=> //= [z|t1 -> t2 ->|z t1 -> t2 ->] //; rewrite swap_varI.
Qed.

Lemma swap_typePx : forall x y s t,
  reflect (x <:> y |- s ~> t) (swap_type x y s == t).
Proof.
move=> x y s; elim Ds: s => [z||s1 Hrec1 s2 Hrec2|z s1 Hrec1 s2 Hrec2] t.
- rewrite /= -subst_swap_var; exact: subst_varP.
- by apply: (iffP eqP)=> [<-|Hs]; [constructor | rewrite -Ds in Hs; case: Hs Ds].
- apply: (iffP eqP)=> [<-|Hs] /=; last rewrite -Ds in Hs.
    constructor; [apply: Hrec1 | apply: Hrec2]; exact: eqxx.
  case: {s t}Hs Ds => // e u1 u2 t1 t2 Hu1 Hu2 [<- <-]{s1 s2} in Hrec1 Hrec2 *.
  by move/Hrec1: Hu1; move/Hrec2: Hu2; do 2 move/eqP <-.
apply: (iffP eqP)=> [<-|Hs] /=; last rewrite -Ds in Hs.
  constructor;
    [rewrite -subst_swap_var; apply: subst_varP | apply: Hrec1 | apply: Hrec2];
  exact: eqxx.
move: z s1 s2 Ds (subst_swap_var x y z) Hrec1 Hrec2 => z' s1' s2'.
case: {s t}Hs => // e z s1 s2 w t1 t2 Hw Hs1 Hs2 [<- <- <-]{z' s1' s2'}.
move/subst_varP: Hw; move/eqP=> -> [<-] Hrec1 Hrec2.
by move/Hrec1: Hs1;  move/Hrec2: Hs2; do 2 move/eqP <-.
Qed.

Notation swap_typeP := (swap_typePx _ _ _ _).

Lemma swap_swap_type : forall x1 y1 x2 y2 t,
  let s1 := swap_var x1 y1 in let s1t := swap_type x1 y1 in
  s1t (swap_type x2 y2 t) = swap_type (s1 x2) (s1 y2) (s1t t).
Proof.
move=> x1 y1 x2 y2; elim=> // [z|t1 Hrec1 t2 Hrec2|z t1 Hrec1 t2 Hrec2];
 by rewrite /= -?swap_swap_var // -Hrec1 -Hrec2.
Qed.

(* The computational version of the WF judgement.   *)
(* We separate the type and environment predicates, *)
(* as this makes them significantly easier to use.  *)

Fixpoint nwf_var (e : nfsub_env) (x : name) {struct e} : bool :=
  if e is e'; y <: _ then (x == y) || nwf_var e' x else false.

Definition nwf_bvar e x := negb (nwf_var e x).

Fixpoint nwf_type (e : nfsub_env) (t : nfsub_type) {struct t} : bool :=
  match t with
  | /x  => nwf_var e x
  | Top => true
  | t1 --> t2 => nwf_type e t1 && nwf_type e t2
  | \A x <: t1, t2 =>
    [&& (nwf_bvar e x) , (nwf_type e t1) & (nwf_type (e; x <: t1) t2) ]
  end.

Fixpoint nwf_env (e : nfsub_env) : bool :=
  if e is (e'; x <: t) then [&& (nwf_env e') , (nwf_bvar e' x) & (nwf_type e' t) ]
  else true.

Definition nwf_envtype e t := nwf_env e && nwf_type e t.

(* Reflection for the "freshness" judgement (e |- x ~> x). *)

Lemma subst_bvar : forall e x, nwf_bvar e x -> subst_var e x = x.
Proof.
by move=> e x; rewrite /nwf_bvar; elim: e => //= [e Hrec y t]; case: eqP.
Qed.

Lemma bvarPx : forall e x, nwf_env e -> reflect (e |- /x ~> x) (nwf_bvar e x).
Proof.
move=> e x He; apply: (iffP idP).
  by move/subst_bvar=> Dx; apply: subst_varP; rewrite Dx eqxx.
move/subst_varP; elim: e He => //= [e Hrec y t]; case/and3P=> He Hy Ht.
rewrite /nwf_bvar /=; case: (x =P y) Hy => [<-{y}|_] Hy; last exact: Hrec.
by move/eqP=> Dt; case/negP: Hy; rewrite Dt /= in Ht. 
Qed.

Notation bvarP := (bvarPx _).

(* Well-formedness of swaps. *)

Lemma bvar_swap_var : forall x y e z, nwf_var e z ->
  nwf_bvar e x -> nwf_bvar e y -> swap_var x y z = z.
Proof.
by move=> x y e z; rewrite /nwf_bvar /swap_var; do 2 case: eqP => [-> -> | _] //.
Qed.

Lemma wf_swap_var : forall e x y s t z, nwf_bvar e x ->  nwf_bvar e y ->
  nwf_var (e; x <: s) (swap_var x y z) = nwf_var (e; y <: t) z.
Proof.
move=> e x y s t z Hx Hy; rewrite swap_varC /swap_var /=.
case Hzy: (z == y); first by rewrite eqxx.
case Hzx: (z == x) Hzy; last by rewrite Hzx.
by rewrite eq_sym (eqP Hzx) (negbTE Hx) (negbTE Hy) => ->.
Qed.

Lemma wf_swap_type : forall e x y s t u, nwf_bvar e x ->  nwf_bvar e y ->
  nwf_type (e; x <: s) (swap_type x y u) = nwf_type (e; y <: t) u.
Proof.
move=> e x y s t u Hx Hy; have{Hx Hy} := wf_swap_var s t _ Hx Hy.
elim: u {s e}(e; x <: s) {t}(e; y <: t) => //= [|z] t1 Hrec1 t2 Hrec2 e e' Hz;
  rewrite (Hrec1 _ _ Hz) /nwf_bvar ?Hz; repeat congr andb; auto.
by apply: Hrec2 => w; rewrite /nwf_bvar /= (can_eq (swap_varI x y)) Hz.
Qed.

Lemma nwfPx : forall e t, reflect (e |- t) (nwf_envtype e t).
Proof.
have Hrl: forall e t, (e |- t) -> nwf_envtype e t.
  move=> e t; rewrite/nwf_envtype; elim: e t / => //=.
  - move=> e x t _; rewrite andbT => -> Hxt H; apply/idPn=> Hx; case: H.
    by symmetry; rewrite -(subst_bvar Hx); apply: eqP; apply/subst_varP.
  - move=> e x t Hx _; move/andP=> [He Ht]; rewrite He Ht /= !andbT.
    by apply/(bvarP He).
  - by move=> e t1 t2 _; move/andP=> [_ ->].
  by move=> e x t1 t2 _ _ _; rewrite -!andbA.
have Hrlt: forall t e, (e |- Top) -> nwf_type e t -> (e |- t).
  elim=> //= [x|t1 Hrec1 t2 Hrec2|x t1 Hrec1 t2 Hrec2] e He.
  - move=> Hx; apply: (@WF_Tvar _ _ (subst_var e x)) => //.
      apply: subst_varP; exact: eqxx.
    move/Hrl: He; move/andP=> [He _]; apply: (elimN eqP).
    by rewrite -(sameP (bvarP He) subst_varP) /nwf_bvar Hx.
  - by case/andP; constructor; auto.
  move/and3P=> [Hx Ht1 Ht2]; have Het1: (e |- t1) by auto.
  constructor=> //; apply: Hrec2 => //; constructor=> //.
  move/Hrl: He; move/andP=> [He _]; exact: (bvarP He).
move=> e t; apply: (iffP idP); first (case/andP=> He Ht; apply Hrlt); auto.
elim: e He {t Ht}=> [|e Hrec y t] /=; first by constructor.
move/and3P=> [He Hy Ht]; constructor; auto; exact: (bvarP He).
Qed.

Notation nwfP := (nwfPx _ _).

Lemma nwf_envPx : forall e, reflect (e |- Top) (nwf_env e).
Proof. move=> e; rewrite -[nwf_env e]andbT; exact: nwfP. Qed.

Notation nwf_envP := (nwf_envPx _).
 
Lemma nwf_typePx : forall e t, nwf_env e -> reflect (e |- t) (nwf_type e t).
Proof. move=> e t; rewrite -[nwf_type e t]andTb => <-; exact: nwfP. Qed.

Notation nwf_typeP := (nwf_typePx _).

Lemma nwf_varPx : forall e x, nwf_env e -> reflect (e |- /x) (nwf_var e x).
Proof. move=> e x; exact: nwf_typeP. Qed.

Notation nwf_varP := (nwf_varPx _).

(* Alpha-conversion *)

Fixpoint nalpha (s t : nfsub_type) {struct s} : bool :=
  match s, t with
  | /x, /y => x == y
  | Top, Top => true
  | s1 --> s2, t1 --> t2 => nalpha s1 t1 && nalpha s2 t2
  | \A x <: s1, s2, \A y <: t1, t2 => nalpha s1 t1 && nalpha s2 (swap_type x y t2)
  | _, _ => false
  end.

Lemma nalpha_swap : forall x y s t,
  nalpha (swap_type x y s) (swap_type x y t) = nalpha s t.
Proof.
move=> x y; elim=> [z||s1 Hrec1 s2 Hrec2|z s1 Hrec1 s2 Hrec2] [w||t1 t2|w t1 t2];
 by rewrite /= ?(can_eq (swap_varI x y)) // -?swap_swap_type Hrec1 Hrec2.
Qed.

Lemma nalpha_sym : forall s t, nalpha s t = nalpha t s.
Proof.
elim=> [x||s1 Hrec1 s2 Hrec2|x s1 Hrec1 s2 Hrec2] [y||t1 t2|y t1 t2] //=;
by rewrite 1?eq_sym // Hrec1 Hrec2 // swap_typeC -(nalpha_swap y x t2) swap_typeI.
Qed.

Lemma nalphaPx : forall s t, reflect (|- s <-> t) (nalpha s t).
Proof.
move=> s; elim Ds: s => [x||s1 Hs1 s2 Hs2|x s1 Hs1 s2 Hs2] t;
  case Dt: t => [y||t1 t2|y t1 t2]; rewrite -{1}Ds -{1}Dt /=;
  try by right=> Hst; case: s t / Hst Ds Dt.
- apply: (iffP eqP) => [Dx|Hst]; first by rewrite Ds Dt -Dx; constructor.
  by case: s t / Hst Ds Dt => // z -> [].
- by rewrite Ds Dt; left; constructor.
- case: Hs1 => Hst1; last (right=> Hst; case: Hst1).
    apply: {Hs2}(iffP (Hs2 _)) => Hst2; first by rewrite Ds Dt; constructor.
    by case: s t / Hst2 Ds Dt => // _ _ _ _ _ _ [_ <-] [_ <-] //.  
  by case: s t / Hst Ds Dt => // _ _ _ _ _ _ [<- _] [<- _] //.
case: Hs1 => Hst1; last (right=> Hst; case: Hst1).
  apply: {Hs2}(iffP (Hs2 _)) => Hst2.
    rewrite Ds Dt; apply: ALPHA_All Hst1 _ Hst2; apply: swap_typeP; exact: eqxx.
  case: s t / Hst2 Ds Dt => // z _ u2 w _ v2 v3 _ Hv3 Huv2 [<- _ <-] [<- _ <-].
  by move/(introT swap_typeP): Hv3; move/eqP=> ->.
by case: s t / Hst Ds Dt => // _ __ _ _ _ _ _ _ _ _ [_ <- _] [_ <- _] //.
Qed.

Notation nalphaP := (nalphaPx _ _).

Notation sub_set A B := (forall x, A x -> B x).

Definition sub_nenv e e' :=  sub_set (nwf_var e) (nwf_var e').

Lemma sub_base_env : forall e x s, sub_nenv e (e; x <: s).
Proof. by move=> e x s y /= ->; rewrite orbT. Qed.

Lemma sub_decl_env : forall e e' x s,
  sub_nenv e e' -> sub_nenv (e; x <: s) (e'; x <: s).
Proof. move=> e e' x s He y /=; case: eqP => //= _; exact: He. Qed.

Lemma sub_env_bvar :
  forall e e', sub_nenv e e' -> sub_set (nwf_bvar e') (nwf_bvar e).
Proof. by move=> e e' He z; move/negP=> Hz; apply/negP; eauto. Qed.

Lemma nwf_interpolate : forall e e' e'' t,
    sub_nenv e e' -> sub_nenv e' e'' -> 
  nwf_type e t -> nwf_type e'' t ->  nwf_type e' t.
Proof.
move=> e e' e'' t.
elim: t e e' e'' => //= [x|t1 Hrec1 t2 Hrec2|x t1 Hrec1 t2 Hrec2] e e' e'' He He'.
- by move/He.
- by move/andP=> [Het1 Het2]; move/andP=> [He''t1 He''t2]; apply/andP; eauto.
move/and3P=> [_ Het1 Het2]; move/and3P=> [Hx He''t1 He''t2].
apply/and3P; split; eauto; first exact: sub_env_bvar Hx.
apply: Hrec2 Het2 He''t2; exact: sub_decl_env.
Qed.

Lemma nwf_alpha : forall e e' t t', sub_nenv e e' -> nalpha t t' ->
  nwf_type e t -> nwf_type e' t' ->  nwf_type e t'.
Proof.
move=> e e' t t'; elim: t' t e e' => [y||t1 Hrec1 t2 Hrec2|y t1 Hrec1 t2 Hrec2];
  case=> [x||s1 s2|x s1 s2] e e' He //=; first by move/eqP=> ->.
- move/andP=> [Dt1 Dt2]; move/andP=> [Hs1 Hs2]; move/andP=> [Ht1 Ht2].
  by apply/andP; eauto.
move/andP=> [Dt1 Dt2]; move/and3P=> [Hx Hs1 Hs2].
case/and3P; move/(sub_env_bvar He)=> Hy Ht1 Ht2; apply/and3P; split; eauto.
rewrite -(swap_typeI x y s2) nalpha_swap in Dt2.
apply: Hrec2 (@sub_decl_env _ _ y t1 He) Dt2 _ Ht2.
by rewrite swap_typeC (wf_swap_type _ s1 _ Hy Hx).
Qed.

(* Translation to de Bruijn representation. We assume that the types and *)
(* environments are well-formed, since it's not possible to check the    *)
(* Barendregt condition on the compiled form.                            *)

Fixpoint compile_var (e : nfsub_env) (x : name) {struct e} : nat :=
  if e is e'; y <: _ then if x == y then 0 else S (compile_var e' x) else 0.

Fixpoint compile_type (e : nfsub_env) (t : nfsub_type) {struct t} : fsub_type :=
  match t with
  | /x => FsubTvar (compile_var e x)
  | Top => FsubTop
  | t1 --> t2 => FsubProd false (compile_type e t1) (compile_type e t2)
  | \A x <: t1, t2 =>
    FsubProd true (compile_type e t1) (compile_type (e; x <: t1) t2)
  end.

Fixpoint compile_env (e : nfsub_env) : type_env :=
  if e is e'; y <: t then cons (compile_type e' t) (compile_env e') else nil.

Lemma wf_compile_var : forall e x,
  nwf_var e x -> compile_var e x < size (compile_env e).
Proof. by move=> e x; elim: e => //= [e Hrec y t]; case: (x == y). Qed.

Lemma wf_compile_type : forall e t,
  nwf_type e t -> wf_type (size (compile_env e)) (compile_type e t).
Proof.
move=> e t; elim: t e => //= [x|t1 Hrec1 t2 Hrec2|x t1 Hrec1 t2 Hrec2] e.
- exact: wf_compile_var.
- by case/andP=> *; rewrite Hrec1 //; exact: Hrec2.
by case/and3P=> *; rewrite Hrec1 //; exact: (Hrec2 (_;_<:_)).
Qed.

Lemma wf_compile_env : forall e, nwf_env e -> wf_env (compile_env e).
Proof.
by elim=> //= [e Hrec x t]; case/and3P=>*; rewrite wf_compile_type // Hrec.
Qed.
  
Lemma wf_compile : forall e t, (e |- t) -> 
  let ce := compile_env e in wf_env ce /\ wf_type (size ce) (compile_type e t).
Proof.
move=> e t; move/nwfP; case/andP; move/wf_compile_env=> He.
by move/wf_compile_type; split.
Qed.

Lemma compile_swap_var : forall x y e s t, nwf_bvar e x -> nwf_bvar e y -> 
  forall z, compile_var (e; x <: s) (swap_var x y z) = compile_var (e; y <: t) z.
Proof.
move=> x y e s t Hx Hy z; rewrite swap_varC /swap_var {s t}/=.
case Hzy: (z == y); first by rewrite eqxx.
case Hzx: (z == x); last by rewrite Hzx.
move: Hzy Hx Hy; rewrite /nwf_bvar {Hzx}(eqP Hzx) eq_sym => -> {z}.
elim: e => //= [e Hrec z t]; case/norP; move/negbTE=> -> Hx.
by case/norP; move/negbTE=> -> Hy; rewrite Hrec.
Qed.

Lemma compile_swap_type : forall x y e s t, nwf_bvar e x -> nwf_bvar e y -> 
  forall u, compile_type (e; x <: s) (swap_type x y u) = compile_type (e; y <: t) u.
Proof.
move=> x y e s t Hx Hy u.
move: {s}(e; x <: s) {t}(e; y <: t) {Hx Hy}(compile_swap_var s t Hx Hy).
elim: u  => //= [z|t1 Hrec1 t2 Hrec2|z t1 Hrec1 t2 Hrec2] el er He.
- by rewrite He.
- by rewrite (Hrec1 _ _ He) (Hrec2 _ _ He).
rewrite (Hrec1 _ _ He); congr FsubProd; apply: Hrec2 => w /=.
by rewrite (can_eq (swap_varI x y)) He.
Qed.

Lemma alpha_compile : forall e s t, nwf_type e s -> nwf_type e t ->
  nalpha s t = (compile_type e s == compile_type e t).
Proof.
move=> e s t.
elim: s e t => [x||s1 Hrec1 s2 Hrec2|x s1 Hrec1 s2 Hrec2] e [y||t1 t2|y t1 t2] //=.
- elim: e => //= [e Hrec z _].
  case Hx: (x == z); last by case: (y =P z) Hx => // ->.
  by rewrite (eqP Hx) eq_sym; case: eqP.
- by move/andP=> [Hs1 Hs2]; move/andP=> [Ht1 Ht2]; rewrite (Hrec1 e) // (Hrec2 e).
move/and3P=> [Hx Hs1 Hs2]; move/and3P=> [Hy Ht1 Ht2].
rewrite (Hrec1 _ _ Hs1 Ht1) (Hrec2 _ _ Hs2) // ?(wf_swap_type _ t1) //.
congr (_ && (_ == _)); exact: compile_swap_type.
Qed.

Lemma alpha_compileP : forall e s t, (e |- s) -> (e |- t) ->
  reflect (|- s <-> t) (compile_type e s == compile_type e t).
Proof.
move=> e s t; move/nwfP; move/andP=> [_ Hs].
move/nwfP; move/andP=> [_ Ht].
rewrite -alpha_compile //; exact: nalphaP.
Qed.

Lemma lift_compile_type : forall e x s t, nwf_bvar e x -> nwf_type e t ->
  compile_type (e; x <: s) t = lift 0 (compile_type e t).
Proof.
move=> e x s t Hx; set e' := e; x <: s.
have: forall y, nwf_var e y -> compile_var e' y = bump 0 (compile_var e y).
  by move=> y /=; case: eqP => //= -> Hy; case/negP: Hx.
elim: t 0 e {x s Hx}e' => //= [x|t1 Hrec1 t2 Hrec2| x t1 Hrec1 t2 Hrec2] h e e' He.
- by move=> Hx; rewrite He.
- by move/andP=> [Ht1 Ht2]; rewrite (Hrec1 h e) // (Hrec2 h e).
move/and3P=> [Hx Ht1 Ht2]; congr FsubProd; first exact: Hrec1.
by apply: Hrec2 => //= y; case: eqP => //= _ Hy; rewrite add1n bumpS He.
Qed. 

Lemma wf_subst_var : forall e x, nwf_env e -> nwf_var e x ->
  exists2 e', sub_nenv e' e & nwf_type e' (subst_var e x).
Proof.
move=> e x; elim: e => //= [e Hrec y t]; move/and3P=> [He _ Ht].
case: eqP => [<-{y} | _]; first by exists e; first exact: sub_base_env.
move/(Hrec He)=> [e' He' Hx]; exists e'; last done.
move=> z; move/He'; exact: sub_base_env.
Qed.

Lemma lookup_compile : forall e x t,
    nwf_env e -> nwf_var e x -> nalpha (subst_var e x) t -> nwf_type e t ->
  lookup (compile_var e x) (compile_env e) = compile_type e t. 
Proof.
move=> e x t; elim: e => //= [e Hrec y s]; move/and3P=> [He Hy Hs].
case: eqP Hy => //= [<-{y} | _] Hy Hx Dt Ht'.
  have Ht: nwf_type e t by apply: nwf_alpha Dt Hs Ht'; exact: sub_base_env.
  by rewrite lift_compile_type //; congr lift; apply: eqP; rewrite -alpha_compile.
suff Ht: nwf_type e t by rewrite lift_compile_type ?Hrec.
move: (wf_subst_var He Hx) => [e' He' He'x].
apply: (nwf_interpolate He') (Ht'); first exact: sub_base_env.
apply: nwf_alpha Dt He'x Ht' => z; move/He'; exact: sub_base_env.
Qed.

Definition sub_compile_type e s t :=
  sub_ftype (compile_env e) (compile_type e s) (compile_type e t).

Lemma subtype_wf_compile : forall e s t,
  (e |- s <: t) -> and3 (e |- s) (e |- t) (sub_compile_type e s t).
Proof.
move=> e s t; rewrite /sub_compile_type; elim: e s t /.
- move=> e s He; split=> //; last by exists 1.
  by apply/nwf_envP; move/nwfP: He; case/andP.
- by move=> e x; split=> //; exists 1; rewrite /= eqxx.
- move=> e x s t t'; move/(appP subst_varP eqP)=> <- {s}.
  move/nalphaP=> Dt _ [Het Het' [n Hn]].
  move: (appP nwfP andP Het) => [He Ht].
  have Hx: nwf_var e x.
    apply/idPn=> /= Hx; case/negP: (Hx) {n Hn}.
    move: Dt Ht {Het}; rewrite (appP subst_varP eqP (bvarP He Hx)).
    by case: t => //= y; move/eqP=> <-.
    split=> //; first by apply: (appP andP nwfP); split.
  by exists (S n); rewrite /= (lookup_compile He Hx Dt Ht) Hn !orbT.
- move=> e s1 s2 t1 t2 _ [Ht1 Hs1 [n1 Hn1]] _ [Hs2 Ht2 [n2 Hn2]].
  split; try by constructor.
  exists (S (n1 + n2)) => /=; apply/andP.
  split; [exact: subt_addr | exact: subt_addl].
move=> e x s1 s2 y t1 t2 t2' _ [Het1 Hes1 [n1 Hn1]].
move: (appP nwfP andP Het1) => [He Ht1]; move/(introT (bvarP He))=> Hy.
move: (appP nwfP andP Hes1) => [_ Hs1].
move/(appP swap_typeP eqP)=> <-{t2'} _ [Hs2 Ht2' [n2 Hn2]].
have Hx: nwf_bvar e x by case (appP nwfP andP Hs2); case/and3P.
split; try (constructor; auto; apply: nwfP; rewrite /nwf_envtype).
- rewrite -(wf_swap_type s1 _ s2 Hy Hx) (wf_swap_type _ t1) //=.
  by rewrite He Hx Hs1 /=; case: (appP nwfP andP Hs2).
- rewrite -(wf_swap_type t1 _ t2 Hx Hy) /= He Hy Ht1.
  by case (appP nwfP andP Ht2').
exists (S (n1 + n2)) => /=; apply/andP; split; first exact: subt_addr.
apply: subt_addl; rewrite -(compile_swap_type t1 _ Hx Hy) /=.
by rewrite -(compile_swap_type s1 _ Hy Hx) (compile_swap_type _ t1).
Qed.

Fixpoint nenv_size (e : nfsub_env) : nat :=
  if e is (e'; _ <: _) then S (nenv_size e') else 0.

Fixpoint fresh_below (e : nfsub_env) (i : nat) {struct i} : name :=
  if nwf_bvar e (gen_name i) then gen_name i else
  if i is S i' then fresh_below e i' else gen_name 0.

Definition gen_fresh e := fresh_below e (nenv_size e).

Lemma fresh_belowE e i :
  fresh_below e i = 
  if nwf_bvar e (gen_name i) then gen_name i else
  if i is S i' then fresh_below e i' else gen_name 0.
Proof. by case: i. Qed.

Lemma iota_pos x n : iota x n.+1 = rcons (iota x n) (n + x).
Proof. by elim: n x  => //= n IH acc; rewrite IH addnS addSn. Qed.

Lemma bvar_fresh : forall e, nwf_bvar e (gen_fresh e).
Proof.
pose fix a (e : nfsub_env) : seq name_eqType :=
  if e is (e'; x <: _) then cons x (a e') else nil.
move=> e; apply: negbT; rewrite /gen_fresh; set n := nenv_size e.
pose b := filter (nwf_var e) (map gen_name (rev (iota 0 n.+1))).
suff: size b <= size (a e).
rewrite {}/b {}/n; elim: {2 3 6}e => [/=|e' Hrec ? t].
  by case Hx: (nwf_var e _) => //=; rewrite if_same.
  rewrite [nenv_size _]/= [size (a _)]/= fresh_belowE /nwf_bvar .
  case Hx: (nwf_var e (gen_name (nenv_size e').+1)) => // Hsize.
  rewrite Hrec //; move: Hsize.
  by rewrite iota_pos rev_rcons addn0 map_cons /= Hx /=.
apply: uniq_leq_size => [|x].
  by apply: filter_uniq; rewrite map_inj_uniq ?rev_uniq ?iota_uniq //.
rewrite {}/b mem_filter; move/andP=> [Hx _].
by elim: e Hx {n} => //= [e Hrec y _]; rewrite inE eq_sym; case: eqP.
Qed.

Lemma freshen_lookup : forall e x, (e |- /x) ->
  exists2 t, (|- subst_var e x <-> t) & (e |- t).
Proof.
move=> e x; case/(appP nwfP andP)=> He; case/(wf_subst_var He) => e'.
move/(subst_var e): x => s; pose n := tsize (compile_type e' s).
move: (ltnSn n) He; rewrite {1}/n; move/S: {s e'}n (s) e (e').
elim=> // [n Hrec] [x||s1 s2|x s1 s2] e e'; rewrite /= ?ltnS => Hn He He'.
- move/He'; exists (/x); first by constructor.
  by apply: (appP andP nwfP); split.
- by exists Top; [constructor | apply: (appP andP nwfP); split].
- move/andP=> [Hs1 Hs2].
  case: (Hrec _ _ _ _ He He' Hs1); first by apply: leq_trans Hn; exact: leq_addr.
  case: (Hrec _ _ _ _ He He' Hs2); first by apply: leq_trans Hn; exact: leq_addl.
  by move=> t2 Hst2 Ht2 t1 Hst1 Ht1; exists (t1 --> t2); constructor.
move/and3P=> [Hx Hs1 Hs2].
case: (Hrec _ _ _ _ He He' Hs1); first by apply: leq_trans Hn; exact: leq_addr.
move=> t1 Hst1 Ht1; move: (gen_fresh e) (bvar_fresh e) => y Hy.
pose s2' := swap_type y x s2.
have Hy' := sub_env_bvar He' Hy.
case: (Hrec s2' (e; y <: t1) (e'; y <: s1)).
- rewrite /s2' (compile_swap_type _ s1) //; apply: leq_trans Hn; exact: leq_addl.
- by rewrite /= Hy; apply/nwfP.
- exact: sub_decl_env.
- by rewrite /s2' (wf_swap_type _ s1).
move=> t2 Hst2 Ht2; exists (\A y <: t1, t2); last by constructor.
apply ALPHA_All with (swap_type y x t2) => //.
  apply: (appP eqP swap_typeP); exact: swap_typeC.
by apply: nalphaP; rewrite -(swap_typeI y x s2) nalpha_swap; apply/nalphaP.
Qed.

Lemma wf_compile_subtype : forall e s t,
  and3 (e |- s) (e |- t) (sub_compile_type e s t) -> (e |- s <: t).
Proof.
move=> e s t [Hs Ht [n Hn]]; elim: n e t s Hn Hs Ht => //= [n Hrec] e t.
case Ht0: (_ == _); first by case: t Ht0 => //=; constructor.
case{Ht0}=> //= [x|s1 s2|x s1 s2].
- case/orP.
    case: t => //= y Dx Hx; suff ->: x = y by constructor.
    case/(appP nwfP andP): Hx {Hrec} => _; elim: e Dx => //= [e Hrec z t].
    by case: (x =P z) => [<-|_]; case: (y =P _) => //=; auto.
  move=> Hn Hex Ht; move: (freshen_lookup Hex) => [s Hts Hs]. 
  move: (appP nwfP andP Hex) => [He Hx].
  apply: SA_Trans_Tvar (Hts) _; first by apply: subst_varP; exact: eqxx.
  apply: Hrec (Hs) Ht; rewrite -(lookup_compile He Hx) //; first by apply/nalphaP.
  by apply/(nwf_typeP He).
- case: t => //= [t1 t2]; move/andP=> [Hn1 Hn2]; case/(appP nwfP andP)=> He /=.
  case/andP=> [Hs1 Hs2]; case/(appP nwfP andP) => _ /=; case/andP=> [Ht1 Ht2].
  by constructor; apply: Hrec => //; apply: (nwf_typeP He).
case: t => //= [y t1 t2]; move/andP=> [Hn1 Hn2]; case/(appP nwfP andP)=> He /=.
case/and3P=> [Hx Hs1 Hs2]; case/(appP nwfP andP) => _ /=.
case/and3P=> [Hy Ht1 Ht2]; apply SA_All with (swap_type x y t2).
- by apply: Hrec => //; apply: (nwf_typeP He).
- exact: bvarP.
- apply: swap_typeP; exact: eqxx.
apply: Hrec.
- rewrite (compile_swap_type t1 t1) => //.
  by rewrite -(compile_swap_type s1 _ Hy Hx) (compile_swap_type _ s1).
- apply: nwfP; rewrite /nwf_envtype /= He Hx Ht1 /=.
  by rewrite -(wf_swap_type s1 _ _ Hy Hx) (wf_swap_type _ s1).
by apply: nwfP; rewrite /nwf_envtype /= He Hx Ht1 /=; rewrite (wf_swap_type _ t1).
Qed.

End NaturalFsub.

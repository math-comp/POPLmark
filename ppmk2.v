(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Index manipulations (actuallly common to de Bruijn & Barendregt indices). *)

Definition liftv h i j := if i <= j then h + j else j.

Definition lowerv i j := if j <= i then j else predn j.

Lemma lift1v_inv : forall i, cancel (liftv 1 i) (lowerv i).
Proof.
move=> i j; rewrite /liftv /lowerv.
by case Hj: (i <= j); [rewrite add1n ltnNge Hj | rewrite ltnW  // ltnNge Hj].
Qed.

Lemma neq_liftv : forall h i j, (liftv (S h) i j == i) = false.
Proof.
move=> h i j; rewrite eqn_leq leqNgt (leqNgt i) andbC /liftv.
case: (leqP i j) => [Hj|->] //.
by rewrite andbC addSn ltnS (leq_trans Hj) ?leq_addl.
Qed.

Lemma lift1v_lower : forall i j, liftv 1 i (lowerv i j) = (j == i) + j.
Proof.
move=> i j; rewrite /liftv /lowerv eqn_leq.
by case: (leqP j i) => Hj; [case: leqP | rewrite -(subnKC Hj) /= leq_addr].
Qed.

Lemma lowerv_inv : forall i j, (j == i) = false -> liftv 1 i (lowerv i j) = j.
Proof.  by move=> i j; rewrite lift1v_lower => ->. Qed.

Lemma liftv_add : forall h1 h2 i j,
  liftv (h1 + h2) i j = liftv h1 i (liftv h2 i j).
Proof.
move=> h1 h2 i j; rewrite /liftv; case Hij: (i <= j); last by rewrite Hij.
by rewrite addnA (leq_trans Hij) ?leq_addl.
Qed.

Lemma liftv0 : forall i j, liftv 0 i j = j.
Proof. move=> *; exact: if_same. Qed.

Lemma liftvS_lo : forall h i j, liftv (S h) i j = liftv 1 i (liftv h i j).
Proof. exact: liftv_add 1. Qed.

Lemma liftvS_hi : forall h i j, liftv (S h) i j = liftv 1 (h + i) (liftv h i j).
Proof.
move=> h i j; rewrite /liftv; case: leqP => Hj; first by rewrite leq_add2l Hj.
by rewrite leqNgt (leq_trans Hj) ?leq_addl.
Qed.

Lemma liftvT : forall h1 h2 i, liftv h1 i (h2 + i) = h1 + h2 + i.
Proof. by move=> *; rewrite /liftv leq_addl addnA. Qed.

Lemma liftvF : forall h1 h2 i, liftv h1 (S h2 + i) i = i.
Proof. by move=> *; rewrite /liftv addSn ltnNge leq_addl. Qed.

Lemma lowervF : forall h i, lowerv (h + i) i = i.
Proof. by move=> *; rewrite /lowerv leq_addl. Qed.

Lemma lowervT : forall h i, lowerv i (S h + i) = h + i.
Proof. by move=> *; rewrite -add1n -liftvT lift1v_inv. Qed.

Lemma eq_liftv2 : forall h i j1 j2, (liftv h i j1 == liftv h i j2) = (j1 == j2).
Proof.
move=> h i j1 j2; elim: h => [|h <-]; first by rewrite !liftv0.
by rewrite !(liftvS_lo h) (can_eq (lift1v_inv i)).
Qed.

Lemma eq_lowerv : forall i j1 j2,
  (lowerv i j1 == j2) = ((j1 == i) + j1 == liftv 1 i j2).
Proof. by move=> *; rewrite -lift1v_lower eq_liftv2. Qed.

Lemma liftvC : forall h1 h2 i1 i2 j,
  i1 <= i2 -> liftv h1 i1 (liftv h2 i2 j) = liftv h2 (h1 + i2) (liftv h1 i1 j).
Proof.
rewrite /liftv => h1 h2 i1 i2 j Hi; case: (leqP i1 j) => Hj1.
  rewrite leq_add2l; case Hj2: (i2 <= j); last by rewrite Hj1.
  by rewrite addnCA (leq_trans Hj1) ?leq_addl.
rewrite !(leqNgt _ j) !(leq_trans Hj1) //=; first by rewrite leqNgt Hj1.
exact: leq_trans Hi (leq_addl _ _).
Qed.

Lemma liftvC_addl : forall h1 h2 h3 i j,
  liftv h1 i (liftv h2 (h3 + i) j) = liftv h2 (h1 + h3 + i) (liftv h1 i j).
Proof. by move=>*; rewrite liftvC ?leq_addl ?addnA. Qed.

(* Core F-sub types, with Barendregt indices. *)
(* This is almost the same as Fsub with variables with the Barendregdt   *)
(* convention that no variable is free and bound: the variables are      *)
(* systematically labelled with integers, i.e., the variable introduced  *)
(* under a context of length n is always X_n. Thus we can omit the       *)
(* variable name in the binders, and indeed we do so because this avoids *)
(* ill-defined substitutions below. For more uniformity, we group the    *)
(* Arrow and All types in a CoC-style Prod type, using a boolean flag    *)
(* to indicate (dependent) bounded products. We use a kind environment   *)
(* below to check that the Arrow product is indeed non-dependent, that   *)
(* is, that the bound variable does not actually occur in the codomain.  *)

CoInductive kind : Set := Ktype | Kvalue.

Definition eq_kind k1 k2 :=
  match k1, k2 with
  | Ktype, Ktype => true
  | Kvalue, Kvalue => true
  | _, _ => false
  end.

Lemma eq_kindP : Equality.axiom eq_kind.
Proof. by do 2 case; constructor. Qed.

Definition eq_kindMixin := Equality.Mixin eq_kindP.
Canonical Structure kind_eqType := EqType kind eq_kindMixin.

Inductive type : Type := Tvar (i : nat) | Top | Prod (k : kind) (s t : type).

Fixpoint eq_type (t1 t2 : type) {struct t2} : bool :=
  match t1, t2 with
  | Tvar i1, Tvar i2 => i1 == i2
  | Top, Top => true
  | Prod k1 s1 t1', Prod k2 s2 t2' =>
    [&& (k1 == k2) , (eq_type s1 s2) & (eq_type t1' t2') ]
  | _, _ => false
  end.

Lemma eq_typeP : Equality.axiom eq_type.
Proof.
elim=> [i1||k1 s1 IHs t1 IHt] [i2||k2 s2 t2] //=; try by constructor.
  by apply: (iffP eqP) => [<- | [<-]].
apply: (iffP and3P); case; first by move/eqP->; move/IHs->; move/IHt->.
split; [exact/eqP | exact/IHs | exact/IHt].
Qed.

Definition type_mixin := Equality.Mixin eq_typeP.
Canonical Structure type_eqType := EqType type type_mixin.

Fixpoint lift (h i : nat) (t : type) {struct t} : type :=
  match t with
  | Tvar j => Tvar (liftv h i j)
  | Top => Top
  | Prod b s t' => Prod b (lift h i s) (lift h i t')
  end.

Lemma lift0 : forall i t, lift 0 i t = t.
Proof. by move=> i; elim=> //= [j|k s -> t ->] //; rewrite liftv0. Qed.

Lemma liftS_lo : forall h i t, lift (S h) i t = lift 1 i (lift h i t).
Proof. by move=> h i; elim=> //= [j|b s -> t -> //]; rewrite -liftvS_lo. Qed.

Lemma liftS_hi : forall h i t, lift (S h) i t = lift 1 (h + i) (lift h i t).
Proof. by move=> h i; elim=> //= [j|b s -> t -> //]; rewrite -liftvS_hi. Qed.

Lemma lift_iter1: forall h i, lift h i =1 iter h (lift 1 i).
Proof. by move=> h i t; elim: h => /= [|h <-]; rewrite /= ?lift0 -?liftS_lo. Qed.

Lemma lift_add : forall h1 h2 i t,
  lift (h1 + h2) i t = lift h1 i (lift h2 i t).
Proof. by move=> *; rewrite lift_iter1 iter_add -!lift_iter1. Qed.

Lemma liftC : forall h1 h2 i1 i2 t,
  i1 <= i2 -> lift h1 i1 (lift h2 i2 t) = lift h2 (h1 + i2) (lift h1 i1 t).
Proof.
by move=> h1 h2 i1 i2 t Hi; elim: t => //= [j|k s <- t <- //]; rewrite liftvC.
Qed.

Lemma liftC_addl : forall h1 h2 h3 i t,
  lift h1 i (lift h2 (h3 + i) t) = lift h2 (h1 + h3 + i) (lift h1 i t).
Proof. by move=> *; rewrite -addnA liftC ?leq_addl. Qed.

(* Declarations (= environment items). *)

Inductive decl : Set := Decl (k : kind) (t : type).

Notation "k '~:' t" := (Decl k t) (at level 45, no associativity).

Definition eq_decl d1 d2 :=
  let: k1 ~: t1 := d1 in let: k2 ~: t2 := d2 in (k1 == k2) && (t1 == t2).

Lemma eq_declP : Equality.axiom eq_decl.
Proof.
move=> [k1 t1] [k2 t2] /=; case: eqP => [->|]; last by right; case; eauto.
by apply: (iffP eqP) => [->|[]].
Qed.

Definition eq_declMixin := Equality.Mixin eq_declP.
Canonical Structure decl_eqType := EqType decl eq_declMixin.

Definition liftd h i d := let: k ~: t := d in k ~: lift h i t.

Definition env := seq decl_eqType.

(* We'll be representing environments with reversed sequences, since *)
(* most of the time we extend an environment at the end. To make the *)
(* lemmas more readable we introduce some notation.                  *)
(* Warning : since this is only notation, we must beware that the    *)
(* true syntax is reversed when rewriting or selecting occurrences.  *)

Notation "e ',`' d" := (@cons _ d e)
  (at level 61, left associativity, d at level 50, format "e ',`' d").
Notation "e ',`' 'X' : t" := (e,`Kvalue ~: t)
  (at level 61, left associativity, t at level 45, format "e ',`' 'X'  ':'  t").
Notation "e ',`' 'X' <: t" := (e,`Ktype ~: t)
  (at level 61, left associativity, t at level 45, format "e ',`' 'X'  '<:'  t").
Notation "e1 ';`' e2" := (@cat _ e2 e1)
  (at level 61, left associativity, format "e1 ';`' e2").
Notation "# e" := (@size _ e) (at level 8, e at level 0, format "# e").
Notation "e1 ',`' [ d ] ';`' e2" := (e1,`d;`map (liftd 1 #e1) e2)
  (at level 61, d at level 50, format "e1 ',`' [ d ] ';`' e2").
Notation "e1 ',`' [ 'X' : t ] ';`' e2" := (e1,`[Kvalue ~: t];`e2)
  (at level 61, t at level 45, format "e1 ',`' [ 'X'  :  t ] ';`' e2").
Notation "e1 ',`' [ 'X' <: t ] ';`' e2" := (e1,`[Ktype ~: t];`e2)
  (at level 61, t at level 45, format "e1 ',`' [ 'X'  <:  t ] ';`' e2").

Lemma size_widen : forall u2 e1 e2 k u1, #(e1,`k ~: u1;`e2) = #(e1,`k ~: u2;`e2).
Proof. by move=> *; rewrite !size_cat. Qed.

(* Lexical correctness check: we check only that a type has only bound *)
(* type variables.                                                     *)

Fixpoint wfv (e : env) (i : nat) (k : kind) {struct e} : bool :=
  if e is e',`k' ~: _ then (if i == #e' then k == k' else wfv e' i k) else false.

Lemma wfv_overlift : forall h e i, wfv e (liftv h #e i) =1 wfv e i.
Proof.
move=> h e i k; rewrite /liftv addnC; case: leqP => //.
elim: e => //= [[k' t] e IHe] Hi; rewrite {}IHe; last exact: ltnW.
by rewrite -(addn0 #e) -{1 3}(subnKC Hi) -!addnA !addSnnS !eqn_add2l.
Qed.

Lemma wfv_widen : forall u1 e1 e2 k k' i,
  wfv (e1,`k ~: u1;`e2) i k' =
    if i == #e1 then k' == k else wfv (e1;`e2) (lowerv #e1 i) k'.
Proof.
move=> u1 e1 e2 k k' i; elim: e2 => [/=|[k2 u2] e2 /= ->].
  by case Hi: (i == _); rewrite // -{1}(lowerv_inv Hi) wfv_overlift.
rewrite !size_cat /= eq_lowerv liftvT add1n -addSnnS.
by case: (i =P #e1) => // <-; rewrite -{1}[i]add0n eqn_add2r.
Qed.

Definition wfv_weak1 : forall e1 e2 d i,
  wfv (e1,`[d];`e2) (liftv 1 #e1 i) =1 wfv (e1;`e2) i.
Proof.
move=> e1 e2 [uk u] i k; elim: e2 => [/=|[k2 u2] e2 /= ->].
  by rewrite neq_liftv wfv_overlift.
by rewrite !size_cat /= size_map -addSnnS -(add1n #e2) -liftvT eq_liftv2.
Qed.

Fixpoint wft (e : env) (t : type) {struct t} : bool :=
  match t with
  | Tvar i => wfv e i Ktype
  | Top => true
  | Prod k s t' => wft e s && wft (e,`k ~: s) t'
  end.

Lemma wft_widen : forall u1 u2 e1 e2 k t,
  wft (e1,`k ~: u1;`e2) t = wft (e1,`k ~: u2;`e2) t.
Proof.
move=> u1 u2 e1 e2 k t; elim: t e2 => //= [i|k' s IHs t IHt] e2.
  by rewrite wfv_widen (wfv_widen u2).
by rewrite IHs -cat_cons IHt.
Qed.

Lemma wft_widen0 : forall u1 u2 e k, wft (e,`k ~: u1) =1 wft (e,`k ~: u2).
Proof. move=> u1 u2 e; exact: wft_widen nil. Qed.

Lemma wft_weak1 : forall e1 e2 d t,
  wft (e1,`[d];`e2) (lift 1 #e1 t) = wft (e1;`e2) t.
Proof.
move=> e1 e2 d t; elim: t e2 => //= [i|k s IHs t IHt] e2; first exact: wfv_weak1.
by rewrite -!cat_cons IHs -IHt.
Qed.

Lemma wft_weak0 : forall e d t, wft (e,`d) (lift 1 #e t) = wft e t.
Proof. move=> e; exact: wft_weak1 nil. Qed.

Lemma wft_weak : forall e1 e2 t, wft (e1;`e2) (lift #e2 #e1 t) = wft e1 t.
Proof.
move=> e1 e2 t; rewrite lift_iter1; elim: e2 => //= [d e2 <-].
by rewrite -iterS -!lift_iter1 liftS_hi -size_cat wft_weak0.
Qed.

Fixpoint wfe (e : env) : bool :=
  if e is e',`_ ~: u then wfe e' && wft e' u else true.

Lemma wfe_widen : forall u1 e1 e2 k,
  wfe (e1,`k ~: u1;`e2) = wfe (e1,`k ~: Top;`e2) && wft e1 u1.
Proof.
move=> u1 e1 e2 k; elim: e2 => [/=|[k2 u2] e2 /= ->]; rewrite -!andbA //.
by congr andb; rewrite andbC -(wft_widen Top).
Qed.

Lemma wfe_weak1 : forall e1 e2 k u,
  wfe (e1,`[k ~: u];`e2) = wfe (e1;`e2) && wft e1 u.
Proof.
move=> e1 e2 k u; elim: e2 => [/=|[k2 u2] e2 /= ->]; rewrite -?andbA //.
by congr andb; rewrite wft_weak1 andbC.
Qed.

Fixpoint lookup (e : env) (i : nat) {struct e} : type :=
  if e is e',`_ ~: t then
    lift 1 #e' (if i == #e' then t else lookup e' i)
  else Top.

Lemma wft_lookup : forall e i, wfe e -> wft e (lookup e i).
Proof.
move=> e i; elim: e => [|[k t] e IHe] //=; move/andP=> [He Ht].
by rewrite wft_weak0; case: eqP; auto.
Qed.

Lemma lookup_unbound : forall e i, #e <= i -> lookup e i = Top.
Proof.
move=> e i; elim: e => //= [[_ t] e IHe]; rewrite ltn_neqAle -if_neg eq_sym.
by move/andP => [-> Hi]; rewrite IHe.
Qed.

Lemma lookup_overlift : forall h i e, lookup e (liftv h #e i) = lookup e i.
Proof.
move=> h i e; rewrite /liftv; case Hi: (#e <= i) => //.
rewrite !lookup_unbound //; exact: leq_trans Hi (leq_addl _ _).
Qed. 

Lemma lookup_widen : forall u1 e1 e2 k i, 
  lookup (e1,`k ~: u1;`e2) i =
    if i == #e1 then lift (S #e2) #e1 u1 else lookup (e1,`X <: Top;`e2) i.
Proof.
move=> u1 e1 e2 k i; rewrite lift_iter1.
elim: e2 => [/=|[_ u2] e2 /= ->]; case: (i =P #e1); rewrite ?size_cat //= => <-.
by rewrite -addSnnS -{2}[i]add0n eqn_add2r /= -!iterS -!lift_iter1 -liftS_hi.
Qed.

Lemma lookup_weak1 : forall e1 e2 d i,
  lookup (e1,`[d];`e2) (liftv 1 #e1 i) = lift 1 #e1 (lookup (e1;`e2) i).
Proof.
move=> e1 e2 [k1 t1] i; elim: e2 => [/=|[k2 t2] e2 /= ->].
  by rewrite neq_liftv lookup_overlift.
rewrite !size_cat size_map /= -addSnnS -(fun_if (lift _ _)) -(add1n #e2).
by rewrite -liftC_addl -liftvT eq_liftv2.
Qed.

Lemma lookup_weak0 : forall e d i,
  lookup (e,`d) (liftv 1 #e i) = lift 1 #e (lookup e i).
Proof. move=> e; exact: lookup_weak1 nil. Qed.

(* Fsub subtyping is only semi-decidable, so we need to pass a search *)
(* depth to the function that checks for subtypes.                    *)

Fixpoint nsubtype (e : env) (t1 t2 : type) (n : nat) {struct n} : bool :=
  if n is S n' then
     (t2 == Top)
  || match t1, t2 with
     | Tvar i1, _ => (t1 == t2) || nsubtype e (lookup e i1) t2 n'
     | Prod k1 s1 t1', Prod k2 s2 t2' =>
       [&& (k1 == k2) , (nsubtype e s2 s1 n') & (nsubtype (e,`k2 ~: s2) t1' t2' n') ]
     | _, _ => false
    end
  else false.

Lemma nsubtype_leq : forall e t1 t2 n1 n2, n1 <= n2 ->
  nsubtype e t1 t2 n1 -> nsubtype e t1 t2 n2.
Proof.
move=> e t1 t2 n1 n2; elim: n1 n2 e t1 t2 => // [n1 IHn] [|n2] //= e t1 t2 Hn.
case: eqP => // _; case: t1 => //= [i1|b1 s1 t1]; first by case: eqP => //=; eauto.
by case: t2 => // [b2 s2 t2]; case/and3P=> -> /= *; apply/andP; eauto.
Qed.

Lemma nsubtype_weak1 : forall e1 e2 d t1 t2,
  nsubtype (e1,`[d];`e2) (lift 1 #e1 t1) (lift 1 #e1 t2)
    =1 nsubtype (e1;`e2) t1 t2.
Proof.
move=> e1 e2 d t1 t2 n.
elim: n e2 t1 t2 => //= n IHn e2 t1 t2; congr orb; first by case t2.
case: t1 => //= [i1|b1 s1 t1].
  rewrite lookup_weak1 // IHn; congr orb; case t2 => //= i2; exact: eq_liftv2.
by case: t2 => //= [b2 s2 t2]; rewrite -!cat_cons -!IHn.
Qed.

Lemma nsubtype_weak0 : forall e d t1 t2,
  nsubtype (e,`d) (lift 1 #e t1) (lift 1 #e t2) =1 nsubtype e t1 t2.
Proof. move=> e; exact: nsubtype_weak1 nil. Qed.

Lemma nsubtype_weak : forall e1 e2 t1 t2,
  nsubtype (e1;`e2) (lift #e2 #e1 t1) (lift #e2 #e1 t2) =1 nsubtype e1 t1 t2.
Proof.
move=> e1 e2 t1 t2 n; elim: e2 => [|d e2 IHe]; first by rewrite !lift0.
by rewrite /= !(liftS_hi #e2) -size_cat nsubtype_weak0.
Qed.

Inductive subtype (e : env) (t1 t2 : type) : Prop :=
  Subtype (n : nat) (_ : nsubtype e t1 t2 n).

Lemma subtype_top : forall e t, subtype e t Top.
Proof. by exists 1. Qed.
Hint Resolve subtype_top.

Lemma subtype_prod : forall e k s1 t1 s2 t2,
    subtype e s2 s1 -> subtype (e,`k ~: s2) t1 t2 ->
  subtype e (Prod k s1 t1) (Prod k s2 t2).
Proof.
move=> e k s1 t1 s2 t2 [ns Hs] [nt Ht]; exists (S (ns + nt)); rewrite /= eqxx /=.
by rewrite {1}addnC 2?(nsubtype_leq (leq_addl _ _)).
Qed.
Hint Resolve subtype_prod.

(* Lemma A.1 *)
Lemma subtype_refl : forall e t, subtype e t t.
Proof.
move=> e t; elim: t e => // [i|b s IHs t IHt] e; auto.
by exists 1; rewrite /= eqxx.
Qed.
Hint Resolve subtype_refl.

Lemma subtype_var : forall e i, subtype e (Tvar i) (lookup e i).
Proof.
move=> e i; have [n Hn] := subtype_refl e (lookup e i).
by exists (S n); rewrite /= Hn !orbT.
Qed.
Hint Resolve subtype_var.

(* Induction over the subtype predicate *)

Lemma subtype_ind' : forall P : env -> type -> type -> Prop,
  (forall e t, P e t Top) ->
  (forall e i, P e (Tvar i) (Tvar i)) ->
  (forall e i t, P e (lookup e i) t -> P e (Tvar i) t) ->
  (forall e k s1 t1 s2 t2, P e s2 s1 -> P (e,`k ~: s2) t1 t2 ->
       P e (Prod k s1 t1) (Prod k s2 t2)) ->
  (forall e t1 t2,  subtype e t1 t2 -> P e t1 t2).
Proof.
move=> P Htop Hvar1 HvarT Hprod e t1 t2 [n].
elim: n e t1 t2 => //= [n IHn] e t1 t2; case: eqP => [->|_] //=.
case: t1 => //= [i|k1 s1 t1]; first by case: eqP => [<-|_] /=; auto.
by case: t2 => //= [k2 s2 t2]; case/and3P; move/eqP=> <-; auto.
Qed.

(* Lemmas A.5.1 & A.5.2 *)
Lemma subtype_weak0 : forall e d t1 t2,
  subtype e t1 t2 -> subtype (e,`d) (lift 1 #e t1) (lift 1 #e t2).
Proof. by move=> e d t1 t2 [n Hn]; exists n; rewrite nsubtype_weak0. Qed.

(* Lemmas A.1 + A.5.1/A.5.2 combined *)
Lemma subtype_weak1 : forall e1 e2 d t1 t2,
  subtype (e1;`e2) t1 t2 -> subtype (e1,`[d];`e2) (lift 1 #e1 t1) (lift 1 #e1 t2). 
Proof. by move=> e1 e2 d t1 t2 [n Hn]; exists n; rewrite nsubtype_weak1. Qed.

(* Lemma A.5.5 (also A.2.2). *)
Lemma subtype_weak : forall e1 e2 t1 t2,
  subtype e1 t1 t2 -> subtype (e1;`e2) (lift #e2 #e1 t1) (lift #e2 #e1 t2).
Proof. by move=> e1 e2 t1 t2 [n Hn]; exists n; rewrite nsubtype_weak. Qed.

Lemma subtype_unweak : forall e1 e2 d t1 t2,
  subtype (e1,`[d];`e2) (lift 1 #e1 t1) (lift 1 #e1 t2) -> subtype (e1;`e2) t1 t2.
Proof. by move=> e1 e2 d t1 t2 [n]; rewrite nsubtype_weak1; exact: Subtype. Qed.

Lemma lookup_narrow : forall e1 e2 k t1 t2 i, subtype e1 t1 t2 ->
  let e := e1,`k ~: t2;`e2 in
  subtype e (lookup (e1,`k ~: t1;`e2) i) (lookup e i).
Proof.
move=> e1 e2 k t1 t2 i Ht; rewrite /= (lookup_widen t1) (lookup_widen t2).
rewrite -cat_rcons -(size_rcons e2 (k ~: t2)).
case: (i == _) => //; exact: subtype_weak.
Qed.

Lemma lookup_narrow0 : forall e k t1 t2 i, subtype e t1 t2 ->
  subtype (e,`k ~: t2) (lookup (e,`k ~: t1) i) (lookup (e,`k ~: t2) i).
Proof. move=> e; exact: lookup_narrow nil. Qed.

(* Lemma A.3, i.e., Challenge 1a *)
Lemma subtype_trans_narrow : forall t2,
   (forall e t1 t3, subtype e t1 t2 -> subtype e t2 t3 -> subtype e t1 t3)
/\ (forall e1 e2 k t1 t3 t4, subtype e1 t1 t2 ->
    subtype (e1,`k ~: t2;`e2) t3 t4 -> subtype (e1,`k ~: t1;`e2) t3 t4).
Proof.
pose fix sz (t : type) : nat := if t is Prod _ s t' then S (sz s + sz t') else 0.
have Esz: forall t, sz (lift _ _ t) = sz t.
  by move=> h i t; elim: t => //= [k s -> t ->].
move=> t2; elim: {t2}(S _) {-2}t2 (ltnSn (sz t2)) => //= r IHr.
have{IHr} Htrans: forall e t1 t2 t3,
    sz t2 <= r -> subtype e t1 t2 -> subtype e t2 t3 -> subtype e t1 t3.
- move=> e t1 t2 t3 Hr Ht1 [[|n3] //= Hn3]; case: eqP Hn3 Ht1 => [->|_] //=.
  case: eqP => [<-|_] //= Hn3 [n1]; elim: n1 t1 => //= [n1 IHn1] t1 Hn1.
  case: eqP Hn1 Hn3 => [->|_] //; case: t1 => //= [i1|k1 s1 t1].
    case/orP; first by move/eqP=> <- //; exists (S n3); rewrite /= Hn3 !orbT.
    by case/IHn1 {n1 IHn1} => [n1 Hn1]; exists (S n1); rewrite /= Hn1 !orbT.
  case: t2 {IHn1} Hr => //= [k2 s2 t2] Hr; case/and3P; move/eqP=> -> {k1}.
  move/Subtype=> Hs1; move/Subtype {n1} => Ht1.
  case: t3 => //= [k3 s3 t3]; case/and3P; move/eqP=> <- {k3}.
  move/Subtype=> Hs3; move/Subtype {n3} => Ht3.
  case: (IHr t2) => [|Ht2 _]; first by apply: leq_trans Hr; rewrite ltnS leq_addl.
  case: {IHr}(IHr s2) => [|Hs2t Hs2n]; last by move: (Hs2n e nil) => /=; auto.
  by apply: leq_trans Hr; rewrite ltnS leq_addr.
move=> t2; rewrite ltnS => Hr; split; eauto => e1 e2 k t1 t3 t4 Ht [n Hn].
elim: n e2 t3 t4 Hn => //= n IHn e2 t3 t4.
case: eqP => [->|_] //=; case: t3 => // [i3|k3 s3 t3].
  case: eqP => [<- | _ ] //=; move/IHn {n IHn}; rewrite lookup_widen.
  case Hi3: (i3 == _); last first.
    by move=> [n Hn]; exists (S n); rewrite /= lookup_widen Hi3 Hn !orbT.
  apply: {t4}Htrans; first by rewrite Esz.
  case/(subtype_weak (rcons e2 (k ~: t1))): Ht => n.
  rewrite cat_rcons size_rcons => Hn.
  by exists (S n); rewrite /= lookup_widen Hi3 Hn !orbT.
case: t4 => //= [k4 s4 t4]; case/and3P; move/eqP=> <- {k4}; move/IHn=> Hs.
by rewrite -cat_cons; move/IHn; auto.
Qed.

(* Corollaries of A.4 *)

Lemma subtype_trans : forall e t1 t2 t3,
  subtype e t1 t2 -> subtype e t2 t3 -> subtype e t1 t3.
Proof. by move=> e t1 t2; case (subtype_trans_narrow t2); auto. Qed.
Hint Resolve subtype_trans.

Lemma subtype_narrow : forall e1 e2 k t1 t2 t3 t4, subtype e1 t1 t2 ->
  subtype (e1,`k ~: t2;`e2) t3 t4 -> subtype (e1,`k ~: t1;`e2) t3 t4.
Proof. move=> e1 e2 k t1 t2; case (subtype_trans_narrow t2); eauto. Qed.

Lemma subtype_narrow0 : forall e1 k t1 t2 t3 t4, subtype e1 t1 t2 ->
  subtype (e1,`k ~: t2) t3 t4 -> subtype (e1,`k ~: t1) t3 t4.
Proof. move=> e1; exact: subtype_narrow nil. Qed.

(* Type substitution. *)
(* The type subtituted at index i must have been well-formed in a *)
(* context of depth i, so it can always be lifted at index i.     *)
(* We actually bundle the lifting with the substitution,          *)
(* performing if only at the leaves, as this simplifies inductive *)
(* proofs.                                                        *)

Fixpoint subst (h i : nat) (u t : type) {struct t} : type :=
  match t with
  | Tvar j => if j == i then lift h i u else Tvar (lowerv i j)
  | Top => Top
  | Prod b s t' => Prod b (subst h i u s) (subst (S h) i u t')
  end.

Lemma subst_add : forall h1 h2 i u,
  subst (h1 + h2) i u =1 subst h1 i (lift h2 i u).
Proof.
move=> h1 h2 i u t. 
by elim: t h1 => //= [j|b s IHs t IHt] h1; rewrite ?lift_add // IHs -IHt.
Qed.

Lemma subst_lift : forall h i u t, subst h i u (lift 1 i t) = t.
Proof.
move=> h i u t; elim: t h => //= [j|k s IHs t IHt] h; last by rewrite IHs IHt.
by rewrite lift1v_inv neq_liftv.
Qed.

Lemma lift_subst_leq : forall h1 h2 i1 i2 t u,
  i1 <= i2 -> 
  lift h1 i1 (subst h2 i2 u t)
    = subst h2 (h1 + i2) (lift h1 i1 u) (lift h1 i1 t).
Proof.
move=> h1 h2 i1 i2 t u Hi.
elim: t h2 => //= [j|k s IHs t IHt] h2; last by congr Prod.
have Dh1i2: liftv h1 i1 i2 = h1 + i2 by rewrite /liftv Hi.
rewrite -{1}Dh1i2 eq_liftv2; case Hj: (j == _); first exact: liftC.
by rewrite /= -{2}(lowerv_inv Hj) liftvC // lift1v_inv.
Qed.

Lemma lift_subst_addl : forall h1 h2 i u t,
  lift h1 (h2 + i) (subst h2 i u t) = subst (h1 + h2) i u (lift h1 (S h2 + i) t).
Proof.
move=> h1 h2 i u t; elim: t u => //= [j|b s IHs t IHt] u;
  last by rewrite -IHs -{1}addn1 -(addn1 (h1 + h2)) 2!subst_add -IHt.
rewrite -{6}(liftvF h1 h2 i) eq_liftv2.
case Hj: (j == i); first by rewrite -{1}(addn0 h2) -liftC_addl -lift_add addnC.
by rewrite /= -{2}(lowerv_inv Hj) -add1n -liftvC_addl lift1v_inv.
Qed.

Lemma substC_addl : forall h i u v t,
  subst h i u (subst 0 (S h + i) v t) =
    subst 0 (h + i) (subst h i u v) (subst (S h) i u t).
Proof.
move=> h i u v t; rewrite -{1}(add0n h) -{2}add1n.
elim: t 0 => //= [j|b s IHs t IHt] h'; last by rewrite IHs -addSn IHt.
case Hji: (j == i).
  rewrite -{1}[j]add0n (eqP Hji) eqn_add2r lowervF /= eqxx.
  by rewrite addSnnS !(addnC h') !lift_add liftS_hi subst_lift.
have:= erefl (lowerv i j == h + i).
rewrite /= {2 3}eq_lowerv Hji add0n liftvT add1n.
case Hjh: (j == _) => /= Hijh; first by rewrite lift_subst_addl.
rewrite eq_lowerv Hjh add0n liftvF Hji.
by rewrite -{1}(lowerv_inv Hji) -{1}(lowerv_inv Hijh) liftvC_addl !lift1v_inv.
Qed.

Definition lower i := subst 0 i Top.

Lemma lift1_inv : forall i, cancel (lift 1 i) (lower i).
Proof. move=> i t; exact: subst_lift. Qed.

Lemma lower_inv : forall e1 e2 u t,
  wft (e1,`X : u;`e2) t -> lift 1 #e1 (lower #e1 t) = t.
Proof.
rewrite /lower; move=> e1 e2 u t; elim: t e2 {2}0 => //= [j|k s IHs t IHt] e2 h.
  by rewrite (wfv_widen u); case Hj: (j == _); rewrite //= (lowerv_inv Hj).
rewrite -cat_cons; move/andP=> [Hs Ht]; congr Prod; [exact: IHs Hs| exact: IHt Ht].
Qed.

Lemma lower_inv0 : forall e u t, wft (e,`X : u) t -> lift 1 #e (lower #e t) = t.
Proof. move=> e; exact: lower_inv nil. Qed.

Lemma wft_lower : forall e1 e2 u t,
  wft (e1,`[X : u];`e2) t -> wft (e1;`e2) (lower #e1 t).
Proof.
by move=> e1 e2 u t Ht; move: (Ht); rewrite -{1}(lower_inv Ht) wft_weak1.
Qed.

Lemma wft_lower0 : forall e u t, wft (e,`X : u) t -> wft e (lower #e t).
Proof. move=> e; exact: wft_lower nil. Qed.

Fixpoint subste (i : nat) (u : type) (e : env) {struct e} : env :=
  if e is e',`k ~: t then subste i u e',`k ~: subst #e' i u t else nil.

Notation "e1 ';`' [ u ] e2" := (e1;`subste #e1 u e2)
  (at level 60, u at level 50, format "e1 ';`' [ u ] e2").

Lemma size_subste : forall i u e, #(subste i u e) = #e.
Proof. by move=> i u; elim=> //= [[k t] /= e ->]. Qed.

Lemma wfv_subst : forall e1 e2 u, wfv (e1;`[u]e2) =2 wfv (e1;`e2).
Proof.
move=> e1 e2 u i k; elim: e2 => //= [[k' t] /= e2 ->].
by rewrite !size_cat size_subste.
Qed.

Lemma wft_subst : forall e1 e2 u t,
  wft e1 u -> wft (e1,`X <: u;`e2) t -> wft (e1;`[u]e2) (subst #e2 #e1 u t).
Proof.
move=> e1 e2 u t Hu; elim: t e2 => //= [i|k s IHs t IHt] e2.
  rewrite wfv_widen; case: (i == _); last by rewrite /= wfv_subst.
  by rewrite -(size_subste #e1 u e2) wft_weak.
case/andP=> Hs; rewrite IHs // -cat_cons; exact: IHt.
Qed.

Lemma wft_subst0 : forall e u t,
  wft e u -> wft (e,`X <: u) t -> wft e (subst 0 #e u t).
Proof. move=> e; exact: wft_subst nil. Qed.

Lemma wfe_subst : forall e1 e2 u, wfe (e1,`X <: u;`e2) -> wfe (e1;`[u]e2).
Proof.
move=> e1 e2 u; elim: e2 => [|[k t] e2 IHe] //=; move/andP=> [He Ht] //.
by rewrite {}IHe //=; apply: wft_subst Ht; rewrite wfe_widen in He; case/andP: He.
Qed.

Lemma lookup_subst : forall e1 e2 u i,
  lookup (e1;`[u]e2) i =
    subst #e2 #e1 u (lookup (e1,`X <: u;`e2) (liftv 1 #e1 i)).
Proof.
move=> e1 e2 u i; elim: e2 => [/=|[k2 t2] /= e2 ->].
  by rewrite neq_liftv subst_lift lookup_overlift.
rewrite !size_cat size_subste /=  -addSnnS -{-2}(add1n #e2) -lift_subst_addl.
by rewrite -liftvT eq_liftv2; case: (i == _).
Qed.

(* Lemma A. 10, but without the narrowing. *)

Lemma subtype_subst : forall e1 e2 u t1 t2,
  subtype (e1,`X <: u;`e2) t1 t2 ->
  subtype (e1;`[u]e2) (subst #e2 #e1 u t1) (subst #e2 #e1 u t2).
Proof.
move=> e1 e2 u t1 t2 [n]; elim: n e2 t1 t2 => //= [n IHn] e2 t1 t2.
do 2 case: eqP => [->|_] //=; case: t1 => //= [i1|b1 s1 t1].
  move/IHn {n IHn}; case Hi1: (i1 == _).
    by rewrite lookup_widen Hi1 liftS_lo subst_lift.
  by apply: subtype_trans; rewrite /= -{2}(lowerv_inv Hi1) -lookup_subst.
case: t2 => // [b2 s2 t2]; case/and3P; move/eqP=> <- {b2}; move/IHn=> Hs.
rewrite /= -cat_cons; move/IHn{n IHn}; eauto.
Qed.

Lemma subtype_subst0 : forall e u t1 t2,
  subtype (e,`X <: u) t1 t2 -> subtype e (subst 0 #e u t1) (subst 0 #e u t2).
Proof. move=> e; exact: subtype_subst nil. Qed.

(* Lemma A.6 *)

Lemma subtype_strengthen : forall e u t1 t2,
  wft (e,`X : u) t1 -> wft (e,`X : u) t2 -> 
  subtype (e,`X : u) t1 t2 -> subtype e (lower #e t1) (lower #e t2).
Proof.
move=> e u t1 t2 Ht1 Ht2; rewrite -{1}(lower_inv0 Ht1) -{1}(lower_inv0 Ht2).
exact: (@subtype_unweak _ nil).
Qed.

(* Fsub expressions (we use variables x, y, etc for expressions).      *)

Inductive expr : Set :=
  | Var (i : nat)
  | Fun (k : kind) (s : type) (x : expr)
  | App (x y : expr)
  | Tapp (x : expr) (t : type).

Fixpoint wfx (e : env) (x : expr) {struct x} : bool :=
  match x with
  | Var i => wfv e i Kvalue
  | Fun k s x' => wft e s && wfx (e,`k ~: s) x'
  | App x' y => wfx e x' && wfx e y
  | Tapp x' t =>  wfx e x' && wft e t
  end.

Fixpoint liftx (h i : nat) (x : expr) {struct x} : expr :=
  match x with
  | Var j => Var (liftv h i j)
  | Fun k t x' => Fun k (lift h i t) (liftx h i x')
  | App y x => App (liftx h i y) (liftx h i x)
  | Tapp x' t => Tapp  (liftx h i x') (lift h i t)
  end.

Fixpoint substx (h i : nat) (u : type) (x : expr) {struct x} : expr :=
  match x with
  | Var j =>  Var (if j == i then h + i else lowerv i j)
  | Fun k s x' => Fun k (subst h i u s) (substx (S h) i u x')
  | App x' y => App (substx h i u x') (substx h i u y)
  | Tapp x' t => Tapp (substx h i u x') (subst h i u t)
  end.

Fixpoint subsxx (h i : nat) (z x : expr) {struct x} : expr :=
  match x with
  | Var j => if j == i then liftx h i z else Var (lowerv i j)
  | Fun k s x' => Fun k (lower i s) (subsxx (S h) i z x')
  | App x' y => App (subsxx h i z x') (subsxx h i z y)
  | Tapp x' t => Tapp (subsxx h i z x') (lower i t)
  end.

Lemma wfx_widen :
  forall e1 e2 k t x, wfx (e1,`k ~: t;`e2) x = wfx (e1,`k ~: Top;`e2) x.
Proof.
move=> e1 e2 k1 t1 x; elim: x e2 => [j|k s x IHx|y IHy x IHx|x IHx s] e2 /=.
- by rewrite !wfv_widen.
- rewrite -!cat_cons -IHx; congr andb; exact: wft_widen.
- by rewrite IHy IHx.
rewrite IHx; congr andb; exact: wft_widen.
Qed.

Lemma wfx_widen0 :
  forall e1 k t x, wfx (e1,`k ~: t) x = wfx (e1,`k ~: Top) x.
Proof. move=> e; exact: wfx_widen nil. Qed.

Lemma wfx_weak1 : forall e1 e2 d x,
  wfx (e1,`[d];`e2) (liftx 1 #e1 x) = wfx (e1;`e2) x.
Proof.
move=> e1 e2 d x; elim: x e2 => [j|k s x IHx|y IHy x IHx|x IHx s] e2 /=.
- exact: wfv_weak1.
- by rewrite wft_weak1 -!cat_cons -IHx.
- by rewrite IHy IHx.
by rewrite IHx wft_weak1.
Qed.

Lemma wfx_weak0 : forall e d x, wfx (e,`d) (liftx 1 #e x) = wfx e x.
Proof. move=> e; exact: wfx_weak1 nil. Qed.

Lemma liftxC : forall h1 h2 i1 i2 x,
  i1 <= i2 -> liftx h1 i1 (liftx h2 i2 x) = liftx h2 (h1 + i2) (liftx h1 i1 x).
Proof.
move=> h1 h2 i1 i2 x Hi.
by elim: x => /= [j|k s x ->|y -> x ->|x -> s]; rewrite // -?liftvC -?liftC.
Qed.

Lemma liftxS_hi : forall h i x, liftx (S h) i x = liftx 1 (h + i) (liftx h i x).
Proof.
move=> h i.
by elim=> /= [j|k s x ->|y -> x ->|x -> s]; rewrite -?liftvS_hi -?liftS_hi.
Qed.

Lemma liftxS_lo : forall h i x, liftx (S h) i x = liftx 1 i (liftx h i x).
Proof.
move=> h i.
by elim=> /= [j|k s x ->|y -> x ->|x -> s]; rewrite -?liftvS_lo -?liftS_lo.
Qed.

Lemma liftx0 : forall i x, liftx 0 i x = x.
Proof.
by move=> i; elim=> /= [j|k s x ->|y -> x ->|x -> s]; rewrite ?liftv0 ?lift0.
Qed.

Lemma wfx_weak : forall e1 e2 x,
  wfx (e1;`e2) (liftx #e2 #e1 x) = wfx e1 x.
Proof.
move=> e1 e2 x; elim: e2 => [|[k t] e2 <-] /=; first by rewrite liftx0.
rewrite liftxS_hi -size_cat -cat_cons; exact: wfx_weak0.
Qed.

Lemma wfx_subst : forall e1 e2 u x,
  wft e1 u -> wfx (e1,`X <: u;`e2) x -> wfx (e1;`[u]e2) (substx #e2 #e1 u x).
Proof.
move=> e1 e2 u x Hu; elim: x e2 => [j|k s x IHx|x IHx y IHy|x IHx t] e2 /=.
- by rewrite wfv_subst wfv_widen; case: eqP.
- case/andP=> Hs; rewrite (wft_subst Hu Hs) -cat_cons; exact: IHx.
- by move/andP=> [Hx Hy]; apply/andP; auto.
by move/andP=> [Hx Ht]; rewrite (wft_subst Hu Ht) IHx.
Qed.

Lemma wfx_subst0 : forall e u x,
  wft e u -> wfx (e,`X <: u) x -> wfx e (substx 0 #e u x).
Proof. move=> e; exact: wfx_subst nil. Qed.

Lemma substx_lift : forall h i u x, substx h i u (liftx 1 i x) = x.
Proof.
move=> h i u x; elim: x h => [j|k s x IHx|y IHy x IHx|x IHx t] h /=.
- by rewrite neq_liftv lift1v_inv.
- by rewrite IHx subst_lift.
- by rewrite IHx IHy.
by rewrite IHx subst_lift.
Qed.

Lemma wfx_subsx : forall e1 e2 t z x,
  wfx e1 z -> wfx (e1,`[X : t];`e2) x -> wfx (e1;`e2) (subsxx #e2 #e1 z x).
Proof.
move=> e1 e2 t z x Hz; elim: x e2 => [i|k s x IHx|x IHx y IHy|x IHx s] e2 /=.
- by case Hi: (i == _); rewrite ?wfx_weak // -{1}(lowerv_inv Hi) wfv_weak1.
- move/andP=> [Hs Ht]; rewrite (wft_lower Hs) -!cat_cons.
  by apply: IHx; rewrite /= (lower_inv Hs).
- by move/andP=> [Hx Hy]; rewrite IHx // IHy.
by move/andP=> [Hx Ht]; rewrite (wft_lower Ht) IHx.
Qed.

Lemma wfx_subsx0 : forall e t z x,
  wfx e z -> wfx (e,`X : t) x -> wfx e (subsxx 0 #e z x).
Proof. move=> e; exact: wfx_subsx nil. Qed.

Lemma subsxx_lift : forall h i u x, subsxx h i u (liftx 1 i x) = x.
Proof.
move=> h i u x; elim: x h => [j|b s x IHx|x IHx y IHy|x IHx s] h /=.
- by rewrite neq_liftv lift1v_inv.
- by rewrite lift1_inv IHx.
- by rewrite IHx IHy.
by rewrite lift1_inv IHx.
Qed.

(* Type-checking algorithm. We use an approximation of the subtype predicate, *)
(* coerce, to define a "typeof" function, which combines with the subtype    *)
(* predicate to give both typing and well-typing predicates.                  *)

Fixpoint coerce (e : env) (t : type) {struct e} : type :=
  if t is Tvar i then 
    if e is e',`_ ~: s then lift 1 #e' (coerce e' (if i == #e' then s else t))
    else Top
  else t.

Inductive non_tvar : type -> Set :=
  | NtvarTop : non_tvar Top
  | NtvarProd : forall k s t, non_tvar (Prod k s t).

Lemma coerceP : forall e t, non_tvar (coerce e t).
Proof.
elim=> [|[_ s] e IHt] [] /=; try by constructor.
by move=> i; case: IHt=> /=; constructor.
Qed.

Lemma wf_coerce : forall e t, wfe e -> wft e t -> wft e (coerce e t).
Proof.
elim=> [|[k s] e IHe] //= [] //= i; move/andP=> [He Hs].
rewrite wft_weak0; case: (i == _) => // Hi; exact: IHe.
Qed.

Lemma coerce_overlift : forall h e i,
  coerce e (Tvar (liftv h #e i)) = coerce e (Tvar i).
Proof.
move=> h e i; rewrite /liftv; case: leqP => //; elim: e => [|[k s] e IHe] //= Hi.
rewrite {1}addnC -{2 4}(addn0 #e) -{1 3}(subnKC Hi) -addnA !addSnnS !eqn_add2l.
by rewrite /= IHe // ltnW.
Qed.

Lemma coerce_weak0 : forall e d t,
  coerce (e,`d) (lift 1 #e t) = lift 1 #e (coerce e t).
Proof.
move=> e [k s]; case; try by case e.
by move=> i /=; rewrite neq_liftv coerce_overlift.
Qed.

Lemma coerce_def : forall e t,
  coerce e t = if t is Tvar i then coerce e (lookup e i) else t.
Proof.
elim=> // [[k s] e IHe]; case=> // [i].
by rewrite [lookup _ _]/= coerce_weak0 /=; case: (i == _) => //; rewrite IHe.
Qed.

Lemma coerce_weak1 : forall e1 e2 u t,
  coerce (e1,`[u];`e2) (lift 1 #e1 t) = lift 1 #e1 (coerce (e1;`e2) t).
Proof.
move=> e1 e2 u; elim: e2 => [|[k s] e2 IHe]; first exact: coerce_weak0.
case=> //= i; rewrite -[Tvar _]/(lift 1 #e1 (Tvar i)) -(fun_if (lift 1 _)) IHe.
rewrite !size_cat size_map liftC_addl /= -addSnnS; do 2 congr lift.
by rewrite -(add1n #e2) -liftvT eq_liftv2.
Qed.

Lemma coerce_weak : forall e1 e2 t,
  coerce (e1;`e2) (lift #e2 #e1 t) = lift #e2 #e1 (coerce e1 t).
Proof.
move=> e1 e2 t; elim: e2 => [|[k s] e2 IHe]; first by rewrite /= !lift0.
by rewrite [#(_,`_)]/= !(liftS_hi #e2) -size_cat cat_cons coerce_weak0 IHe.
Qed.

Lemma coerce_weak_eq : forall e1 e2 h t, h = #e2 -> 
  coerce (e1;`e2) (lift h #e1 t) = lift h #e1 (coerce e1 t).
Proof. move=> e1 e2 h t ->; exact: coerce_weak. Qed.

Lemma coerce_subst : forall e1 e2 u t,
  coerce (e1;`[u]e2) (subst #e2 #e1 u t)
     = subst #e2 #e1 u (coerce (e1,`X <: u;`e2) t).
Proof.
move=> e1 e2 u; elim: e2 => [|[k2 t2] e2 IHe] [];
  first [by move=> *; rewrite !coerce_def | move=> i].
- rewrite /= subst_lift lift0 !coerce_def; case Hi: (i == _) => //.
  by rewrite -{2}(lowerv_inv Hi) lookup_overlift.
case Hi: (i == #e1).
  rewrite [coerce]lock /= -!cat_cons -{2}lock coerce_def -lock lookup_widen Hi.
  rewrite -cat_rcons !coerce_weak_eq /= ?size_subste ?size_rcons //.
  by rewrite (liftS_lo (S _)) subst_lift.
rewrite /= Hi /= eq_lowerv !size_cat size_subste /= liftvT Hi add0n.
rewrite -addSnnS -{1 3}(add1n #e2).
by case: (i == _); rewrite -lift_subst_addl -IHe //= Hi.
Qed.

Lemma coerce_subst0 : forall e u t,
  coerce e (subst 0 #e u t) = subst 0 #e u (coerce (e,`X <: u) t).
Proof. move=> e; exact: coerce_subst nil. Qed.

Lemma coerce_refl : forall e t, subtype e t (coerce e t).
Proof.
elim=> [|[k' t'] e IHe] [i||k s t] //; rewrite coerce_def.
apply: subtype_trans (subtype_var _ _) _.
rewrite [lookup _ _]/= coerce_weak0; exact: subtype_weak0.
Qed.

Lemma coerce_nvar : forall e t1 t2,
  non_tvar t2 -> subtype e t1 t2 -> subtype e (coerce e t1) t2.
Proof.
move=> e t1 _ [|k2 s2 t2] //= [n]; elim: n t1 => // [n IHn] t1 Hn.
by move/Subtype: Hn (Hn); rewrite /= coerce_def; case t1; auto.
Qed.

Lemma coerce_subtype : forall e t1 t2,
  subtype e t1 t2 -> subtype e (coerce e t1) (coerce e t2).
Proof.
move=> e t1 t2 Ht; apply: coerce_nvar; first exact: coerceP.
apply: subtype_trans Ht _; exact: coerce_refl.
Qed.

Lemma coerce_narrow : forall e1 e2 k t1 t2 t3, subtype e1 t1 t2 ->
  let e := e1,`k ~: t2;`e2 in
  subtype e (coerce (e1,`k ~: t1;`e2) t3) (coerce e t3).
Proof.
move=> e1 e2 k t1 t2 t3 Ht12 /=; elim: e2 t3 => [|[k2 u2] e2 IHe] t3;
  rewrite !coerce_def; case: t3 => [i||k3 s3 t3]; try exact: subtype_refl;
  rewrite ?cat0s ?cat_cons /lookup -/lookup !coerce_weak0.
- apply: subtype_weak0; apply: coerce_subtype.
  case: (i == _) => //; exact: subtype_refl.
have ->:  #(e1,`k ~: t1;`e2) = #(e1,`k ~: t2;`e2) by rewrite !size_cat.
by apply: subtype_weak0; case: (i == _) (IHe (Tvar i)); rewrite // !coerce_def.
Qed.

Lemma coerce_narrow0 : forall e k t1 t2 t3, subtype e t1 t2 ->
  subtype (e,`k ~: t2) (coerce (e,`k ~: t1) t3) (coerce (e,`k ~: t2) t3).
Proof. move=> e; exact: coerce_narrow nil. Qed.

(*
Definition codom e t := if coerce e t is Prod _ _ t' then t' else Top.
*)

Fixpoint typeof (e : env) (x : expr) {struct x} : type :=
  match x with
  | Var i =>
    lookup e i
  | Fun k t x' =>
    Prod k t (typeof (e,`k ~: t) x')
  | App x' _ =>
    if coerce e (typeof e x') is Prod Kvalue _ t then lower #e t else Top
  | Tapp x' u =>
    if coerce e (typeof e x') is Prod Ktype _ t then subst 0 #e u t else Top
  end.

Lemma wf_typeof : forall e x, wfe e -> wfx e x -> wft e (typeof e x).
Proof.
move=> e x; elim: x e => [i|b s x IHx|x IHx y _|x IHx t] e He /=.
- clear 1; exact: wft_lookup.
- by case/andP=> Hs; rewrite Hs; apply: IHx => /=; rewrite He.
- move/andP=> [Hx _]; move: (wf_coerce He (IHx e He Hx)).
  case: coerceP => //= [[] // s t]; case/andP=> _; exact: wft_lower0.
move/andP=> [Hx Ht]; move: (wf_coerce He (IHx e He Hx)).
case: coerceP => //= [[] // s' t']; rewrite -(wft_widen0 t).
case/andP=> _; exact: wft_subst0.
Qed.

Lemma typeof_weak1 : forall e1 e2 d x,
  typeof (e1,`[d];`e2) (liftx 1 #e1 x) = lift 1 #e1 (typeof (e1;`e2) x).
Proof.
move=> e1 e2 d x; elim: x e2 => [i|k t x IHx|x IHx _ _|x IHx t] e2 /=.
- exact: lookup_weak1.
- by rewrite -!cat_cons -IHx.
- rewrite IHx coerce_weak1; case: coerceP => // [[] // s t].
  by rewrite /lower !size_cat size_map /= addnS lift_subst_leq ?leq_addl.
rewrite IHx coerce_weak1; case: coerceP => // [[] // s t'].
by rewrite !size_cat size_map /= addnS lift_subst_leq ?leq_addl.
Qed.

Lemma typeof_weak0 : forall e u x,
  typeof (e,`u) (liftx 1 #e x) = lift 1 #e (typeof e x).
Proof. move=> e; exact: typeof_weak1 nil. Qed.

Lemma typeof_weak : forall e1 e2 x,
  typeof (e1;`e2) (liftx #e2 #e1 x) = lift #e2 #e1 (typeof e1 x).
Proof.
move=> e1 e2 x; elim: e2 => [|[k t] e2 IHe] /=; first by rewrite liftx0 lift0.
by rewrite liftS_hi liftxS_hi -size_cat typeof_weak0 IHe.
Qed.

Lemma typeof_subst : forall e1 e2 u x,
    wfe (e1,`X <: u;`e2) -> wfx (e1,`X <: u;`e2) x ->
  typeof (e1;`[u]e2) (substx #e2 #e1 u x)
    = subst #e2 #e1 u (typeof (e1,`X <: u;`e2) x).
Proof.
move=> e1 e2 u x; elim: x e2 => [i|k s x IHx|x IHx y IHy|x IHx t] /= e2 He.
- rewrite wfv_widen; case Hi: (i == #e1) => // _.
  by rewrite lookup_subst lowerv_inv.
- rewrite -!cat_cons; move/andP=> [Hks Hkx]; congr Prod.
  by apply: (IHx (_,`_ ~: _)) Hkx => //=; rewrite He.
- move/andP=> [Hkx Hky]; rewrite IHx // coerce_subst.
  have:= wf_coerce He (wf_typeof He Hkx).
  case: coerceP => //= [[] // s t]; move/andP=> [_ Hkt].
  rewrite -{1}(lower_inv0 Hkt) !size_cat /= size_subste -addSnnS.
  by rewrite -{1}(add1n #e2) -lift_subst_addl lift1_inv.
move/andP=> [Hkx Hkt]; rewrite IHx // coerce_subst.
case: coerceP => //= [[] // _ t'].
by rewrite !size_cat /= size_subste -addSnnS substC_addl.
Qed.

Lemma typeof_subst0 : forall e u x,
  wfe e -> wft e u -> wfx (e,`X <: u) x ->
  typeof e (substx 0 #e u x) = subst 0 #e u (typeof (e,`X <: u) x).
Proof. by move=> e u x He Hu; apply: (@typeof_subst e nil); rewrite /= He. Qed.

Lemma typeof_subsx : forall e1 e2 z x,
    wfe (e1,`[X : typeof e1 z];`e2) -> wfx (e1,`[X : typeof e1 z];`e2) x ->
  typeof (e1;`e2) (subsxx #e2 #e1 z x)
    = lower #e1 (typeof (e1,`[X : typeof e1 z];`e2) x).
Proof.
move=> e1 e2 z x; set u := typeof e1 z.
elim: x e2 => [i|k s x IHx|x IHx y _|x IHx t] /= e2 He.
- case Hi: (i == #e1) => /= _.
    by rewrite typeof_weak lookup_widen Hi liftS_lo lift1_inv size_map.
  by rewrite -{2}(lowerv_inv Hi) lookup_weak1 lift1_inv.
- move/andP=> [Hks Hkx]; move: (Hks); rewrite -{1 5}(lower_inv Hks) {Hks}.
  rewrite /lower /= -[1]/(0 + 1) subst_add => Hks; congr Prod.
  apply: IHx (_,`_) _ _; first by rewrite /= He.
  by rewrite /= wfx_widen0 -(wfx_widen0 _ _ s).
- move/andP=> [Hkx _]; rewrite {IHx}(IHx _ He Hkx).
  rewrite -{2}(lower_inv (wf_typeof He Hkx)) coerce_weak1.
  case: coerceP => //= [[] // _ t]; rewrite !size_cat /= size_map addnS.
  Check canRL. Check lift1_inv.
  by apply: canRL _ (lift1_inv _) _; rewrite /lower lift_subst_leq // leq_addl.
move/andP=> [Hkx Hkt]; rewrite {IHx}(IHx _ He Hkx).
rewrite -{2}(lower_inv (wf_typeof He Hkx)) coerce_weak1.
case: coerceP => //= [[] // _ t']; rewrite !size_cat /= size_map addnS.
apply: canRL _ (lift1_inv _) _; rewrite lift_subst_leq ?leq_addl //.
congr subst; exact: lower_inv Hkt.
Qed.

Lemma typeof_subsx0 : forall e z x,
    wfe e -> wfx e z -> wfx (e,`X : typeof e z) x ->
  typeof e (subsxx 0 #e z x) = lower #e (typeof (e,`X : typeof e z) x).
Proof.
move=> e z x He Hkz; apply: (@typeof_subsx _ nil).
rewrite /= He; exact: wf_typeof.
Qed.

Fixpoint typed (e : env) (x : expr) {struct x} : Prop :=
  match x with
  | Var _ => True
  | Fun k s x' => typed (e,`k ~: s) x'
  | App x' y =>
    if coerce e (typeof e x') is Prod Kvalue s _ then
       and3 (typed e x') (typed e y) (subtype e (typeof e y) s)
    else False
  | Tapp x' u =>
    if coerce e (typeof e x') is Prod Ktype s _ then
       typed e x' /\ subtype e u s
    else False
  end.

Lemma typeof_narrow : forall e1 e2 k t1 t2 x,
  subtype e1 t1 t2 -> wft e1 t1 -> 
  let e := e1,`k ~: t2;`e2 in wfe e -> wfx e x -> typed e x ->
  subtype e (typeof (e1,`k ~: t1;`e2) x) (typeof e x).
Proof.
move=> e1 e2 k1 t1 t2 x Ht Ht1 /=.
elim: x e2 => [i|k s x IHx|x IHx y _|x IHx t] /= e2 He.
- clear 2; exact: lookup_narrow.
- move/andP=> [Hs Hkx] Hx; apply: subtype_prod => //.
  by apply: (IHx (_,`k ~: s)); rewrite /= ?He.
- move/andP=> [Hkx _] Hx; have{IHx} := coerce_subtype (IHx _ He Hkx _); move: Hx.
  have:= wf_coerce He (wf_typeof He Hkx).
  case: coerceP => //= [[] // s4 t4]; move/andP=> [_ Ht4] [Hx _ _] Hxt4.
  case: {Hxt4 Hx}(subtype_trans (coerce_narrow _ _ _ Ht) (Hxt4 Hx)); case=> // n.
  have He': wfe (e1,`k1 ~: t1;`e2).
    by rewrite wfe_widen Ht1 andbT; rewrite wfe_widen in He; case/andP: He.
  have Hkx' : wfx (e1,`k1 ~: t1;`e2) x.
    by rewrite wfx_widen; rewrite wfx_widen in Hkx.
  have:= wf_coerce He' (wf_typeof He' Hkx').
  case: coerceP => [|[] s3 t3] //=; move/andP=> [_ Ht3]; case/andP=> _.
  have ->: #(e1,`k1 ~: t1;`e2) = #(e1,`k1 ~: t2;`e2) by rewrite !size_cat.
  move/Subtype; apply: subtype_strengthen => //.
  by rewrite -(wft_widen0 s3) -cat_cons -(wft_widen t1).
move/andP=> [Hkx _]; have{IHx} := coerce_subtype (IHx _ He Hkx _).
have:= wf_coerce He (wf_typeof He Hkx).
case: coerceP => //= [[] // s4 t4]; move/andP=> [_ Ht4] Hxt4 [Hx Hts4].
case: {Hxt4 Hx}(subtype_trans (coerce_narrow _ _ _ Ht) (Hxt4 Hx)); case=> // n.
have He': wfe (e1,`k1 ~: t1;`e2).
  by rewrite wfe_widen Ht1 andbT; rewrite wfe_widen in He; case/andP: He.
have Hkx' : wfx (e1,`k1 ~: t1;`e2) x.
  by rewrite wfx_widen; rewrite wfx_widen in Hkx.
have:= wf_coerce He' (wf_typeof He' Hkx').
case: coerceP => [|[] s3 t3] //=; move/andP=> [_ Ht3]; case/andP=> _.
have ->: #(e1,`k1 ~: t1;`e2) = #(e1,`k1 ~: t2;`e2) by rewrite !size_cat.
move/Subtype; move/(subtype_narrow0 Hts4); exact: subtype_subst0.
Qed.

Lemma typeof_narrow0 : forall e k t1 t2 x,
  subtype e t1 t2 ->
  wfe e -> wft e t1 -> wft e t2 -> wfx (e,`k ~: t2) x -> typed (e,`k ~: t2) x ->
  subtype (e,`k ~: t2) (typeof (e,`k ~: t1) x) (typeof (e,`k ~: t2) x).
Proof.
move=> e k t1 t2 x Ht He Ht1 Ht2.
by apply: (@typeof_narrow _ nil); rewrite //= He.
Qed.

Lemma typed_weak1 : forall e1 e2 x d,
  typed (e1;`e2) x -> typed (e1,`[d];`e2) (liftx 1 #e1 x).
Proof.
move=> e1 e2 x d; elim: x e2 => //= [k s x IHx|x IHx y IHy|x IHx t] e2.
- exact: IHx (_,`_).
- rewrite !typeof_weak1 coerce_weak1; case: coerceP => //= [[] // s t] [Hx Hy Hs].
  split; auto; exact: subtype_weak1.
rewrite typeof_weak1 coerce_weak1; case: coerceP => //= [[] // s _] [Hx Hs].
split; auto; exact: subtype_weak1.
Qed.

Lemma typed_weak0 : forall e x d, typed e x -> typed (e,`d) (liftx 1 #e x).
Proof. move=> e; exact: typed_weak1 nil. Qed.

Definition typecheck e x t :=
  and5 (wfe e) (wfx e x) (wft e t) (subtype e (typeof e x) t) (typed e x).

(* Lemmas A.4 and A.5.3 / A.5.4 combined *)
Lemma typecheck_weak1 : forall e1 e2 k1 u1 x t,
  wft e1 u1 -> typecheck (e1;`e2) x t ->
  typecheck (e1,`[k1 ~: u1];`e2) (liftx 1 #e1 x) (lift 1 #e1 t).
Proof.
move=> e1 e2 k1 u1 x t Hku1 [He Hkx Hkt Ht Hx].
split; first by rewrite wfe_weak1 // He.
- by rewrite wfx_weak1.
- by rewrite wft_weak1.
- rewrite typeof_weak1; exact: subtype_weak1.
exact: typed_weak1.
Qed.

(* Lemmas A.5.3 and A.5.4 *)
Lemma typecheck_weak0 : forall e k u x t,
  wft e u -> typecheck e x t -> typecheck (e,`k ~: u) (liftx 1 #e x) (lift 1 #e t).
Proof. move=> e; exact: typecheck_weak1 nil. Qed.

(* Lemma A.5.6 *)
Lemma typecheck_weak : forall e1 e2 x t,
  typecheck e1 x t -> wfe (e1;`e2) ->
  typecheck (e1;`e2) (liftx #e2 #e1 x) (lift #e2 #e1 t).
Proof.
move=> e1 e2 x t Hx; elim: e2 => [|[k u] e IHe] /=; first by rewrite liftx0 lift0.
move/andP=> [He Hku]; rewrite liftxS_hi liftS_hi -!size_cat.
apply: typecheck_weak0 Hku _; exact: IHe.
Qed.

(* Lemma A.7 (depends on Lemma A.10!) *)

Lemma typecheck_narrow : forall e1 e2 k t1 t2 t3 x,
    subtype e1 t1 t2 -> wft e1 t1 ->
  typecheck (e1,`k ~: t2;`e2) x t3 -> typecheck (e1,`k ~: t1;`e2) x t3.
Proof.
move=> e1 e2 k t1 t2 t3 x Ht12 Hkt1; case.
rewrite wfe_widen -(wft_widen t1) wfx_widen.
move/andP=> [He Hkt2] Hkx Hkt3 Hxt3 Hx.
rewrite /typecheck wfe_widen wfx_widen He; split=> {Hkt3}//.
  apply: subtype_narrow (Ht12) _; apply: subtype_trans Hxt3.
  by apply: typeof_narrow; rewrite // ?wfx_widen // wfe_widen He.
elim: x e2 {t3 Hxt3} He Hkx Hx => //= [k' s x IHx|x IHx y IHy|x IHx t] e2 He.
- by move/andP=> [Hks Hkx]; apply: (IHx (e2,`k' ~: s)); rewrite //= He.
- move/andP=> [Hkx Hky]; have Het2: wfe (e1,`k ~: t2;`e2) by rewrite wfe_widen He.
  have He12 := typeof_narrow Ht12 Hkt1 Het2.
  have Hk2x : wfx (e1,`k ~: t2;`e2) x by rewrite wfx_widen.
  have Hk2y : wfx (e1,`k ~: t2;`e2) y by rewrite wfx_widen.
  have:= subtype_trans (coerce_narrow _ _ _ Ht12) (coerce_subtype (He12 _ Hk2x _)).
  case: (coerceP (e1,`k ~: t2;`e2)) => // [[] //= s4 t4] Hs43 [Hx Hy Hys4].
  case: {Hs43}(Hs43 Hx) => [[|n] //]; case: coerceP => // [[] //= s3 t3].
  case/andP; move/Subtype=> Hs43 _ {t3 t4}; split; eauto. 
  by apply: subtype_narrow Ht12 _; move: subtype_trans; eauto.
move/andP=> [Hkx Hkt]; have Het2: wfe (e1,`k ~: t2;`e2) by rewrite wfe_widen He.
have He12 := typeof_narrow Ht12 Hkt1 Het2.
have Hk2x : wfx (e1,`k ~: t2;`e2) x by rewrite wfx_widen.
have:= subtype_trans (coerce_narrow _ _ _ Ht12) (coerce_subtype (He12 _ Hk2x _)).
case: (coerceP (e1,`k ~: t2;`e2)) => // [[] //= s4 t4] Hs43 [Hx Hts4].
case: {Hs43}(Hs43 Hx) => [[|n] //]; case: coerceP => // [[] //= s3 t3].
case/andP; move/Subtype=> Hs43 _ {t3 t4}; split; eauto. 
apply: subtype_narrow Ht12 _; move: subtype_trans; eauto.
Qed.

Lemma typecheck_narrow0 : forall e k t1 t2 t3 x,
  subtype e t1 t2 -> wft e t1 ->
  typecheck (e,`k ~: t2) x t3 -> typecheck (e,`k ~: t1) x t3.
Proof. move=> e; exact: typecheck_narrow nil. Qed.

(* Lemma A.11 *)

Lemma typecheck_subst : forall e1 e2 u1 u2 x t,
    subtype e1 u1 u2 -> wft e1 u1 -> typecheck (e1,`X <: u2;`e2) x t ->
  typecheck (e1;`[u1]e2) (substx #e2 #e1 u1 x) (subst #e2 #e1 u1 t).
Proof.
move=> e1 e2 u1 u2 x t Hu Hku1.
move/(typecheck_narrow Hu Hku1)=> [He Hkx Hkt Hxt Hx]; split.
- exact: wfe_subst.
- exact: wfx_subst.
- exact: wft_subst.
- rewrite (typeof_subst He Hkx); exact: subtype_subst.
move: u1 Hku1 He Hkx Hx {u2 t Hu Hkt Hxt} => u Hku.
elim: x e2 => //= [k' s x IHx|x IHx y IHy|x IHx t] e2 He.
- by rewrite -!cat_cons; case/andP=> Hks; apply: IHx => //=; rewrite He.
- move/andP=> [Hkx Hky]; rewrite (typeof_subst He Hkx) coerce_subst.
  case: coerceP => //= [[] // s t] [Hx Hy Hys]; split; eauto.
  rewrite (typeof_subst He Hky); exact: subtype_subst.
move/andP=> [Hkx _]; rewrite (typeof_subst He Hkx) coerce_subst.
case: coerceP => //= [[] // s t'] [Hx Ht]; split; eauto; exact: subtype_subst.
Qed.

Lemma typecheck_subst0 : forall e u1 u2 x t, subtype e u1 u2 ->
    wft e u1 -> typecheck (e,`X <: u2) x t ->
  typecheck e (substx 0 #e u1 x) (subst 0 #e u1 t).
Proof. move=> e; exact: typecheck_subst nil. Qed.

Lemma typecheck_subsxx0 : forall e z x s t,
  typecheck e z s -> typecheck (e,`X : s) x (lift 1 #e t) ->
  typecheck e (subsxx 0 #e z x) t.
Proof.
move=> e z x s t [He Hkz _ Hzs Hz]; have Hktz := wf_typeof He Hkz.
case/(typecheck_narrow0 Hzs Hktz)=> [He' Hkx Hkt Hxt Hx].
rewrite wft_weak0 {s Hzs} in Hkt.
split=> //; first exact: wfx_subsx0 Hkx.
  rewrite (typeof_subsx0 He) // -(lift1_inv #e t).
  by apply: subtype_strengthen _ _ Hxt; [exact: wf_typeof | rewrite wft_weak0].
move: He' Hkx Hx {t Hkt Hxt}; rewrite -{7}(cat0s e); set e' := nil.
rewrite -[e,`_]/(e,`[X : typeof e z];`e') -{4}[0]/#e'.
elim: x e' => //= [i|k s x IHx|x IHx y IHy|x IHx t] e2 He2.
- case: eqP => //; case: (@typecheck_weak e e2 z Top) => //.
  by move: (He2); rewrite wfe_weak1 //; case/andP.
- move/andP=> [Hks Hkx]; rewrite -{1}(lower_inv Hks).
  by apply: IHx (_,`k ~: _) _ _; rewrite /= ?He2 (lower_inv Hks).
- move/andP=> [Hkx Hky]; rewrite (typeof_subsx He2 Hkx).
  rewrite -{1}(lower_inv (wf_typeof He2 Hkx)) coerce_weak1.
  case: coerceP => //= [[] // s _] [Hx Hy Hys]; split; eauto.
  rewrite -(lower_inv (wf_typeof He2 Hky)) in Hys; case: Hys => n.
  rewrite (typeof_subsx He2 Hky) nsubtype_weak1; exact: Subtype.
move/andP=> [Hkx Hkt]; rewrite (typeof_subsx He2 Hkx).
rewrite -{1}(lower_inv (wf_typeof He2 Hkx)) coerce_weak1.
case: coerceP => //= [[] // s _] [Hx Hts]; split; eauto.
rewrite -(lower_inv Hkt) in Hts; exact: subtype_unweak Hts.
Qed.

(* Subtyping rules that enforce well-formedness. *)

Definition wfsubtype e t1 t2 :=
  and4 (wfe e) (wft e t1) (wft e t2) (subtype e t1 t2).

Lemma wfsubtype_top : forall e t, wfe e -> wft e t -> wfsubtype e t Top.
Proof. by split. Qed.

Lemma wfsubtype_refl : forall e t, wfe e -> wft e t -> wfsubtype e t t.
Proof. by split. Qed.

Lemma wfsubtype_tvar : forall e i t,
  wfv e i Ktype -> wfsubtype e (lookup e i) t -> wfsubtype e (Tvar i) t.
Proof. by move=> e i t Hi [Hke _ Hkt]; split; eauto. Qed.

Lemma wfsubtype_prod : forall e k s1 t1 s2 t2,
    wfsubtype e s2 s1 -> wfsubtype (e,`k ~: s2) t1 t2 ->
  wfsubtype e (Prod k s1 t1) (Prod k s2 t2).
Proof.
move=> e k s1 t1 s2 t2 [He Hks2 Hks1 Hs] [_ Hkt1 Hkt2 Ht].
by split; auto; rewrite /= ?Hks2 ?Hks1 -1?(wft_widen0 s2).
Qed.

(* Type-checking rules *)

Lemma typecheck_var : forall e i t,
  typecheck e (Var i) t <-> wfv e i Kvalue /\ wfsubtype e (lookup e i) t.
Proof.
by split; [case; repeat split; try exact: wft_lookup | case=> Hki; case; split].
Qed.

Lemma typecheck_subsume : forall e x t1 t2,
  wfsubtype e t1 t2 -> typecheck e x t1 -> typecheck e x t2.
Proof. move=> e x t1 t2 [_ _ Hkt2 Ht12]; case; split; eauto. Qed.

Lemma typecheck_fun : forall e k s x t,
  typecheck e (Fun k s x) t
    <->  exists2 t', typecheck (e,`k ~: s) x t' & wfsubtype e (Prod k s t') t.
Proof.
move=> e k s x t; split; case=> /=.
  move=> He; move/andP=> [Hks Hkx] Hkt Ht Hx.
  by exists (typeof (e,`k ~: s) x); split; rewrite /= ?Hks ?He //=; 
    apply: wf_typeof; rewrite /= ?Hks ?He //=. 
move=> t' [] /=; move/andP=> [Hke Hks] Hkx _ Hs Hx [_ _ Hkt Ht].
by split; rewrite //= ?Hks ?Hks' //; eauto.
Qed.

Lemma typecheck_app : forall e x y t,
  typecheck e (App x y) t
  <->  exists2 s, typecheck e x (Prod Kvalue s (lift 1 #e t)) & typecheck e y s.
Proof.
move=> e x y t; split; case=> /=.
  move=> He; move/andP=> [Hkx Hky] Hkt; have:= coerce_refl e (typeof e x).
  have:= wf_coerce He (wf_typeof He Hkx). 
  case: coerceP => // [[] s1 t1] //=; move/andP=> [Hks1 Hkt1] Hx1 Ht1 [Hx Hy Hs1].
  exists s1; split=> //=; first by rewrite Hks1 wft_weak0.
  apply: subtype_trans Hx1 _; have:= subtype_weak0 (Kvalue ~: s1) Ht1.
  by rewrite (lower_inv0 Hkt1); eauto.
move=> s [He Hkx] /=; move/andP=> [Hks Hkt] Hxt Hx [_ Hky _ Hys Hy].
rewrite /typecheck /= Hkx -(wft_weak0 e (Kvalue ~: s)).
case: (coerce_nvar _ Hxt) => [|[|n1] //]; first right.
have:= wf_coerce He (wf_typeof He Hkx).
case: coerceP => // [[] //= s1 t1]; move/andP=> [_ Hkt1]; case/andP.
move/Subtype=> Hs1; move/Subtype; rewrite -(wft_widen0 s) in Hkt1.
by move/(subtype_strengthen Hkt1 Hkt); rewrite lift1_inv; do 2 split=> //; eauto.
Qed.

Lemma typecheck_tapp : forall e x u t,
  typecheck e (Tapp x u) t
  <->  exists2 t', typecheck e x (Prod Ktype u t') 
                 & wfsubtype e (subst 0 #e u t') t.
Proof.
move=> e x u t; split; case=> /=.
  move=> He; move/andP=> [Hkx Hku] Hkt; have:= coerce_refl e (typeof e x).
  have:= wf_coerce He (wf_typeof He Hkx). 
  case: coerceP => // [[] s1 t1] //=; move/andP=> [_ Hkt1] Hx1 Ht1 [Hx Hus1].
  have Hkt1': wft (e,`X <: u) t1 by rewrite -(wft_widen0 s1).
  by have:= wft_subst0 Hku Hkt1'; exists t1; split=> //=; eauto; rewrite Hku.
move=> t1 [Hke Hkx /=]; move/andP=> [Hku Hkt1] Hxt1 Hx [_ _ Hkt].
case: {Hxt1}(coerce_nvar _ Hxt1) => [|[|n] //]; first right.
rewrite /typecheck /= Hkx.
case: coerceP => // [[] //= s2 t2]; case/andP; move/Subtype=> Hs2.
move/Subtype; move/(@subtype_subst _ nil) => /= Ht.
by move/(subtype_trans Ht) {Ht}=> Ht; repeat split.
Qed.

(* Evaluation contexts. We evaluate under prenex type binders, as this allows *)
(* for a straightforward embedding of the simply typed lambda calculus.       *)
(* Thus our evaluation contexts consist of an applicative context together    *)
(* with a type environment, and we distinguish between values, which stop     *)
(* applicative evaluation, and answers, which stop global evaluation. Note    *)
(* that answers are just type-abstracted function values.                     *)

Definition value x := if x is Fun _ _ _ then true else false.

Fixpoint answer (x : expr) : bool :=
  if x is Fun k _ x' then if k is Kvalue then true else answer x' else false.

Fixpoint valid_ctx_expr (i : nat) (x : expr) {struct x} : bool :=
  match x with
  | Var j => j == i
  | Fun _ _ _ => false
  | App x' y => if negb (value x') then valid_ctx_expr i x' else valid_ctx_expr i y
  | Tapp x' _ => valid_ctx_expr i x'
  end.

Identity Coercion seq_of_env : env >-> seq.

Fixpoint valid_ctx_env (e : env) : bool :=
  if e is e',`X <: _ then valid_ctx_env e' else nil == e.

Lemma wfv_ctx : forall e i, valid_ctx_env e -> wfv e i Kvalue = false.
Proof.
by move=> e i; elim: e => // [[[] //= _] e IHe] He; rewrite IHe ?if_same.
Qed.

Record ctx : Type := Ctx {ctx_env :> env; ctx_expr :> expr}.

Definition valid_ectx (c : ctx) := valid_ctx_env c && valid_ctx_expr #c c.

(* Splitting a term into a context/redex pair. *)

(* Applicative context. *)

Fixpoint actx (i : nat) (x : expr) {struct x} : expr :=
  match x with
  | App x' y =>
    if negb (value x') then App (actx i x') (liftx 1 i y) else
    if negb (value y) then App (liftx 1 i x') (actx i y) else Var i
  | Tapp x' t =>
    if negb (value x') then Tapp (actx i x') (lift 1 i t) else Var i
  | _ => Var i
  end.

Lemma actx_valid : forall i x, valid_ctx_expr i (actx i x).
Proof.
move=> i; elim=> [j|b s x _|x IHx y IHy|x IHx t];
  rewrite /= ?(fun_if (valid_ctx_expr i)) /= ?eqxx // {}IHx ?{}IHy ?if_same //.
by case: x => *; rewrite //= ?(fun_if value) /= ?if_same.
Qed.

Lemma wfx_actx : forall k s x, wfx k x -> wfx (k,`X : s) (actx #k x).
Proof.
move=> k' s'; elim=> [j|k s x _|x IHx y IHy|x IHx t] /=; rewrite ?eqxx //.
  move/andP=> [Hx Hy]; rewrite !(fun_if (wfx _)) /= !wfx_weak0 eqxx.
  by rewrite IHx Hx // IHy Hy // !if_same.
by move/andP=> [Hx Ht]; case: (negb _); rewrite /= ?eqxx // wft_weak0 IHx.
Qed.

(* Applicative redex. *)

Fixpoint ardx (x : expr) : expr :=
  match x with
  | App x' y =>
    if negb (value x') then ardx x' else
    if negb (value y) then ardx y else x
  | Tapp x' _ =>
    if negb (value x') then ardx x' else x
  | _ => x
  end.

Lemma wfx_ardx : forall e x, wfx e x -> wfx e (ardx x).
Proof.
move=> e; elim=> [i|k s x _|x IHx y IHy|x IHx t] //=.
  by move/andP=> [Hx Hy]; rewrite !(fun_if (wfx e)) /= IHx Hx // IHy Hy ?if_same.
by move/andP=> [Hx Ht]; rewrite (fun_if (wfx e)) /= IHx Hx // Ht if_same.
Qed.

Lemma subs_ardx : forall i x, subsxx 0 i (ardx x) (actx i x) = x.
Proof.
move=> i; elim=> [j|b s x _|x IHx y IHy |x IHx t] /=.
- by rewrite eqxx liftv0.
- by rewrite eqxx lift0 liftx0.
- case: (negb _); first by rewrite /= IHx subsxx_lift.
  by case: (negb _); [ rewrite /= IHy subsxx_lift | rewrite /= eqxx !liftx0].
by case: (negb _); [ rewrite /= IHx lift1_inv | rewrite /= eqxx liftx0 lift0].
Qed.

Lemma typeof_actx : forall e x, wfe e -> wfx e x ->
  typeof (e,`X : typeof e (ardx x)) (actx #e x) = lift 1 #e (typeof e x).
Proof.
move=> e x He; elim: x => [j|b s x _|x IHx y _|x IHx t] /=; try by rewrite eqxx.
  move/andP=> [Hx _]; have:= wf_coerce He (wf_typeof He Hx).
  rewrite [_,`_]lock; case: (negb _).
    rewrite /= -lock IHx // coerce_weak0; case: coerceP => //= [[] // s t].
    by move/andP=> [_ Ht]; rewrite -{1}(lower_inv0 Ht) liftC ?leqnn // lift1_inv.
  case: (negb _); last by rewrite -lock /= eqxx.
  rewrite /= -lock typeof_weak0 coerce_weak0; case: coerceP => //= [[] // s t].
  by move/andP=> [_ Ht]; rewrite -{1}(lower_inv0 Ht) liftC ?leqnn // lift1_inv.
move/andP=> [Hx _]; case: (negb _); last by rewrite /= eqxx.
rewrite [_,`_]lock /= -lock IHx // coerce_weak0.
by case: coerceP => //= [[] // s t']; rewrite lift_subst_leq // leqnn.
Qed.

(* General context. *)

Fixpoint ectx_in (e : env) (x : expr) {struct x} : ctx :=
  if x is Fun Ktype s x' then ectx_in (e,`X <: s) x' else Ctx e (actx #e x).

Definition ectx := ectx_in nil.

Lemma ectx_valid : forall x, valid_ectx (ectx x).
Proof.
move=> x; rewrite /ectx; have: valid_ctx_env nil by done.
elim: x nil => [j|[] s x IHx|x _ y _|x _ t] e He; try exact: IHx;
by rewrite /ectx_in [actx]lock /valid_ectx /= He -lock actx_valid.
Qed.

Definition wfc (c : ctx) := wfe c && wfx (c,`X : Top) c.

Lemma wf_ectx : forall x, wfx nil x -> wfc (ectx x).
Proof.
move=> x; rewrite /ectx; set e := nil; have: wfe e by done.
elim: x e => [j|[] s x IHx|x _ y _|x _ t] e He;  
  try by move/(wfx_actx Top)=> Hx; apply/andP; split.
by rewrite /=; case/andP=> Hs; apply: (IHx (_,`_)); rewrite /= He.
Qed.

(* General redex. *)

Fixpoint rdx (x : expr) : expr := if x is Fun Ktype _ x' then rdx x' else ardx x.

Lemma wfx_rdx : forall x, wfx nil x -> wfx (ectx x) (rdx x).
Proof.
move=> x; rewrite /ectx.
elim: x nil => [i|[] s x IHx|x _ y _|x _ t] e; try exact: wfx_ardx.
case/andP=> _; exact: IHx (_,`_).
Qed.

Lemma typecheck_rdx : forall x t, 
  typecheck nil x t -> typecheck (ectx x) (rdx x) (typeof (ectx x) (rdx x)).
Proof.
move=> x _ [_ Hkx _ _ Hx]; have Hkr := wfx_rdx Hkx.
move/andP: {Hkx}(wf_ectx Hkx) => [He _].
split=> //; first exact: wf_typeof.
rewrite /ectx; move: x nil Hx {Hkr He}.
suff Hardx: forall e x, typed e x -> typed e (ardx x).
  elim=> [i|[] s x IHx|x _ y _|x _ t] e; try exact: Hardx; exact: IHx.
move=> e; elim=> //= [y IHy z IHz|y IHy t].
  case Ds: (coerce _ _) =>  [_||[] s t'] //= [Hy Hz Hzs].
  by do 2 (case: (negb _); auto); rewrite /= Ds; split.
case Ds: (coerce _ _) =>  [_||[] s t'] //= [Hy Hts].
by case: (negb _); auto; rewrite /= Ds; split.
Qed.

(* Iterated abstraction, for typing and substituting in general contexts. *)

Fixpoint nFun (e : env) (x : expr) {struct e} : expr :=
  if e is e',`k ~: s then nFun e' (Fun k s x) else x.

Fixpoint nProd (e : env) (t : type) {struct e} : type :=
  if e is e',`k ~: s then nProd e' (Prod k s t) else t.

Lemma typeof_nFun : forall e x,
  typeof nil (nFun e x) = nProd e (typeof e x).
Proof. by elim=> //= [[k s] e2 IHe] x; rewrite IHe. Qed.

Lemma subtype_nProd : forall e t1 t2,
  subtype e t1 t2 -> subtype nil (nProd e t1) (nProd e t2).
Proof. elim=> //= [[k s] e IHe] t1 t2 Ht12; apply: IHe; exact: subtype_prod. Qed.

Lemma typed_nFun : forall e x, typed e x -> typed nil (nFun e x).
Proof.
by move=> e x; rewrite -{1}(cats0 e); elim: e nil x => // [[k s] e //= IHe]; auto.
Qed.

(* Typing general contexts. *)

Definition ectypeof (c : ctx) s := nProd c (lower #c (typeof (c,`X : s) c)).

Lemma ectypeof_rdx : forall x, wfx nil x ->
  ectypeof (ectx x) (typeof (ectx x) (rdx x)) = typeof nil x.
Proof.
move=> x Hkx; symmetry; rewrite /ectx.
transitivity (nProd nil (typeof nil x)); first done.
move: Hkx; have: wfe nil by done.
elim: x nil => [i|[] k x IHx|x _ y _|x _ t] e He Hkx;
  try (congr nProd; apply: canRL _ (lift1_inv _) _; symmetry; exact: typeof_actx He Hkx).
by case/andP: Hkx=> *; rewrite /= -IHx //= He.
Qed.

Definition ectx_typecheck c s t :=
  and5 (wfc c) (wft c s) (wft nil t)
       (subtype nil (ectypeof c s) t) (typed (c,`X : s) c).

Lemma typecheck_ectx : forall x t,
  typecheck nil x t -> ectx_typecheck (ectx x) (typeof (ectx x) (rdx x)) t.
Proof.
move=> x t [_ Hkx Hkt Hxt Hx].
have Hkc := wf_ectx Hkx; have Hkr := wfx_rdx Hkx; move/andP: (Hkc) => [Hke Hka].
split=> //; first exact: wf_typeof; first by rewrite ectypeof_rdx.
move: x Hke Hkx Hx {t Hxt Hka Hkt Hkc Hkr}.
suff Hactx: forall e x, wfe e -> wfx e x ->
    typed e x -> typed (e,`X : typeof e (ardx x)) (actx #e x).
- move=> x; rewrite /ectx.
  elim: x nil => // [[] s x IHx|x _ y _|x _ t] e; try exact: Hactx.
  rewrite /= => He; case/andP=> Hs; exact: IHx He.
move=> e x He; elim: x => //= [x IHx y IHy|x IHx t]; rewrite [_,`_]lock.
  move/andP=> [Hkx Hky]; case Dt: (coerce _ _) => [_||[] s t] //= [Hx Hy Hys].
  case: (negb _); last case: (negb _);
  rewrite //= -lock typeof_weak0 typeof_actx // coerce_weak0 Dt /=; split;
  first [exact: IHx |  exact: IHy | exact: typed_weak0 | exact: subtype_weak0].
move/andP=> [Hkx Hkt]; case Dt: (coerce _ _) => [_||[] s t'] //= [Hx Hts].
case: (negb _); rewrite //= -lock typeof_actx // coerce_weak0 Dt /=.
split; [exact: IHx | exact: subtype_weak0].
Qed.

(* Context substitution. *)

Definition subsxe x (c : ctx) := nFun c (subsxx 0 #c x c).

Lemma wfx_subsxe : forall c x, wfc c -> wfx c x -> wfx nil (subsxe x c).
Proof.
move=> [e a] /= x; move/andP=> [He Ha] Hx.
move: {Hx Ha}(wfx_subsx0 Hx Ha) He; rewrite /subsxe /=.
elim: e {a x}(subsxx _ _ x a) => //= [[k s] e IHe] x Hx; move/andP=> [He Hs].
by apply: IHe He; rewrite /= Hs.
Qed.

Lemma subs_rdx : forall x, subsxe (rdx x) (ectx x) = x.
Proof.
move=> x; rewrite /ectx /subsxe; transitivity (nFun nil x); last done.
elim: x nil => [j|[] s x IHx|x _ y _|x _ t] e; try exact: IHx (e,`X <: s);
 by congr nFun; exact: subs_ardx.
Qed.

Lemma typecheck_subsxe : forall c s t x,
  ectx_typecheck c s t -> typecheck c x s -> typecheck nil (subsxe x c) t.
Proof.
move=> [e a] s t x; case; rewrite /= /ectypeof /= => Hea Hks Hkt Hat Ha.
case; move/andP: (Hea) => [/= He Hka] _ Hkx _ Hxs Hx.
have Hkex: wfe (e,`X : typeof e x) by rewrite /= He wf_typeof.
have Hkes: wfe (e,`X : s) by rewrite /= He.
have Hkas: wfx (e,`X : s) a by rewrite wfx_widen0.
have Hkax: wfx (e,`X : typeof e x) a by rewrite wfx_widen0.
split=> //; first exact: wfx_subsxe.
  rewrite /subsxe typeof_nFun /=; apply: subtype_trans Hat; apply: subtype_nProd.
  rewrite (typeof_subsx0 He) //.
  have:= typeof_narrow0 Hxs He (wf_typeof He Hkx) Hks Hkas Ha.
  apply: subtype_strengthen; last exact: wf_typeof.
  rewrite -(wft_widen0 (typeof e x)); exact: wf_typeof.
case: (@typecheck_subsxx0 e x a s Top); [by split | by split | clear 4].
rewrite /subsxe {s t Hea Hks Hkt Hat Ha He Hka Hkas Hkax Hkx Hxs Hx Hkex Hkes}/=.
by elim: e {a x}(subsxx _ _ _ _) => //=; case; auto.
Qed.

(* Reduction proper, finally.*)

Definition areduce i x :=
  match x with
  | App (Fun Kvalue _ x') y => Some (subsxx 0 i y x')
  | Tapp (Fun Ktype _ x') u => Some (substx 0 i u x')
  | _ => None
  end.

Lemma typecheck_areduce : forall e x t,
  typecheck e x t -> if areduce #e x is Some x' then typecheck e x' t else True.
Proof.
move=> e [] // [] // [] //= s x => [y|u] t [He /=]; rewrite !coerce_def -andbA.
  move/and3P=> [Hks Hkx Hky] Hkt Hxt [Hx Hy Hys].
  apply typecheck_subsxx0 with s; first by split.
  have Hes: wfe (e,`X : s) by rewrite /= He.
  split=> //; first by rewrite wft_weak0.
  rewrite -(lower_inv0 (wf_typeof Hes Hkx)); exact: subtype_weak0.
move/and3P=> [Hks Hkx Hku] Hkt Hxt [Hx Hus].
have Hx': wfx (e,`X <: u) x by rewrite wfx_widen0 -(wfx_widen0 _ _ s).
split=> //; first exact: wfx_subst0.
  rewrite (typeof_subst0 He) //; apply: subtype_trans Hxt; apply: subtype_subst0.
  apply: subtype_narrow0 (Hus) _; exact: typeof_narrow0 Hkx Hx.
case: (@typecheck_subst0 e u s x Top) => //.
by split=> //=; rewrite He.
Qed.

Definition reduce x :=
  let c := ectx x in
  if areduce #c (rdx x) is Some y then Some (subsxe y c) else None.

(* Theorem A.20 *)
Theorem type_preservation : forall x t, typecheck nil x t ->
  if reduce x is Some y then typecheck nil y t else True.
Proof.
move=> x t Hx; rewrite /reduce.
case: (areduce _ _) (typecheck_areduce (typecheck_rdx Hx)) => // y.
apply: typecheck_subsxe; exact: typecheck_ectx.
Qed.

Lemma areduce_progress : forall e x,
   valid_ctx_env e -> wfx e x -> typed e x ->
   reflect (areduce #e (ardx x) = None) (value x).
Proof.
move=> e x He; elim: x => /= [i|k s x _|x IHx y IHy|x IHx t]; try by left.
- by rewrite wfv_ctx.
- move/andP=> [Hkx Hky]; case Hxt: (coerce _ _) =>  [||[] s t] // [Hx Hy _].
  move: Hxt; rewrite coerce_def.
  by case: x {IHx Hkx Hx}(IHx Hkx Hx) => //= _ s' x _ [-> _ _]; right; case: IHy.
move/andP=> [Hkx _]; case Hxt: (coerce _ _) =>  [||[] s t'] // [Hx _].
move: Hxt; rewrite coerce_def.
by case: x {IHx Hkx Hx}(IHx Hkx Hx) => //= _ s' x _ [-> _ _]; right.
Qed.

(* Theorem A.16 *)
Theorem reduce_progress : forall x t, typecheck nil x t ->
  reflect (reduce x = None) (answer x).
Proof.
move=> x _ [_ Hkx _ _ Hx].
suff: reflect (areduce #(ectx x) (rdx x) = None) (answer x).
  by rewrite /reduce; case: (areduce _ _) => // y; case => //; right.
rewrite /ectx; move: Hkx Hx; have: valid_ctx_env nil by done.
elim: x nil => [i|[] s x IHx|x _ y _|x _ t] e; try exact: areduce_progress.
rewrite /= => He; case/andP=> _; exact: IHx (_,`_) _.
Qed.

Unset Implicit Arguments.
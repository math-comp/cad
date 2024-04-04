(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(* This file defines types {SAset F^n} for semi-algebraic sets and           *)
(* {SAfun F^n -> F^m} for semi-algebraic functions, where F has a structure  *)
(* of real closed field and n and m are natural numbers.                     *)
(* {SAset F^n} is constructed as a quotient of formulae and is equipped with *)
(* a structure of predType 'rV_n and choiceType.                             *)
(* Given F : rcfType and n : nat, we define:                                 *)
(*            SAset0 == the empty set                                        *)
(*          SAset1 x == the singleton containing x                           *)
(*       SAsub s1 s2 == s1 is included in s2                                 *)
(*  SAset_meet s1 s2 == the intersection of s1 and s2                        *)
(*  SAset_join s1 s2 == the union of s1 and s2                               *)
(*         SAset_top == the full set                                         *)
(*   SAset_sub s1 s2 == the difference s1 minus s2                           *)
(* These operations equip {SAset F^n} with a structure of distributive       *)
(* lattice with top, bottom and complement.                                  *)
(* Given F : rcfType and n, m : nat, we define:                              *)
(*         SAgraph f == the graph of f                                       *)
(*       SAimset f s == the image of s by f                                  *)
(*             SAabs == the absolute value as a semi-algebraic function      *)
(*              SAid == the identity of F^n as a semi-algebraic function     *)
(*        SAcomp f g == the composite of f and g                             *)
(*                                                                           *)
(*****************************************************************************)

Require Import ZArith Init.

From HB Require Import structures.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice path.
From mathcomp Require Import fintype div tuple finfun generic_quotient bigop.
From mathcomp Require Import finset perm ssralg ssrint poly polydiv ssrnum.
From mathcomp Require Import mxpoly binomial interval finalg complex zmodp.
From mathcomp Require Import mxpoly mpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order finset classical_sets topology.
From mathcomp Require Import normedtype polyrcf polyorder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax.
Import numFieldTopology.Exports.

From SemiAlgebraic Require Import auxresults formula.

Local Open Scope type_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.
Local Open Scope ring_scope.

Declare Scope sa_scope.
Delimit Scope sa_scope with SA.
Local Open Scope sa_scope.

Reserved Notation "{ 'SAset' F }"
  (format "{ 'SAset'  F }").
Reserved Notation "{ 'SAfun' T }"
  (format "{ 'SAfun'  T }").

Section Ngraph.
Variable (n : nat) (F : Type).

Definition ngraph (m : nat) (x : 'rV[F]_m) := [tuple x ord0 i | i < m].

Definition ngraph_tnth k (t : k.-tuple F) :
  ngraph (\row_(i < k) (tnth t i)) = t.
Proof.
apply/val_inj; rewrite /= -map_tnth_enum; apply/eq_map => i.
by rewrite mxE.
Qed.

Definition ngraph_nth k (x : F) (t : k.-tuple F) :
  ngraph (\row_(i < k) (nth x t i)) = t.
Proof.
rewrite -{2}[t]ngraph_tnth; congr ngraph; apply/rowP => i.
by rewrite !mxE -tnth_nth.
Qed.

Lemma nth_ngraph k x0 (t : 'rV[F]_k) (i : 'I_k) :
  nth x0 (ngraph t) i = t ord0 i.
Proof. by rewrite -tnth_nth tnth_map tnth_ord_tuple. Qed.

Lemma ngraph_nil (t : 'rV[F]_0) : ngraph t = [tuple of nil].
Proof. by apply/eq_from_tnth => - []. Qed.

Fact size_ngraph (m : nat) (t : 'rV[F]_m) : size (ngraph t) = m.
Proof. by rewrite size_tuple. Qed.

Fact cat_ffunE (x0 : F) (m : nat) (t : 'rV[F]_m) (p : nat)
    (u : 'rV[F]_p) (i : 'I_(m + p)) :
  (row_mx t u) ord0 i
  = if (i < m)%N then nth x0 (ngraph t) i else nth x0 (ngraph u) (i - m).
Proof.
by rewrite mxE; case: splitP => j ->; rewrite ?(addnC, addnK) nth_ngraph.
Qed.

Fact ngraph_cat (m : nat) (t : 'rV[F]_m) (p : nat) (u : 'rV[F]_p) :
  ngraph (row_mx t u) = ngraph t ++ ngraph u :> seq F.
Proof.
case: m t => [|m] t.
  by rewrite row_thin_mx ngraph_nil.
apply: (@eq_from_nth _ (t ord0 ord0)) => [|i].
  by rewrite size_cat ?size_ngraph.
rewrite size_ngraph=> lt_i_mp; rewrite nth_cat.
have -> : i = nat_of_ord (Ordinal lt_i_mp) by [].
by rewrite nth_ngraph (cat_ffunE (t ord0 ord0)) size_ngraph.
Qed.

Lemma ngraph_bij k : bijective (@ngraph k).
Proof.
exists (fun (x : k.-tuple F) => (\row_(i < k) (tnth x i))) => x.
  by apply/rowP => i; rewrite mxE tnth_mktuple.
by rewrite ngraph_tnth.
Qed.

Lemma take_ngraph m (x : 'rV[F]_(n + m)) :
  take n (ngraph x) = ngraph (lsubmx x).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
by rewrite ngraph_cat take_cat size_ngraph ltnn subnn take0 cats0.
Qed.

Lemma drop_ngraph m (x : 'rV[F]_(n + m)) :
  drop n (ngraph x) = ngraph (rsubmx x).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
by rewrite ngraph_cat drop_cat size_ngraph ltnn subnn drop0.
Qed.

End Ngraph.

Section Var_n.

Variable F : rcfType.
Variable n : nat.

(* We define a relation in formulae *)
Definition equivf (f g : formula F) :=
  rcf_sat [::] (nquantify O n Forall ((f ==> g) /\ (g ==> f))).

Lemma equivf_refl : reflexive equivf.
Proof. by move=> f; apply/rcf_satP; apply: nforall_is_true => e /=. Qed.

Lemma equivf_sym : ssrbool.symmetric equivf.
Proof.
move=> f g; rewrite /equivf; move: [::] => e.
move: O => i; move: (f ==> g)%oT (g ==> f)%oT => f' g' {f} {g}.
move: i e; elim: n=> [i e | n' iHn' i e].
by rewrite !nquantify0; apply/rcf_satP/rcf_satP => [[fg gf] | [gf fg]]; split.
rewrite !nquantSout /=.
apply/rcf_satP/rcf_satP => /= [h x | h x];
  move/(_ x)/rcf_satP : h => h; apply/rcf_satP.
+ by rewrite -iHn'.
+ by rewrite iHn'.
Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> f g h; rewrite /equivf; move: [::] => e.
move: e O; elim: n => [|m ih] e i.
+ rewrite !nquantify0; move/rcf_satP => [h1 h2]; move/rcf_satP => [h3 h4].
  apply/rcf_satP; split => [Hg | Hh].
  - by apply: h3; apply: h1.
  - by apply: h2; apply: h4.
+ rewrite !nquantSout.
  move/rcf_satP => fg; move/rcf_satP => hf; apply/rcf_satP => x.
  apply/rcf_satP; apply: ih; apply/rcf_satP.
  - exact: fg.
  - exact: hf.
Qed.

(* we show that equivf is an equivalence *)
Definition equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.

(* equiv_formula *)
Definition sub_equivf :=
  (@sub_r _ _ {formula_n _} equivf_equiv).

Definition SAtype := {eq_quot sub_equivf}.
Definition SAtype_of of phant (F ^ n) := SAtype.
Identity Coercion id_type_of : SAtype_of >-> SAtype.
Local Notation "{ 'SAset' }" := (SAtype_of (Phant (F ^ n))).

Coercion SAtype_to_form (A : SAtype) : {formula_n _} := repr A.

(* we recover some structure for the quotient *)
HB.instance Definition SAset_quotType := Quotient.on SAtype.
HB.instance Definition Aset_eqType := Equality.on SAtype.
HB.instance Definition Aset_choiceType := Choice.on SAtype.
HB.instance Definition Aset_eqQuotType := EqQuotient.on SAtype.

HB.instance Definition Aset_of_quotType := Quotient.on {SAset}.
HB.instance Definition Aset_of_eqType := Equality.on {SAset}.
HB.instance Definition Aset_of_choiceType := Choice.on {SAset}.
HB.instance Definition Aset_of_eqQuotType := EqQuotient.on {SAset}.

End Var_n.

Notation "{ 'SAset' F }" := (SAtype_of (Phant F)) : type_scope.

Section Interpretation.

Variable F : rcfType. (* is also a realDomainType *)

Variable n : nat.

Definition interp := fun (f : {formula_n F}) =>
  [pred v : 'rV[F]_n | rcf_sat (ngraph v) f].

Definition pred_of_SAset (s : {SAset F^n}) :
  pred ('rV[F]_n) := interp (repr s).
Canonical SAsetPredType := PredType pred_of_SAset.

End Interpretation.

Section SemiAlgebraicSet.

Variable F : rcfType.
Variable n : nat.

Fact rcf_sat_tuple (t : n.-tuple F) (f : {formula_n F}) :
  rcf_sat t f = ((\row_(i < n) (tnth t i)) \in
  [pred y : 'rV[F]_n | rcf_sat (ngraph (\row_(i < n) (tnth t i))) f]).
Proof. by rewrite inE ngraph_tnth. Qed.

Fact holds_tuple (t : n.-tuple F) (s : {SAset F^n}) :
  reflect (holds t s) ((\row_(i < n) (tnth t i)) \in s).
Proof.
apply: (iffP idP) => [h | ].
  by apply/rcf_satP; rewrite rcf_sat_tuple.
by move/rcf_satP; rewrite rcf_sat_tuple.
Qed.

Lemma holds_equivf (t : n.-tuple F) (f g : {formula_n F}) :
  sub_equivf f g -> holds t f -> holds t g.
Proof. by move/rcf_satP/nforallP; move/(_ t) => [h _]. Qed.

Lemma rcf_sat_equivf (t : n.-tuple F) (f g : {formula_n F}) :
  sub_equivf f g -> rcf_sat t f = rcf_sat t g.
Proof.
move=> h; apply/rcf_satP/rcf_satP; apply: holds_equivf => //.
by rewrite /sub_equivf /= equivf_sym.
Qed.

Fact rcf_sat_repr_pi (t : n.-tuple F) (f : {formula_n F}) :
  rcf_sat t (repr (\pi_{SAset F^n} f)) = rcf_sat t f.
Proof. by case: piP => ? /eqmodP /rcf_sat_equivf ->. Qed.

Fact holds_repr_pi (t : n.-tuple F) (f : {formula_n F}) :
  holds t (repr (\pi_{SAset F^n} f)) <-> holds t f.
Proof. by split; apply: holds_equivf; rewrite /sub_equivf -eqmodE reprK. Qed.

Lemma equivf_exists (f g : {formula_n F}) (i : nat) :
  equivf n f g -> (equivf n ('exists 'X_i, f) ('exists 'X_i, g))%oT.
Proof.
rewrite /equivf; move/rcf_satP/nforallP => h.
apply/rcf_satP/nforallP => u /=.
have [lt_in|leq_ni] := ltnP i n.
  by split=> -[x hxf]; exists x; move: hxf;
    move/(_ [tuple of (set_nth 0 u (Ordinal lt_in) x)]) : h;
    rewrite cat0s /= => -[].
split=> -[x].
  rewrite set_nth_over ?size_tuple // rcons_cat /=.
  move/holds_take; rewrite take_size_cat ?size_tuple // => holds_ug.
  exists 0; rewrite set_nth_nrcons ?size_tuple // rcons_nrcons -nseq_cat.
  by apply/holds_cat_nseq; move: holds_ug; move/(_ u) : h => [].
move/holds_fsubst.
rewrite fsubst_id; last
  by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
move=> holds_uf; exists x; apply/holds_fsubst.
rewrite fsubst_id; last
  by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
by move: holds_uf; move/(_ u) : h; rewrite cat0s /=; move => [].
Qed.

Lemma pi_form (f : {formula_n F}) (x : 'rV[F]_n) :
  (x \in \pi_{SAset F^n} f) = rcf_sat (ngraph x) f.
Proof. by rewrite inE; apply/rcf_satP/rcf_satP => ?; apply/holds_repr_pi. Qed.

Lemma SAsetP (s1 s2 : {SAset F^n}) : reflect (s1 =i s2) (s1 == s2).
Proof.
move: s1 s2; apply: quotW => f1; apply: quotW => f2.
apply: (iffP idP) => [/eqP <-|] //.
rewrite eqmodE /equivf => h; apply/rcf_satP/nforallP => u.
split; move/holds_repr_pi/holds_tuple; [rewrite h | rewrite -h];
by move/holds_tuple/holds_repr_pi.
Qed.

End SemiAlgebraicSet.

Section Comprehension.

Variables (F : rcfType) (n : nat) (f : formula F).

(* TODO: remove the useless cut. *)
Definition SAset_comprehension := \pi_({SAset F^n}) (cut n f).

Lemma SAin_setP x : reflect (holds (ngraph x) f) (x \in SAset_comprehension).
Proof.
apply/(iffP (rcf_satP _ _)) => [/holds_repr_pi/holds_subst|hf].
  by rewrite -{1}[ngraph x : seq _]cats0 subst_env_iota_catl ?size_ngraph.
apply/holds_repr_pi/holds_subst.
by rewrite -[ngraph x : seq _]cats0 subst_env_iota_catl ?size_ngraph.
Qed.

End Comprehension.

Notation "[ 'set' : T | f ]" := ((@SAset_comprehension _ _ (f)%oT) : T)
  (at level 0, only parsing) : sa_scope.
Notation "[ 'set' | f ]" := (@SAset_comprehension _ _ (f)%oT)
  (at level 0, f at level 99, format "[ 'set' |  f ]") : sa_scope.

Section Ops.

Variables (F : rcfType) (n : nat).

Definition SAset_seq (r : seq 'rV[F]_n) : {SAset F^n} :=
  [set | \big[Or/False]_(x <- r)
           \big[And/True]_(i < n) ('X_i == (x ord0 i)%:T)%oT ].

Lemma inSAset_seq r x : x \in SAset_seq r = (x \in r).
Proof.
apply/SAin_setP/idP => [/holdsOr [y][+][_] /holdsAnd hy|xr].
  congr in_mem; apply/rowP => i.
  move: hy => /(_ i); rewrite mem_index_enum /= (nth_map i) ?size_enum_ord//.
  by rewrite nth_ord_enum => ->.
apply/holdsOr; exists x; split=> //; split=> //.
apply/holdsAnd => i _ _ /=.
by rewrite (nth_map i) ?size_enum_ord// nth_ord_enum.
Qed.

Definition SAset0 : {SAset F^n} := SAset_seq [::].

Lemma inSAset0 (x : 'rV[F]_n) : x \in SAset0 = false.
Proof. by rewrite inSAset_seq. Qed.

Lemma inSAset1 (x y : 'rV[F]_n) : x \in SAset_seq [:: y] = (x == y).
Proof. by rewrite inSAset_seq in_cons in_nil orbF. Qed.

Definition SAsetT : {SAset F^n} := [set | True%oT ].

Lemma inSAsetT (x : 'rV[F]_n) : x \in SAsetT.
Proof. exact/SAin_setP. Qed.

Definition SAsetU (f g : {SAset F^n}) :=
  \pi_({SAset F^n}) (formulan_or f g).

Lemma inSAsetU f g x : x \in SAsetU f g = (x \in f) || (x \in g).
Proof.
rewrite /SAsetU pi_form !inE.
by apply/rcf_satP/orP; (case=> [l|r]; [left|right]; apply/rcf_satP).
Qed.

Definition SAsetU1 x f := SAsetU (SAset_seq [:: x]) f.

Lemma inSAsetU1 x f y : y \in SAsetU1 x f = (y == x) || (y \in f).
Proof. by rewrite inSAsetU inSAset1. Qed.

Definition SAsetI (f g : {SAset F^n}) :=
  \pi_({SAset F^n}) (formulan_and f g).

Lemma inSAsetI f g x : x \in SAsetI f g = (x \in f) && (x \in g).
Proof.
rewrite /SAsetI pi_form !inE.
by apply/rcf_satP/andP => [/=|] [l r]; split; apply/rcf_satP.
Qed.

Definition SAsetC (s : {SAset F^n}) := \pi_{SAset F^n} (formulan_not s).

Lemma inSAsetC f x : x \in SAsetC f = ~~ (x \in f).
Proof.
rewrite /SAsetC pi_form !inE.
apply/rcf_satP/negP => /= [hn /rcf_satP//|hn h].
by apply/hn/rcf_satP.
Qed.

Definition SAsetD (s1 s2 : {SAset F^n}) : {SAset F^n} :=
  SAsetI s1 (SAsetC s2).

Lemma inSAsetD s1 s2 x : x \in SAsetD s1 s2 = (x \in s1) && ~~ (x \in s2).
Proof. by rewrite inSAsetI inSAsetC. Qed.

Definition SAsetD1 s x := SAsetD s (SAset_seq [:: x]).

Lemma inSAsetD1 s x y : y \in SAsetD1 s x = (y \in s) && (y != x).
Proof. by rewrite inSAsetD inSAset1. Qed.

Definition SAsetX m (s1 : {SAset F^n}) (s2 : {SAset F^m}) : {SAset F^(n + m)} :=
  [set | s1 /\ subst_formula (iota n m) s2 ].

Lemma inSAsetX m (s1 : {SAset F^n}) (s2 : {SAset F^m}) (x : 'rV[F]_(n + m)) :
  x \in SAsetX s1 s2 = (lsubmx x \in s1) && (rsubmx x \in s2).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
apply/SAin_setP/andP => /= -[]; rewrite ngraph_cat.
  move=> /holds_take + /holds_subst.
  rewrite take_size_cat ?size_ngraph// subst_env_iota_catr ?size_ngraph//.
  by split; apply/rcf_satP.
move=> ls rs; split.
  by apply/holds_take; rewrite take_size_cat ?size_ngraph//; apply/rcf_satP.
apply/holds_subst; rewrite subst_env_iota_catr ?size_ngraph//.
exact/rcf_satP.
Qed.

Definition SAset_sub s1 s2 := SAsetD s1 s2 == SAset0.

Lemma SAset_subP s1 s2 : reflect {subset s1 <= s2} (SAset_sub s1 s2).
Proof.
apply/(iffP idP) => [/SAsetP|] s12; last first.
  by apply/SAsetP => x; rewrite inSAsetD inSAset0; apply/negP => /andP[/s12 ->].
move=> x x1; apply/negP => /negP x2.
suff: x \in SAset0 by rewrite inSAset0.
by rewrite -s12 inSAsetD x1.
Qed.

Definition SAset_proper s1 s2 := SAset_sub s1 s2 && ~~ SAset_sub s2 s1.

End Ops.

Definition SAset_cast (F : rcfType) (n m : nat) (s : {SAset F^n}) : {SAset F^m} :=
  [set | (\big[And/True]_(i <- iota n (m-n)) ('X_i == 0)) /\
      nquantify m (n-m) Exists s].

Notation "[ 'set' x1 ; .. ; xn ]" :=
  (SAset_seq (cons x1 .. (cons xn nil) .. )): sa_scope.
Notation "A :|: B" := (SAsetU A B) : sa_scope.
Notation "x |: A" := (SAsetU1 x A) : sa_scope.
Notation "A :&: B" := (SAsetI A B) : sa_scope.
Notation "~: A" := (SAsetC A) : sa_scope.
Notation "A :\: B" := (SAsetD A B) : sa_scope.
Notation "A :\ x" := (SAsetD1 A x) : sa_scope.
Notation "A :*: B" := (SAsetX A B) (at level 35) : sa_scope.
Notation "A :<=: B" := (SAset_sub A B) (at level 49) : sa_scope.
Notation "A :<: B" := (SAset_proper A B) (at level 49) : sa_scope.

Definition SAset_itv (F : rcfType) (I : interval F) :=
  let 'Interval l u := I in
  (match l with
   | BSide false lb => [set | lb%:T <% 'X_0]
   | BSide true lb => [set | lb%:T <=% 'X_0]
   | BInfty false => SAset0 F 1
   | BInfty true => SAsetT F 1
   end) :&: (
   match u with
   | BSide false ub => [set | 'X_0 <=% ub%:T]
   | BSide true ub => [set | 'X_0 <% ub%:T]
   | BInfty false => SAsetT F 1
   | BInfty true => SAset0 F 1
   end).

Arguments SAset_itv : simpl never.

Lemma inSAset_itv (F : rcfType) (I : interval F) (x : 'rV[F]_1) :
  (x \in SAset_itv I) = (x 0 0 \in I).
Proof.
rewrite in_itv; case: I => l u.
rewrite inSAsetI; congr andb.
  case: l => [+ t|]; case=> /=; last first.
  - exact/inSAset0.
  - exact/inSAsetT.
  - by apply/SAin_setP/idP => /=; rewrite enum_ordSl/=.
  - by apply/SAin_setP/idP => /=; rewrite enum_ordSl/=.
case: u => [+ t|]; case=> /=; last first.
- exact/inSAsetT.
- exact/inSAset0.
- by apply/SAin_setP/idP => /=; rewrite enum_ordSl/=.
- by apply/SAin_setP/idP => /=; rewrite enum_ordSl/=.
Qed.

Definition SAset_pos (F : rcfType) : {SAset F^1} :=
  SAset_itv `]0, +oo[%R.

Section SAsetTheory.
Variables (F : rcfType) (n : nat).
Implicit Types (A B C : {SAset F^n}) (x y z : 'rV[F]_n) (s t : seq 'rV[F]_n).

Lemma eqEsubset A B : (A == B) = (A :<=: B) && (B :<=: A).
Proof.
apply/SAsetP/andP => [AB|[] /SAset_subP AB /SAset_subP BA x].
  by split; apply/SAset_subP => x; rewrite AB.
by apply/idP/idP => [/AB|/BA].
Qed.

Lemma subEproper A B : (A :<=: B) = (A == B) || (A :<: B).
Proof. by rewrite eqEsubset -andb_orr orbN andbT. Qed.

Lemma properEneq A B : (A :<: B) = (A != B) && (A :<=: B).
Proof. by rewrite andbC eqEsubset negb_and andb_orr [X in X || _]andbN. Qed.

(* lt_def does things the other way. Should we have a fixed convention? *)
Lemma properEneq' A B : (A :<: B) = (B != A) && (A :<=: B).
Proof. by rewrite properEneq eq_sym. Qed.

Lemma proper_neq A B : A :<: B -> A != B.
Proof. by rewrite properEneq; case/andP. Qed.

Lemma eqEproper A B : (A == B) = (A :<=: B) && ~~ (A :<: B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEsubset. Qed.

Lemma sub0set A : SAset0 F n :<=: A.
Proof. by apply/SAset_subP => x; rewrite inSAset0. Qed.

Lemma subset0 A : (A :<=: SAset0 F n) = (A == SAset0 F n).
Proof. by rewrite eqEsubset sub0set andbT. Qed.

Lemma proper0 A : (SAset0 F n :<: A) = (A != SAset0 F n).
Proof. by rewrite properEneq sub0set andbT eq_sym. Qed.

Lemma set0Vmem A : (A = SAset0 F n) + {x | x \in A}.
Proof.
case/boolP: (A == SAset0 F n) => [/eqP|] A0; first by left.
right; move: A A0; apply: quotW => /= f; rewrite eqmodE /=.
move=> /rcf_satP/n_nforall_formula/nexistsP P.
apply: sigW; move: P => [x hx] /=; exists (\row_(i < n) x`_i).
rewrite inE ngraph_nth rcf_sat_repr_pi.
move/rcf_satP: hx; rewrite cat0s !simp_rcf_sat; case: rcf_sat => //=.
by rewrite implybF negbK big_nil => /rcf_satP/holds_subst.
Qed.

Lemma proper0P A : reflect (exists x, x \in A) (SAset0 F n :<: A).
Proof.
rewrite proper0; have [->|[x xA]] := set0Vmem A.
  by rewrite eqxx/=; apply/Bool.ReflectF => -[x]; rewrite inSAset0.
suff ->: (A != SAset0 F n) by apply/Bool.ReflectT; exists x.
by apply/eqP => A0; rewrite A0 inSAset0 in xA.
Qed.

Lemma subsetT A : A :<=: SAsetT F n.
Proof. by apply/SAset_subP => x; rewrite inSAsetT. Qed.

Lemma subTset A : (SAsetT F n :<=: A) = (A == SAsetT F n).
Proof. by rewrite eqEsubset subsetT. Qed.

Lemma properT A : (A :<: SAsetT F n) = (A != SAsetT F n).
Proof. by rewrite properEneq subsetT andbT. Qed.

Lemma perm_SAset_seq s t :
  perm_eq s t -> SAset_seq s = SAset_seq t.
Proof.
by move=> st; apply/eqP/SAsetP => x; rewrite !inSAset_seq (perm_mem st).
Qed.

Lemma SAset_nil : SAset_seq [::] = SAset0 F n.
Proof. by []. Qed.

Lemma SAset_cons x s : SAset_seq (x :: s) = x |: SAset_seq s.
Proof. by apply/eqP/SAsetP => y; rewrite inSAsetU1 !inSAset_seq in_cons. Qed.

Lemma SAset_cat s t : SAset_seq (s ++ t) = SAset_seq s :|: SAset_seq t.
Proof. by apply/eqP/SAsetP => y; rewrite inSAsetU !inSAset_seq mem_cat. Qed.

Lemma SAset_rev s : SAset_seq (rev s) = SAset_seq s.
Proof. exact/perm_SAset_seq/permPl/perm_rev. Qed.

Lemma SAset0U A : SAset0 F n :|: A = A.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetU inSAset0. Qed.

Lemma SAsetUC A B : A :|: B = B :|: A.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetU orbC. Qed.

Lemma SAsetUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetU orbA. Qed.

Lemma SAsetU_comprehension (f g : formula F) :
  [set| f] :|: [set| g] = [set| f \/ g] :> {SAset F^n}.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetU; apply/orP/SAin_setP => /=.
  by case=> /SAin_setP xfg; [left|right].
by case=> xfg; [left|right]; apply/SAin_setP.
Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build {SAset F^n}
    (SAset0 F n) (@SAsetU F n) SAsetUA SAsetUC SAset0U.

Lemma SAsetIC A B : A :&: B = B :&: A.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetI andbC. Qed.

Lemma SAsetIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetI andbA. Qed.

Lemma SAsetI0 A :
  A :&: SAset0 F n = SAset0 F n.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAset0 andbF. Qed.

Lemma SAsetTI A : SAsetT F n :&: A = A.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAsetT. Qed.

Lemma SAsetIT A : A :&: SAsetT F n = A.
Proof. by rewrite SAsetIC SAsetTI. Qed.

Lemma SAsetI_comprehension (f g : formula F) :
  [set| f] :&: [set| g] = [set| f /\ g] :> {SAset F^n}.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetI; apply/andP/SAin_setP.
  by move=> [] /SAin_setP xf /SAin_setP yf /=; split.
by move=> /= [] xf yf; split; apply/SAin_setP.
Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build {SAset F^n}
    (SAsetT F n) (@SAsetI F n) SAsetIA SAsetIC SAsetTI.

Lemma SAsetCK A :
  ~: ~: A = A.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetC negbK. Qed.

Lemma SAsetCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetI !inSAsetC inSAsetU negb_or.
Qed.

Lemma SAsetCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetU !inSAsetC inSAsetI negb_and.
Qed.

Lemma SAsetC_comprehension (f : formula F) :
  ~: [set | f] = [set | Not f] :> {SAset F^n}.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetC !inE.
apply/negP/SAin_setP => [fP|/nn_formula + /SAin_setP fP //].
by apply/nn_formula => fP'; apply/fP/SAin_setP.
Qed.

Lemma SAsubset_refl : reflexive (@SAset_sub F n).
Proof. by move=> A; apply/SAset_subP. Qed.

Lemma SAsubset_anti : antisymmetric (@SAset_sub F n).
Proof. by move=> A B /andP[] AB BA; apply/eqP; rewrite eqEsubset AB. Qed.

Lemma SAsubset_trans : transitive (@SAset_sub F n).
Proof.
by move=> A B C /SAset_subP BA /SAset_subP AC; apply/SAset_subP => x /BA /AC.
Qed.

Lemma SAsetIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetI !inSAsetU !inSAsetI andb_orr.
Qed.

Lemma SAsetIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by rewrite ![_ :&: C]SAsetIC SAsetIUr. Qed.

Lemma SAsetUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetU !inSAsetI !inSAsetU orb_andr.
Qed.

Lemma SAsetDIr A B :
  A :\: (A :&: B) = A :\: B.
Proof.
apply/eqP/SAsetP => x.
by rewrite !inSAsetI !inSAsetC inSAsetI negb_and andb_orr andbN.
Qed.

Lemma SAsubsetI A B C : A :<=: B :&: C = (A :<=: B) && (A :<=: C).
Proof.
apply/SAset_subP/andP => [ABC|[/SAset_subP AB]/SAset_subP AC x xA]; last first.
  by rewrite inSAsetI (AB _ xA) (AC _ xA).
by split; apply/SAset_subP => x /ABC; rewrite inSAsetI => /andP[].
Qed.

Lemma SAsubsetIl A B : A :&: B :<=: A.
Proof. by apply/SAset_subP => x; rewrite inSAsetI => /andP[]. Qed.

Lemma SAsubsetIidl A B : (A :<=: A :&: B) = (A :<=: B).
Proof. by rewrite SAsubsetI SAsubset_refl. Qed.

Lemma SAsubsetEI A B : A :<=: B = (A :&: B == A).
Proof. by rewrite eqEsubset SAsubsetIl SAsubsetIidl. Qed.

Lemma SAsubsetED A B :
  A :<=: B = (A :\: B == SAset0 F n).
Proof.
rewrite -subset0; apply/SAset_subP/SAset_subP => AB x.
  by rewrite inSAsetD => /andP[] /AB + /negP.
move=> xA; apply/negP => /negP xB.
have /AB: x \in A :\: B by rewrite inSAsetD xA.
by rewrite inSAset0.
Qed.

Lemma SAsetI_idem : idempotent (@SAsetI F n).
Proof.
by move=> A; apply/eqP; rewrite eqEsubset SAsubsetIl SAsubsetIidl SAsubset_refl.
Qed.

Lemma SAsetKU A B : A :&: (B :|: A) = A.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAsetU orKb. Qed.

Lemma SAsetKU' B A : A :&: (A :|: B) = A.
Proof. by rewrite SAsetUC SAsetKU. Qed.

Lemma SAsetKI A B : A :|: (B :&: A) = A.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetU inSAsetI andKb. Qed.

Lemma SAsetKI' B A : A :|: (A :&: B) = A.
Proof. by rewrite SAsetIC SAsetKI. Qed.

Lemma SAsetICr A : A :&: ~: A = SAset0 F n.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAsetC andbN inSAset0. Qed.

Lemma SAset0I A : SAset0 F n :&: A = SAset0 F n.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAset0. Qed.

Lemma SAsetID0 A B : SAsetI B (SAsetD A B) = (SAset0 F n).
Proof. by rewrite /SAsetD [A :&: _]SAsetIC SAsetIA SAsetICr SAset0I. Qed.

Lemma SAsetUCr A : A :|: ~: A = SAsetT F n.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetU inSAsetC orbN inSAsetT. Qed.

Lemma SAsetUID A B : A :&: B :|: A :\: B = A.
Proof. by rewrite -SAsetIUr SAsetUCr SAsetIT. Qed.

Notation "\bigcap_( i <- r | P ) f" :=
    (\big[@SAsetI _ _/SAsetT _ _]_(i <- r | P) f)
  (at level 41, f at level 41, r, P at level 50).

Lemma inSAset_bigcap (I : Type) (r : seq I) (P : pred I)
  (f : I -> {SAset F^n}) (x : 'rV[F]_n) :
  (x \in \bigcap_(i <- r | P i) f i) = all (fun i => P i ==> (x \in f i)) r.
Proof.
elim: r => /= [|i r IHr]; first by rewrite big_nil inSAsetT.
by rewrite big_cons; case: (P i) => //; rewrite inSAsetI IHr.
Qed.

Notation "\bigcup_( i <- r | P ) f" :=
    (\big[@SAsetU _ _/SAset0 _ _]_(i <- r | P) f)
  (at level 41, f at level 41, r, P at level 50).

Lemma inSAset_bigcup (I : Type) (r : seq I) (P : pred I)
  (f : I -> {SAset F^n}) (x : 'rV[F]_n) :
  (x \in \bigcup_(i <- r | P i) f i) = has (fun i => P i && (x \in f i)) r.
Proof.
elim: r => /= [|i r IHr]; first by rewrite big_nil inSAset0.
by rewrite big_cons; case: (P i) => //; rewrite inSAsetU IHr.
Qed.

Lemma SAsetIbigcupr A (I : Type) (r : seq I) (P : pred I)
  (f : I -> {SAset F^n}) :
  A :&: \bigcup_(i <- r | P i) f i = \bigcup_(i <- r | P i) (A :&: f i).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil SAsetI0.
by rewrite !big_cons; case: (P i) => //; rewrite SAsetIUr IHr.
Qed.

Lemma SAsetIbigcup (I J : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^n})
  (s : seq J) (Q : pred J) (g : J -> {SAset F^n}) :
  (\bigcup_(i <- r | P i) f i) :&: (\bigcup_(j <- s | Q j) g j)
      = \bigcup_(ij <- allpairs pair r s | P (fst ij) && Q (snd ij))
          (f (fst ij) :&: g (snd ij)).
Proof.
elim: r => /= [|i r IHr]; first by rewrite !big_nil SAset0I.
rewrite big_cons big_cat/= big_map/=; case: (P i) => /=; last first.
  by rewrite big_pred0_eq SAset0U.
by rewrite SAsetIUl -IHr SAsetIbigcupr.
Qed.

Lemma SAsetCbigcap (I : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^n}) :
  (~: \bigcap_(i <- r | P i) f i) = \bigcup_(i <- r | P i) ~: f i.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetC inSAset_bigcap inSAset_bigcup.
rewrite -has_predC; elim: r => [//|] i r IHr /=.
by rewrite negb_imply IHr inSAsetC.
Qed.

Lemma SAsetCbigcup (I : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^n}) :
  (~: \bigcup_(i <- r | P i) f i) = \bigcap_(i <- r | P i) ~: f i.
Proof.
rewrite -[RHS]SAsetCK SAsetCbigcap; congr (~: _).
by apply/eq_bigr => i _; rewrite SAsetCK.
Qed.

Lemma SAset0X (s : {SAset F^n}) :
  SAset0 F 0 :*: s = SAset0 F n.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetX !inSAset0. Qed.

Lemma SAsetX0 (s : {SAset F^n}) :
  s :*: SAset0 F 0 = SAset0 F (n + 0).
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetX !inSAset0 andbF. Qed.

Lemma inSAset_pos (x : 'rV[F]_1) : x \in SAset_pos F = (0 < x ord0 ord0).
Proof. by rewrite inSAset_itv in_itv/= andbT. Qed.

Lemma SAset_cast_id m (A : {SAset F^m}) : SAset_cast m A = A.
Proof.
apply/eqP/SAsetP => x; apply/SAin_setP/rcf_satP => /= [[] _|hx];
  rewrite subnn nquantify0//.
by split=> //; apply/holdsAnd.
Qed.

Lemma SAset_cast_le m k (A : {SAset F^m}) : (k <= m)%N ->
  SAset_cast k A = [set | nquantify k (m - k) Exists A].
Proof.
rewrite -subn_eq0 => /eqP km; apply/eqP/SAsetP => x.
apply/Bool.eq_iff_eq_true.
rewrite [X in X <-> _](iff_sym (rwP (SAin_setP _ _))).
rewrite [X in _ <-> X](iff_sym (rwP (SAin_setP _ _))).
rewrite km big_nil/=.
by split=> // -[].
Qed.

Lemma SAset_cast_ge m k (A : {SAset F^m}) : (m <= k)%N ->
  SAset_cast k A
  = [set | A /\ \big[And/True]_(i <- iota m (k - m)) ('X_i == 0)].
Proof.
rewrite -subn_eq0 => /eqP km; apply/eqP/SAsetP => x.
apply/Bool.eq_iff_eq_true.
rewrite [X in X <-> _](iff_sym (rwP (SAin_setP _ _))).
rewrite [X in _ <-> X](iff_sym (rwP (SAin_setP _ _))).
rewrite km nquantify0/=.
by split=> -[].
Qed.

Lemma inSAset_cast m (s : {SAset F^n}) (x : 'rV[F]_m) (mn : m = n) :
  x \in SAset_cast m s = (castmx (erefl, mn) x \in s).
Proof.
by move: x (mn); rewrite mn => x nn; rewrite SAset_cast_id castmx_id.
Qed.

Lemma inSAset_castDn m k (A : {SAset F^(m+k)}) (x : 'rV[F]_m) :
  reflect (exists y : 'rV[F]_(m+k), y \in A /\ x = lsubmx y)
    (x \in SAset_cast m A).
Proof.
rewrite SAset_cast_le ?leq_addr// subDnCA// subnn addn0.
rewrite -[X in nquantify X](size_ngraph x).
apply/(iffP (SAin_setP _ _)) => [/nexistsP [y] hxy|[y][yA]->].
  exists (row_mx x (\row_i tnth y i)); rewrite row_mxKl; split=> //.
  by apply/rcf_satP; rewrite ngraph_cat ngraph_tnth.
apply/nexistsP; exists (ngraph (rsubmx y)); rewrite -ngraph_cat hsubmxK.
exact/rcf_satP.
Qed.

Lemma inSAset_castnD m k (A : {SAset F^m}) (x : 'rV[F]_(m+k)) :
  x \in SAset_cast (m+k) A = (lsubmx x \in A) && (rsubmx x == 0).
Proof.
rewrite SAset_cast_ge ?leq_addr//.
apply/SAin_setP/andP => /=;
    rewrite -holds_take take_ngraph holdsAnd /= => -[/rcf_satP hx].
  move=> h0; split=> //; apply/eqP/rowP => i.
  move/(_ (@unsplit m k (inr i))): h0.
  rewrite nth_ngraph mem_iota subnKC ?leq_addr//= -addnS leq_add//.
  move=> /(_ Logic.eq_refl Logic.eq_refl).
  by rewrite !mxE.
move=> /eqP /rowP x0; split=> // => i.
rewrite mem_iota subnKC ?leq_addr// => /andP[mi im] _.
rewrite (nth_ngraph _ _ (Ordinal im)) -(splitK (Ordinal im)).
move: mi; rewrite leqNgt -{1}[i%N]/(Ordinal im : nat).
case: splitP => // j _ _.
by move: (x0 j); rewrite !mxE.
Qed. 

Lemma SAset_cast_trans k m A : (minn n k <= m)%N ->
  SAset_cast k (SAset_cast m A) = SAset_cast k A.
Proof.
case: (ltnP m n) => [mn|nm _]; last first.
  case/orP: (leq_total m k) => [mk|km].
    rewrite -(subnKC mk) -(subnKC nm) [X in (k-X)%N]subnKC//.
    apply/eqP/SAsetP => x.
    rewrite 2!inSAset_castnD.
    move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
    move: (lsubmx l) (rsubmx l) (hsubmxK l) => ll lr <- {l}.
    rewrite SAset_cast_ge; last by rewrite subnKC// subnKC// (leq_trans nm mk). 
    apply/andP/SAin_setP => /=;
        rewrite holdsAnd -holds_take -(take_takel _ (@leq_addr (m-n) n)%N);
        rewrite !take_ngraph !row_mxKl (rwP (rcf_satP _ _));
        rewrite subDnCA ?leq_addr// subDnCA// subnn addn0 addnC.
      move=> [] /andP[] llA /eqP -> /eqP ->; split=> //= i.
      rewrite mem_iota addnA => /andP[+ ilt] _.
      rewrite -[i%N]/(Ordinal ilt : nat) nth_ngraph mxE.
      case: (splitP (Ordinal ilt)) => j ->; rewrite mxE//.
      by case: (splitP j) => j' ->; rewrite leqNgt ?ltn_ord// mxE.
    move=> [llA /= h0]; split; last first.
      apply/eqP/rowP => i.
      move/(_ (unsplit (inr i) : 'I_(n + (m - n) + (k - m))%N)): h0.
      rewrite nth_ngraph !mxE unsplitK.
      by rewrite mem_iota addnA ltn_ord/= -addnA leq_addr; apply.
    apply/andP; split=> //.
    apply/eqP/rowP => i; move: h0.
    move=> /(_ (unsplit (inl (unsplit (inr i))) :
                  'I_(n + (m - n) + (k - m))%N)).
    rewrite nth_ngraph !mxE unsplitK mxE unsplitK.
    by rewrite mem_iota addnA ltn_ord/= leq_addr; apply.
  case/orP: (leq_total n k) => [nk|kn].
    rewrite -(subnKC km) -(subnKC nk) [X in (m-X)%N]subnKC//.
    apply/eqP/SAsetP => x.
    rewrite inSAset_castnD.
    move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
    apply/inSAset_castDn/andP => [[y]|[lA] /eqP ->];
        rewrite SAset_cast_ge -?addnA ?leq_addr//.
      move: (lsubmx y) (rsubmx y) (hsubmxK y).
      move=> yl yr <- {y} [] /[swap] <- {yl} /SAin_setP/= [] /holds_take.
      rewrite -(take_takel _ (@leq_addr (k - n)%N n)) !take_ngraph !row_mxKl.
      move=> /rcf_satP lA /holdsAnd.
      rewrite subDnCA ?leq_addr// subDnCA// subnn addn0 addnC /= => h0.
      split=> //; apply/eqP/rowP => i; move: h0.
      move=> /(_ (unsplit (inl (unsplit (inr i))) :
                  'I_(n + (k - n) + (m - k))%N)).
      rewrite nth_ngraph !mxE unsplitK mxE unsplitK mem_iota addnA ltn_ord/=.
      by rewrite leq_addr; apply.
    exists (row_mx (row_mx l 0) 0); rewrite row_mxKl; split=> //.
    apply/SAin_setP => /=; split.
      apply/holds_take.
      rewrite -(take_takel _ (@leq_addr (k - n)%N n)) !take_ngraph !row_mxKl.
      exact/rcf_satP.
    apply/holdsAnd => i; rewrite mem_iota subDnCA ?leq_addr// subDnCA// subnn.
    rewrite addn0 [X in (n + X)%N]addnC /= addnA => /andP[+ ilt] _.
    rewrite -[i%N]/(Ordinal ilt : nat) nth_ngraph mxE.
    case: (splitP (Ordinal ilt)) => j ->; rewrite mxE//.
    by case: (splitP j) => j' ->; rewrite leqNgt ?ltn_ord// mxE.
  move: A; rewrite -(subnKC nm) -(subnKC kn) [X in (m - X)%N]subnKC// -addnA.
  move=> A.
  apply/eqP/SAsetP => x; apply/inSAset_castDn/inSAset_castDn => -[y].
    rewrite [_ _ A]SAset_cast_ge ?addnA ?leq_addr//.
    move=> -[] /SAin_setP /= [] /holds_take + _.
    rewrite takeD take_ngraph drop_ngraph take_ngraph -ngraph_cat => yA -> {x}.
    exists (row_mx (lsubmx y) (lsubmx (rsubmx y))); split; first exact/rcf_satP.
    by rewrite row_mxKl.
  move=> [] /rcf_satP yA -> {x}.
  exists (row_mx (lsubmx y) (row_mx (rsubmx y) 0)).
  split; last by rewrite row_mxKl.
  rewrite [_ _ A]SAset_cast_ge ?addnA ?leq_addr//; apply/SAin_setP => /=; split.
    apply/holds_take.
    rewrite takeD take_ngraph drop_ngraph take_ngraph -ngraph_cat row_mxKr.
    by rewrite !row_mxKl hsubmxK.
  apply/holdsAnd => i; rewrite {1}addnA subnKC// subnKC// mem_iota.
  rewrite -{1 2}(subnKC kn) -addnA => /andP[] + ilt _ /=.
  rewrite -[i%N]/(Ordinal ilt : nat) nth_ngraph.
  rewrite mxE; case: splitP => j ->.
    by rewrite leqNgt (leq_trans (ltn_ord j) (leq_addr _ _)).
  rewrite leq_add2l mxE; case: splitP => j' ->; last by rewrite mxE.
  by rewrite leqNgt ltn_ord.
rewrite geq_min leqNgt mn/= => km.
rewrite SAset_cast_le// SAset_cast_le ?(ltnW mn)//.
rewrite SAset_cast_le ?(ltnW (leq_ltn_trans km mn))//.
apply/eqP/SAsetP => x; rewrite -[X in nquantify X](size_ngraph x).
apply/SAin_setP/SAin_setP => /nexistsP [y] => /rcf_satP.
  rewrite -[in X in rcf_sat _ X](subnKC km).
  rewrite -[y]ngraph_tnth -ngraph_cat => /SAin_setP.
  have mE: (k + (m - k))%N = size (ngraph x ++ y).
    by rewrite size_cat size_ngraph size_tuple subnKC.
  rewrite [X in nquantify X]mE -{2}[y]ngraph_tnth -ngraph_cat.
  move=> /nexistsP [] {mE}.
  rewrite ngraph_cat (subnKC km) ngraph_tnth => z hA.
  apply/nexistsP.
  have ->: (n - k)%N = (n - m + m - k)%N by rewrite subnK// (ltnW mn).
  have /eqP scat: size (y ++ z) = (n - m + m - k)%N.
    by rewrite size_cat !size_tuple addnC addnBA.
  by exists (Tuple scat) => /=; rewrite catA.
move=> /rcf_satP hy; apply/nexistsP.
have /eqP ts: size (take (m - k)%N y) = (m - k)%N.
  by rewrite size_takel// size_tuple leq_sub// ltnW.
exists (Tuple ts); rewrite -[in X in holds _ X](subnKC km).
rewrite -[Tuple ts]ngraph_tnth -ngraph_cat.
apply/rcf_satP/SAin_setP.
have mE: (k + (m - k))%N = size (ngraph x ++ Tuple ts).
  by rewrite size_cat size_ngraph size_tuple subnKC.
rewrite [X in nquantify X]mE -{2}[Tuple ts]ngraph_tnth -ngraph_cat.
apply/nexistsP.
rewrite ngraph_cat subnKC//.
have /eqP ds: size (drop (m - k)%N y) = (n - m)%N.
  rewrite size_drop size_tuple subnBA// addnC subnKC//.
  exact/(ltnW (leq_ltn_trans km mn)).
by exists (Tuple ds); rewrite -catA ngraph_tnth/= cat_take_drop.
Qed.

End SAsetTheory.
Section SAsetTheory.
Variables (F : rcfType) (n : nat).
Implicit Types (A B C : {SAset F^n}) (x y z : 'rV[F]_n) (s t : seq 'rV[F]_n).

Lemma SAset_castXl m (s : {SAset F^n}) (t : {SAset F^m}) :
  t != SAset0 F m -> SAset_cast n (s :*: t) = s.
Proof.
have [->|[] x0 xt _] := set0Vmem t; first by rewrite eqxx.
apply/eqP/SAsetP => x.
  apply/inSAset_castDn/idP => [[y [+ ->]]|xs].
  by rewrite inSAsetX => /andP[+ _].
by exists (row_mx x x0); rewrite inSAsetX row_mxKl row_mxKr xs.
Qed.

Definition SAset_disjoint (s1 s2 : {SAset F^n}) :=
  s1 :&: s2 == SAset0 F n.

Lemma SAset_disjointC (s1 s2 : {SAset F^n}) :
  SAset_disjoint s1 s2 = SAset_disjoint s2 s1.
Proof. by rewrite /SAset_disjoint SAsetIC. Qed.

Definition SAset_trivI (I : {fset {SAset F^n}}) :=
  [forall s1 : I,
    [forall s2 : I, (val s1 != val s2) ==> SAset_disjoint (val s1) (val s2)]].

Definition SAset_partition (I : {fset {SAset F^n}}) :=
  (SAset0 F n \notin I)
  && SAset_trivI I
  && (\big[@SAsetU F n/SAset0 F n]_(s : I) val s == SAsetT F n).

End SAsetTheory.

Section POrder.

Variable F : rcfType.

Variable n : nat.

Fact SAset_disp : unit. Proof. exact tt. Qed.

HB.instance Definition SAset_latticeType :=
  Order.isMeetJoinDistrLattice.Build SAset_disp {SAset _}
    (@SAsubsetEI F n) (@properEneq' F n) (@SAsetIC F n) (@SAsetUC F n)
    (@SAsetIA F n) (@SAsetUA F n) (@SAsetKU' F n) (@SAsetKI' F n)
    (@SAsetIUl F n) (@SAsetI_idem F n).

HB.instance Definition _ :=
  Order.hasBottom.Build SAset_disp {SAset F^n} (@sub0set F n).

HB.instance Definition SAset_tblatticeType :=
  Order.hasTop.Build SAset_disp {SAset F^n} (@subsetT F n).

HB.instance Definition _ :=
  Order.hasRelativeComplement.Build SAset_disp {SAset F^n}
    (@SAsetID0 F n) (@SAsetUID F n).

End POrder.

Section SAFunction.

Variable F : rcfType.

Variables (n m : nat).

Definition ftotal (f : {formula_(n + m) F}) :=
  nquantify O n Forall (nquantify n m Exists f).

Definition ex_y (f : {formula_(n + m) F}) (x : 'rV[F]_n) :=
  rcf_sat (ngraph x) (nquantify n m Exists f).

Definition SAtot :=
  [pred s : {SAset F ^ _} | rcf_sat [::] (ftotal s)].

Definition ext (p : nat) (f : {formula_p F}) : {formula_(p+m) F} :=
  MkFormulan (formuladd m f).

Lemma ftotalP (f : {formula_(n + m) F}) :
  reflect
    (forall (t : n.-tuple F), exists (u : m.-tuple F), rcf_sat (t ++ u) f)
    (rcf_sat [::] (ftotal f)).
Proof.
apply: (iffP idP) => [h x | h].
  move/rcf_satP/nforallP/(_ x) : h.
  case: x => s /= /eqP -{1}<-.
  by move/nexistsP => [t h]; exists t; apply/rcf_satP.
apply/rcf_satP/nforallP => x /=.
move/(_ x) : h => [t].
case: x => s /= /eqP -{2}<-.
by move/rcf_satP => h; apply/nexistsP; exists t.
Qed.

Definition functional (f : {formula_(n+m) F}) :=
  (nquantify O (n + m + m) Forall (
    ((subst_formula (iota 0 n ++ iota n m) f)
      /\ (subst_formula (iota 0 n ++ iota (n + m) m) f))
    ==> (eq_vec F (iota n m) (iota (n + m) m)))).

Definition SAfunc :=
  [pred s : {SAset F ^ _} | rcf_sat [::] (functional s)].

Lemma functionalP (f : {formula_(n + m) F}) :
  reflect
    (forall (t : n.-tuple F) (u1 u2 : m.-tuple F),
      rcf_sat (t ++ u1) f -> rcf_sat (t ++ u2) f -> u1 = u2)
    (rcf_sat [::] (functional f)).
Proof.
rewrite /functional !nquantify_add !add0n.
apply: (iffP idP).
+ move=> func t u1 u2 tu1f tu2f.
  move: func => /rcf_satP/nforallP /= /(_ t).
  rewrite -[in X in nquantify X](size_tuple t).
  move=> /nforallP /(_ u1).
  rewrite -[in X in nquantify X](size_tuple t).
  rewrite -[in X in nquantify X](size_tuple u1).
  rewrite -size_cat.
  move=> /nforallP /(_ u2) /=.
  rewrite !holds_subst !holds_eq_vec !subst_env_cat -catA.
  rewrite subst_env_iota_catl ?size_tuple //.
  rewrite subst_env_iota ?size_tuple //.
  rewrite catA -[(t ++ u1) ++ u2]cats0 -catA.
  rewrite subst_env_iota ?size_tuple //.
  move=> /(_ _) /val_inj; apply.
  by split; apply/rcf_satP.
+ move=> h; apply/rcf_satP/nforallP => v /=.
  rewrite -[in X in nquantify X](size_tuple v).
  apply/nforallP => w /=.
  rewrite -[in X in nquantify X](size_tuple v).
  rewrite -[in X in nquantify X](size_tuple w) -size_cat.
  apply/nforallP => z.
  rewrite -catA /= !holds_subst !holds_eq_vec !subst_env_cat.
  move=> [/rcf_satP h1 /rcf_satP h2].
  move: ((h [tuple of (subst_env (iota 0 n) (v ++ w ++ z))]
            [tuple of (subst_env (iota n m) (v ++ w ++ z))]
            [tuple of (subst_env (iota (n + m) m) (v ++ w ++ z))]) h1 h2).
  by move/(congr1 val).
Qed.

Lemma inSAtot (s : {SAset F ^ (n + m)}) :
  reflect (forall x, exists y, (row_mx x y) \in s) (s \in SAtot).
Proof.
rewrite inE; apply: (iffP (ftotalP _)) => s_sat x.
  have [y sat_s_xy] := s_sat (ngraph x).
  exists (\row_(i < m) (nth 0 y i)).
  by rewrite inE ngraph_cat ngraph_nth.
have [y xy_in_s] := s_sat ((\row_(i < n) (nth 0 x i))).
exists (ngraph y).
by move: xy_in_s; rewrite inE ngraph_cat ngraph_nth.
Qed.

Lemma inSAfunc (s : {SAset F ^ (n + m)}) :
  reflect
    (forall x y1 y2, (row_mx x y1) \in s -> (row_mx x y2) \in s -> y1 = y2)
    (s \in SAfunc).
Proof.
rewrite inE; apply: (iffP (functionalP _)) => fun_s x y1 y2.
  rewrite !inE !ngraph_cat => /fun_s fun_s1 /fun_s1.
  exact/bij_inj/ngraph_bij.
move=> s_sat1 s_sat2.
suff eq_y12 : (\row_(i < m) (nth 0 y1 i)) = (\row_(i < m) (nth 0 y2 i)).
  apply/eq_from_tnth => i.
  have /rowP /(_ i) := eq_y12.
  by rewrite !mxE !(tnth_nth 0).
by apply: (fun_s (\row_(i < n) (nth 0 x i)));
rewrite inE !ngraph_cat !ngraph_nth.
Qed.

Lemma ex_yE (f : {formula_(n + m) F}) (t : 'rV[F]_n) :
  reflect (exists (u : 'rV[F]_m), rcf_sat (ngraph (row_mx t u)) f) (ex_y f t).
Proof.
apply: (iffP idP); rewrite /ex_y.
  rewrite -{1}[X in nquantify X _ _](size_ngraph t).
  move/rcf_satP/nexistsP=> [u  h].
  exists (\row_(i < m) (nth 0 u i)).
  by rewrite ngraph_cat ngraph_nth; apply/rcf_satP.
move=> [u]; rewrite ngraph_cat => ftu.
apply/rcf_satP; rewrite -{1}[X in nquantify X _ _](size_ngraph t).
by apply/nexistsP; exists (ngraph u); apply/rcf_satP.
Qed.

Definition form_to_fun (f : {formula_(n + m) F}) (x : 'rV[F]_n) : 'rV[F]_m :=
  match boolP (ex_y f x) with
| AltTrue p => proj1_sig (sigW (ex_yE f x p))
| AltFalse _ => (\row_(i < m) 0)
end.

Record SAfun := MkSAfun
{
  SAgraph :> {SAset F ^ (n + m)};
  _ : (SAgraph \in SAfunc) && (SAgraph \in SAtot)
}.

Definition SAfun_of of phant (F^n -> F^m) := SAfun.
Identity Coercion id_SAfun_of : SAfun_of >-> SAfun.
Local Notation "{ 'SAfun' }" := (SAfun_of (Phant (F^n -> F^m))).

HB.instance Definition SAfun_subType := [isSub for SAgraph].
HB.instance Definition SAfun_eqType := [Equality of SAfun by <:].
HB.instance Definition SAfun_choiceType := [Choice of SAfun by <:].

HB.instance Definition SAfun_of_subType := SubType.copy {SAfun} SAfun.
HB.instance Definition SAfun_of_eqType := Equality.copy {SAfun} SAfun.
HB.instance Definition SAfun_of_choiceType := Choice.copy {SAfun} SAfun.

Lemma SAfun_func (f : {SAfun}) x y1 y2 :
  row_mx x y1 \in SAgraph f -> row_mx x y2 \in SAgraph f -> y1 = y2.
Proof. by apply: inSAfunc; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Lemma SAfun_tot (f : {SAfun}) (x : 'rV[F]_n) :
  exists y, row_mx x y \in SAgraph f.
Proof. by apply: inSAtot; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Definition SAfun_to_fun (f : SAfun) x := proj1_sig (sigW (SAfun_tot f x)).

Coercion SAfun_to_fun : SAfun >-> Funclass.

Lemma SAfun_functional (f : {SAfun}) : rcf_sat [::] (functional (SAgraph f)).
Proof. by move: f => [g /= /andP [functional_g _]]. Qed.

Lemma SAfun_ftotal (f : {SAfun}) : rcf_sat [::] (ftotal (SAgraph f)).
Proof. by move: f => [g /= /andP [_ ftotal_g]]. Qed.

End SAFunction.
Arguments SAfunc {F n m}.
Arguments SAtot {F n m}.
Notation "{ 'SAfun' T }" := (SAfun_of (Phant T)) : type_scope.

Section SAfunTheory.

Variable (F : rcfType) (n m : nat).

Lemma inSAgraph (f : {SAfun F^n -> F^m}) x :
  row_mx x (f x) \in SAgraph f.
Proof.
by rewrite /SAfun_to_fun; case: ((sigW (SAfun_tot f x))) => y h.
Qed.

Lemma inSAfun (f : {SAfun F^n -> F^m}) x y :
   (f x == y) = (row_mx x y \in SAgraph f).
Proof.
apply/eqP/idP => [<- | h]; first by rewrite inSAgraph.
exact: (SAfun_func (inSAgraph _ _)).
Qed.

Lemma SAfunE (f1 f2 : {SAfun F^n -> F^m}) :
  reflect (f1 =1 f2) (f1 == f2).
Proof.
apply: (iffP idP); first by move/eqP ->.
move=> h; apply/SAsetP => x.
by rewrite -(cat_ffun_id x) -!inSAfun h.
Qed.

Definition SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) : {SAset F^m} :=
  [set | nquantify m n Exists ((subst_formula ((iota m n)
          ++ (iota O m)) f) /\ (subst_formula (iota m n) s)) ].

Lemma inSAimset (f : {SAfun F^n -> F^m}) s x :
  x \in s -> f x \in SAimset f s.
Proof.
rewrite pi_form /= => h.
apply/rcf_satP/holds_subst.
rewrite -[map _ _]cats0 subst_env_iota_catl ?size_ngraph //.
rewrite -[X in nquantify X _ _](size_ngraph (f x)); apply/nexistsP.
exists (ngraph x).
split; apply/holds_subst; move: h; rewrite inE => /rcf_satP hs; last first.
+ rewrite -[_ ++ ngraph x]cats0.
  by rewrite -catA subst_env_iota // size_ngraph.
+ rewrite subst_env_cat subst_env_iota_catl ?size_ngraph //.
  rewrite -[_ ++ ngraph x]cats0.
  rewrite -catA subst_env_iota ?size_ngraph //.
  by move: (inSAgraph f x); rewrite inE => /rcf_satP; rewrite ngraph_cat.
Qed.

Lemma SAimsetP (f : {SAfun F^n -> F^m}) s y :
  reflect (exists2 x, x \in s & y = f x) (y \in (SAimset f s)).
Proof.
apply: (iffP idP) => [/SAin_setP|[x h]->]; last exact: inSAimset.
rewrite -[X in nquantify X _ _ _](size_ngraph y) => /nexistsP [t] /=.
rewrite !holds_subst subst_env_cat => -[h1 h2].
exists (\row_(i < n) t`_i).
+ rewrite inE ngraph_nth.
  apply/rcf_satP.
  move: h2; rewrite -[ngraph y ++ t]cats0 -catA.
  by rewrite subst_env_iota //  ?size_tuple.
+ move: h1.
  rewrite subst_env_iota_catl ?size_ngraph //.
  rewrite -[ngraph y ++ t]cats0 -catA.
  rewrite subst_env_iota ?size_ngraph // ?size_tuple //.
  rewrite /SAfun_to_fun; case: sigW => /= x h h'.
  symmetry; apply: (SAfun_func h).
  by rewrite inE ngraph_cat ngraph_nth; apply/rcf_satP.
Qed.

Definition SApreimset (f : {SAfun F^n -> F^m}) (s : {SAset F^m}) : {SAset F^n}
  := [set | nquantify n m Exists (f /\ (subst_formula (iota n m) s)) ].

Lemma inSApreimset (f : {SAfun F^n -> F^m}) s x :
  x \in SApreimset f s = (f x \in s).
Proof.
apply/SAin_setP/rcf_satP => [|fxs];
  rewrite -[X in nquantify X](size_ngraph x).
  move=> /nexistsP [y] /= [].
  rewrite -{1}[y]ngraph_tnth -ngraph_cat => xyf /holds_subst.
  have ->: (f x = \row_i tnth y i).
    by apply/eqP; rewrite inSAfun inE; apply/rcf_satP.
  rewrite subst_env_iota_catr ?size_ngraph// ?size_tuple//.
  by rewrite -{1}[y]ngraph_tnth.
apply/nexistsP; exists (ngraph (f x)); rewrite -ngraph_cat => /=; split.
  by move: (inSAgraph f x); rewrite inE => /rcf_satP.
apply/holds_subst; rewrite ngraph_cat subst_env_iota_catr// ?size_ngraph//.
Qed.

Definition SAepigraph (f : {SAfun F^n -> F^1}) : {SAset F^(n + 1)} := 
  [set | nquantify (n + 1) 1 Exists ((subst_formula ((iota 0 n)
  ++ [:: n.+1; n]) f) /\ ('X_n.+1 <% 'X_n)) ].

Definition SAhypograph (f : {SAfun F^n -> F^1}) : {SAset F^(n + 1)} := 
  [set | nquantify (n + 1) 1 Exists ((subst_formula ((iota 0 n)
  ++ [:: n.+1; n]) f) /\ ('X_n <% 'X_n.+1)) ].

End SAfunTheory.

Lemma inSAepigraph (F : rcfType) (n : nat) (f : {SAfun F^n -> F^1}) x :
  (x \in SAepigraph f) = (f (lsubmx x) ord0 ord0 < rsubmx x ord0 ord0).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
apply/SAin_setP/idP; rewrite -[X in nquantify X _ _](size_ngraph (row_mx l r)).
  move=> /nexistsP [y] /= [] /holds_subst.
  rewrite nth_cat size_map size_enum_ord {11 20}addn1 ltnn subnn.
  rewrite nth_cat size_map size_enum_ord {11}addn1 leqnn.
  rewrite (nth_map (unsplit (inr ord0))) ?size_enum_ord ?addn1//.
  have {26}->: n = @unsplit n 1 (inr ord0) by rewrite /= addn0.
  rewrite nth_ord_enum mxE unsplitK ngraph_cat -catA subst_env_cat.
  rewrite subst_env_iota_catl ?size_ngraph//= !nth_cat size_map size_enum_ord.
  rewrite ltnNge leqnSn/= subSnn size_ngraph/= ltnn !subnn/=.
  rewrite (nth_map ord0) ?size_enum_ord//.
  rewrite -[X in nth ord0 _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
  move=> /holds_take; rewrite take_cat size_ngraph ltnNge {1}addn1 leqnSn/=.
  rewrite subDnCA// subnn/= => hf; congr (_ < _).
  transitivity ((\row_i tnth y i) ord0 ord0); first by rewrite mxE (tnth_nth 0).
  congr (_ _ ord0 ord0); apply/esym/eqP => /=; rewrite inSAfun.
  apply/rcf_satP; move: hf; congr holds; apply/(eq_from_nth (x0:=0)) => [|i].
    by rewrite size_cat size_map size_enum_ord size_ngraph.
  rewrite size_cat size_map size_enum_ord /= => ilt.
  have i0: 'I_(n+1) by rewrite addn1; exact: ord0.
  rewrite (nth_map (Ordinal ilt)) ?size_enum_ord// -[i%N]/(Ordinal ilt : nat).
  rewrite nth_ord_enum mxE -{1}(splitK (Ordinal ilt)); case: (split _) => j.
    rewrite nth_cat size_map size_enum_ord ltn_unsplit/=.
    by rewrite (nth_map j) ?size_enum_ord// nth_ord_enum /=.
  rewrite nth_cat/= size_ngraph ltnNge leq_addr/= subDnCA// subnn addn0.
  by case: j; case=> //= jlt; rewrite mxE (tnth_nth 0).
move=> fx; apply/nexistsP; exists (in_tuple [:: f l ord0 ord0]).
split; last first.
  rewrite /= !nth_cat size_ngraph {1 10 11}addn1 ltnn leqnn subnn/=.
  rewrite (nth_map (unsplit (inr ord0))) ?size_enum_ord ?addn1//.
  have {12}->: n = @unsplit n 1 (inr ord0) by rewrite /= addn0.
  by rewrite nth_ord_enum mxE unsplitK.
apply/holds_subst; rewrite ngraph_cat -catA subst_env_cat.
rewrite subst_env_iota_catl ?size_ngraph//= !nth_cat !size_ngraph ltnNge.
rewrite leqnSn/= subSnn/= ltnn subnn/=.
apply/holds_take; rewrite take_cat size_ngraph ltnNge leq_addr/=.
rewrite subDnCA// subnn/=.
have ->: (ngraph l) ++ [:: f l ord0 ord0] = ngraph (row_mx l (f l)).
  rewrite ngraph_cat; congr (_ ++ _); apply/(eq_from_nth (x0:=0)) => [|/=].
    by rewrite size_ngraph.
  case=> //= _; rewrite (nth_map ord0) ?size_enum_ord//.
  by rewrite -[X in nth _ _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
by move: (inSAfun f l (f l)); rewrite eqxx => /esym/rcf_satP.
Qed.

Lemma inSAhypograph (F : rcfType) (n : nat) (f : {SAfun F^n -> F^1}) x :
  (x \in SAhypograph f) = (rsubmx x ord0 ord0 < f (lsubmx x) ord0 ord0).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
apply/SAin_setP/idP; rewrite -[X in nquantify X _ _](size_ngraph (row_mx l r)).
  move=> /nexistsP [y] /= [] /holds_subst.
  rewrite !nth_cat size_map size_enum_ord {11 21 30}addn1 leqnn ltnn subnn.
  rewrite (nth_map (unsplit (inr ord0))) ?size_enum_ord ?addn1//.
  have {26}->: n = @unsplit n 1 (inr ord0) by rewrite /= addn0.
  rewrite nth_ord_enum mxE unsplitK ngraph_cat -catA subst_env_cat.
  rewrite subst_env_iota_catl ?size_ngraph//= !nth_cat size_map size_enum_ord.
  rewrite ltnNge leqnSn/= subSnn size_ngraph/= ltnn !subnn/=.
  rewrite (nth_map ord0) ?size_enum_ord//.
  rewrite -[X in nth ord0 _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
  move=> /holds_take; rewrite take_cat size_ngraph ltnNge {1}addn1 leqnSn/=.
  rewrite subDnCA// subnn/= => hf; congr (_ < _).
  transitivity ((\row_i tnth y i) ord0 ord0); first by rewrite mxE (tnth_nth 0).
  congr (_ _ ord0 ord0); apply/esym/eqP => /=; rewrite inSAfun.
  apply/rcf_satP; move: hf; congr holds; apply/(eq_from_nth (x0:=0)) => [|i].
    by rewrite size_cat size_map size_enum_ord size_ngraph.
  rewrite size_cat size_map size_enum_ord /= => ilt.
  have i0: 'I_(n+1) by rewrite addn1; exact: ord0.
  rewrite (nth_map (Ordinal ilt)) ?size_enum_ord// -[i%N]/(Ordinal ilt : nat).
  rewrite nth_ord_enum mxE -{1}(splitK (Ordinal ilt)); case: (split _) => j.
    rewrite nth_cat size_map size_enum_ord ltn_unsplit/=.
    by rewrite (nth_map j) ?size_enum_ord// nth_ord_enum /=.
  rewrite nth_cat/= size_ngraph ltnNge leq_addr/= subDnCA// subnn addn0.
  by case: j; case=> //= jlt; rewrite mxE (tnth_nth 0).
move=> fx; apply/nexistsP; exists (in_tuple [:: f l ord0 ord0]).
split; last first.
  rewrite /= !nth_cat size_ngraph {1 11 20}addn1 ltnn leqnn subnn/=.
  rewrite (nth_map (unsplit (inr ord0))) ?size_enum_ord ?addn1//.
  have {11}->: n = @unsplit n 1 (inr ord0) by rewrite /= addn0.
  by rewrite nth_ord_enum mxE unsplitK.
apply/holds_subst; rewrite ngraph_cat -catA subst_env_cat.
rewrite subst_env_iota_catl ?size_ngraph//= !nth_cat !size_ngraph ltnNge.
rewrite leqnSn/= subSnn/= ltnn subnn/=.
apply/holds_take; rewrite take_cat size_ngraph ltnNge leq_addr/=.
rewrite subDnCA// subnn/=.
have ->: (ngraph l) ++ [:: f l ord0 ord0] = ngraph (row_mx l (f l)).
  rewrite ngraph_cat; congr (_ ++ _); apply/(eq_from_nth (x0:=0)) => [|/=].
    by rewrite size_ngraph.
  case=> //= _; rewrite (nth_map ord0) ?size_enum_ord//.
  by rewrite -[X in nth _ _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
by move: (inSAfun f l (f l)); rewrite eqxx => /esym/rcf_satP.
Qed.

Section SAfunOps.

Variable (F : rcfType).

Definition abs (i j : nat) : formula F :=
  ((('X_j == 'X_i) \/ ('X_j == - 'X_i)) /\ (0 <=% 'X_j))%oT.

Lemma absP (e : seq F) (i j : nat) : holds e (abs i j) <-> e`_j = `|e`_i|.
Proof.
rewrite /abs /=; split=> [|->].
  move=> [[->|-> h]]; first by move=> h; rewrite ger0_norm.
  by rewrite ler0_norm // -oppr_gte0.
rewrite normr_ge0; split => //.
have [le_e0|lt_0e] := ler0P e`_i; first by right.
by left.
Qed.

Lemma absP2 (e : seq F) (i j : nat) : rcf_sat e (abs i j) = (e`_j == `|e`_i|).
Proof. by apply/rcf_satP/eqP => [/absP //|h]; apply/absP. Qed.

Fact nvar_abs (i j : nat) : @nvar F (maxn i j).+1 (abs i j).
Proof.
rewrite /nvar -maxnSS !fsubUset !fsub1set !seq_fsetE !mem_iota.
by rewrite !add0n !maxnSS !ltnS leq_maxl leq_maxr fsub0set.
Qed.

Fact nvar_abs2 : @nvar F (1 + 1) (abs O 1).
Proof. by rewrite /nvar !fsubUset !fsub1set !seq_fsetE fsub0set. Qed.

Definition absset := \pi_{SAset F ^ (1 + 1)} (MkFormulan nvar_abs2).

Lemma functional_absset : absset \in SAfunc.
Proof.
apply/rcf_satP/nforallP => t.
move=> [/holds_subst/holds_repr_pi/absP h1 /holds_subst/holds_repr_pi/absP h2].
apply/holds_eq_vec; move: h1 h2; case: t => s _ /=. 
by case: s => // a; case=> // b + -> /= {b}; case=> [<-|b _ ->].
Qed.

Lemma total_absset : absset \in SAtot.
Proof.
apply/rcf_satP/nforallP => t /=.
rewrite -[X in nquantify X _ _ _](size_tuple t).
apply/nexistsP.
have size_abs_t : (size [::`|t`_0|]) == 1%N by [].
exists (Tuple size_abs_t).
move: size_abs_t; case: t => s; case: s => // x s /=.
rewrite eqSS size_eq0 => /eqP -> _.
apply/holds_repr_pi => /=.
split; last by rewrite normr_ge0.
by case: (ler0P x); [right|left].
Qed.

Fact SAfun_SAabs : (absset \in SAfunc) && (absset \in SAtot).
Proof. by rewrite functional_absset total_absset. Qed.

Definition SAabs := MkSAfun SAfun_SAabs.

Definition SAid_graph (n : nat) : {SAset F^(n + n)} :=
  [set | \big[And/True]_(i : 'I_n) ('X_(n + i) == 'X_i)].

Lemma SAid_graphP n (x y : 'rV[F]_n) :
  (row_mx x y \in SAid_graph n) = (y == x).
Proof.
apply/SAin_setP/eqP => [/holdsAnd xy|->];
  [apply/rowP => i; move: xy => /(_ i (mem_index_enum _) isT) /=
 | apply/holdsAnd => i _ _ /=];
  (rewrite enum_ordD map_cat nth_catr;
    last by rewrite 2!size_map size_enum_ord);
  rewrite -map_comp (nth_map i) ?size_enum_ord// nth_ord_enum/=;
  rewrite nth_cat 2!size_map size_enum_ord ltn_ord -map_comp;
  rewrite (nth_map i) ?size_enum_ord// nth_ord_enum/= !mxE;
  by rewrite (unsplitK (inl i)) (unsplitK (inr i)).
Qed.

Lemma SAfun_SAid n :
  (SAid_graph n \in SAfunc) && (SAid_graph n \in SAtot).
Proof.
apply/andP; split; last by apply/inSAtot => y; exists y; rewrite SAid_graphP.
by apply/inSAfunc => x0 y1 y2; rewrite !SAid_graphP => /eqP -> /eqP.
Qed.

Definition SAid n := MkSAfun (SAfun_SAid n).

Lemma SAidE n (x : 'rV[F]_n) :
  SAid n x = x.
Proof. by apply/eqP; rewrite inSAfun /SAid SAid_graphP. Qed.

Definition comp_formula (m n p : nat)
 (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) : formula F :=
  nquantify (m + p) n Exists
  ((subst_formula ((iota O m) ++ (iota (m + p) n)) (repr (val f))) /\
  (subst_formula ((iota (m + p) n) ++ (iota m p)) (repr (val g)))).

Fact nvar_comp_formula (m n p : nat)
  (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) :
  @nvar F (m + p) (comp_formula f g).
Proof.
rewrite /nvar /comp_formula /= formula_fv_nexists fsubDset fsetUC -seq_fset_cat.
rewrite -iotaD /= fsubUset.
rewrite ?(fsubset_trans (fv_subst_formula mnfset_key _ _)) // => {f} {g};
rewrite seq_fset_cat fsubUset; apply/andP; split.
case: n=> [|n]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n.
case: p=> [|p]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n leq_addr.
case: m=> [|m]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n add0n -addnA leq_addr.
case: n=> [|n]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n.
Qed.

Definition SAcomp_graph (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :=
  \pi_{SAset F ^ (m + p)} (MkFormulan (nvar_comp_formula f g)).

Lemma holds_ngraph (m n : nat) (f : {SAfun F^m -> F^n}) (t : 'rV[F]_(m + n)) :
reflect (holds (ngraph t) f) (t \in SAgraph f).
Proof. by rewrite inE; apply: rcf_satP. Qed.

(* Who put composition in this direction? *)
Lemma SAcomp_graphP (m n p : nat)
  (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p})
  (u : 'rV[F]_m) (v : 'rV[F]_p) :
    (row_mx u v \in SAcomp_graph f g) = (g (f u) == v).
Proof.
rewrite /SAcomp_graph /= pi_form ngraph_cat /comp_formula.
have h : size ([seq u ord0 i | i <- enum 'I_m] ++
               [seq v ord0 i | i <- enum 'I_p]) = (m + p)%N.
  by rewrite size_cat size_map size_enum_ord size_map size_enum_ord.
rewrite /= -[X in nquantify X _ _ _]h.
apply/(sameP (rcf_satP _ _))/(equivP _ (nexistsP _ _ _))/(iffP idP).
  move/eqP => eq_gfu_v.
  exists (ngraph (f u)).
  split; apply/holds_subst; rewrite subst_env_cat.
    rewrite -catA subst_env_iota_catl; last by rewrite size_map size_enum_ord.
    rewrite catA subst_env_iota_catr ?size_tuple ?card_ord // -ngraph_cat.
    by apply/holds_ngraph; apply: inSAgraph.
  rewrite subst_env_iota_catr ?size_tuple ?card_ord //.
  rewrite -catA subst_env_iota; last 2 first.
    by rewrite size_map size_enum_ord.
  by rewrite size_map size_enum_ord.
  rewrite -ngraph_cat; apply/holds_ngraph; rewrite -eq_gfu_v.
  exact: inSAgraph.
move=> [t] /= [ /holds_subst + /holds_subst].
rewrite subst_env_cat -catA.
rewrite subst_env_iota_catl; last by rewrite size_map size_enum_ord.
rewrite catA subst_env_iota_catr ?size_tuple ?card_ord //.
rewrite subst_env_cat subst_env_iota_catr ?size_tuple ?card_ord //.
rewrite -catA subst_env_iota; first last.
- by rewrite size_map size_enum_ord.
- by rewrite size_map size_enum_ord.
rewrite -[t]ngraph_tnth -!ngraph_cat.
move/holds_ngraph; rewrite -inSAfun; move/eqP ->.
by move/holds_ngraph; rewrite -inSAfun; move/eqP ->.
Qed.

Fact SAfun_SAcomp (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :
  (SAcomp_graph f g \in SAfunc) && (SAcomp_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAcomp_graphP => /eqP -> /eqP ->.
by apply/inSAtot => x; exists (g (f x)); rewrite SAcomp_graphP.
Qed.

Definition SAcomp (m n p : nat) (f : SAfun F n p) (g : SAfun F m n) :=
  MkSAfun (SAfun_SAcomp g f).

Lemma SAcompE (m n p : nat) (f : SAfun F n p) (g : SAfun F m n) :
  SAcomp f g =1 f \o g.
Proof.
move=> x; apply/eqP; rewrite eq_sym -SAcomp_graphP.
by move: (inSAgraph (SAcomp f g) x).
Qed.

Definition SAfun_const_graph n m (x : 'rV[F]_m) : {SAset F^(n + m)%N} :=
  [set | \big[And/True]_(i : 'I_m)
      ('X_(@unsplit n m (inr i)) == GRing.Const (x ord0 i))].

Lemma SAfun_constP n m (x : 'rV[F]_m) y z :
  row_mx y z \in SAfun_const_graph n x = (z == x).
Proof.
apply/SAin_setP/eqP => [/holdsAnd zx|->].
  apply/rowP => i.
  move/(_ i): zx; rewrite mem_index_enum => /(_ isT isT).
  rewrite ngraph_cat/= nth_cat size_ngraph ltnNge leq_addr/=.
  by rewrite subDnCA// subnn addn0 nth_ngraph.
apply/holdsAnd => i _ _ /=.
rewrite ngraph_cat/= nth_cat size_ngraph ltnNge leq_addr/=.
by rewrite subDnCA// subnn addn0 nth_ngraph.
Qed.

Lemma SAfun_SAfun_const n m (x : 'rV[F]_m) :
  (SAfun_const_graph n x \in SAfunc) && (SAfun_const_graph n x \in SAtot).
Proof.
apply/andP; split.
  by apply/inSAfunc => x0 y1 y2; rewrite !SAfun_constP => /eqP -> /eqP.
by apply/inSAtot => y; exists x; rewrite SAfun_constP.
Qed.

Definition SAfun_const n m (x : 'rV[F]_m) := MkSAfun (SAfun_SAfun_const n x).

Lemma SAfun_constE n m (x : 'rV[F]_m) (y : 'rV[F]_n) : SAfun_const n x y = x.
Proof. by apply/eqP; rewrite inSAfun /SAfun_const SAfun_constP. Qed.

Definition join_formula (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) : formula F :=
  (repr (val f)) /\ (subst_formula (iota 0 m ++ iota (m+n) p) (repr (val g))).

Lemma nvar_join_formula (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) :
  @nvar F (m + (n + p)) (join_formula f g).
Proof.
rewrite /nvar /join_formula /=; apply/fsubUsetP; split.
  apply/(fsubset_trans (fsubset_formulan_fv f)).
  by rewrite mnfset0_sub addnA leq_addr.
apply/(fsubset_trans (fv_subst_formula mnfset_key _ g)).
rewrite seq_fset_cat; apply/fsubUsetP; split.
  by rewrite mnfset0_sub leq_addr.
case: {f g} p => [|p]; first by rewrite m0fset fsub0set.
by rewrite mnfset_sub //= !addnA.
Qed.

Definition SAjoin_graph (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) :=
  \pi_{SAset F^(m + (n + p))} (MkFormulan (nvar_join_formula f g)).

Lemma SAjoin_graphP (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) u v :
  (row_mx u v \in SAjoin_graph f g) = (row_mx (f u) (g u) == v).
Proof.
move: (lsubmx v) (rsubmx v) (hsubmxK v) => l r <- {v}.
rewrite /SAjoin_graph /= pi_form /join_formula /= !ngraph_cat.
apply: (sameP (rcf_satP _ _)).
apply: (iffP eqP) => [|/= [/holds_take + /holds_subst]];
    last first.
  rewrite subst_env_cat subst_env_iota_catl ?size_ngraph//.
  rewrite catA -ngraph_cat subst_env_iota_catr ?size_ngraph//.
  rewrite take_size_cat ?size_ngraph// -ngraph_cat.
  move=> /holds_ngraph + /holds_ngraph.
  by rewrite -!inSAfun => /eqP -> /eqP ->.
move=> /[dup] /(congr1 lsubmx) + /(congr1 rsubmx).
rewrite !row_mxKl !row_mxKr => <- <-.
split.
  rewrite catA -ngraph_cat; apply/holds_take.
  rewrite take_size_cat ?size_ngraph//.
  exact/holds_ngraph/inSAgraph.
apply/holds_subst; rewrite subst_env_cat subst_env_iota_catl ?size_ngraph//.
rewrite catA -ngraph_cat subst_env_iota_catr ?size_ngraph// -ngraph_cat.
exact/holds_ngraph/inSAgraph.
Qed.

Fact SAfun_SAjoin (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) :
  (SAjoin_graph f g \in SAfunc) && (SAjoin_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAjoin_graphP => /eqP <- /eqP.
by apply/inSAtot => x; exists (row_mx (f x) (g x)); rewrite SAjoin_graphP.
Qed.

Definition SAjoin (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) :=
  MkSAfun (SAfun_SAjoin f g).

Lemma SAjoinE (m n p : nat) (f : {SAfun F^m -> F^n})
    (g : {SAfun F^m -> F^p}) x :
  SAjoin f g x = row_mx (f x) (g x).
Proof. by apply/eqP; rewrite eq_sym -SAjoin_graphP; apply/inSAgraph. Qed.

Definition add_formula (p : nat) : formula F :=
  (\big[And/True]_(i : 'I_p) ('X_(i + 2 * p) == 'X_i + 'X_(i + p)))%oT.

Lemma nvar_add_formula p : nvar (p + p + p) (add_formula p).
Proof.
apply/fsubsetP => x; rewrite formula_fv_bigAnd => /bigfcupP [i _] /fset1UP.
by case=> [->|/fset2P [|] ->];
  rewrite mnfsetE /= add0n 1?mulSn ?mul1n ?addnA ?ltn_add2r// -[i.+1]add0n;
  apply/leq_add.
Qed.

Definition SAadd_graph p :=
  \pi_{SAset F^(p + p + p)} (MkFormulan (nvar_add_formula p)).

Lemma SAadd_graphP p u v :
  (row_mx u v \in SAadd_graph p) = (v == lsubmx u + rsubmx u)%R.
Proof.
rewrite rowPE.
apply/(sameP (rcf_satP _ _))/(equivP _ (iff_sym (holds_repr_pi _ _))) => /=.
apply/(equivP _ (iff_sym (holdsAnd _ _ _ _)))/forallPP => /= i.
rewrite mem_index_enum mul2n -addnn addnA.
rewrite -[(i + p + p)%N]addnA [(i + _)%N]addnC.
rewrite (nth_map (unsplit (inr i))) ?size_enum_ord ?rshift_subproof//.
rewrite (nth_ord_enum _ (rshift (p + p)%N i)) row_mxEr.
have {1}->: i = lshift p i :> nat by [].
rewrite (nth_map (unsplit (inr i))) ?size_enum_ord ?lshift_subproof//.
rewrite (nth_ord_enum _ (lshift p (lshift p i))) row_mxEl.
have ->: (i + p)%N = rshift p i :> nat by rewrite addnC.
rewrite (nth_map (unsplit (inr i))) ?size_enum_ord ?lshift_subproof//.
rewrite (nth_ord_enum _ (lshift p (rshift p i))) row_mxEl !mxE.
by apply/(iffP eqP) => // /(_ Logic.eq_refl) /(_ Logic.eq_refl).
Qed.

Fact SAfun_SAadd p :
  (SAadd_graph p \in @SAfunc _ (p + p) p)
  && (SAadd_graph p \in @SAtot _ (p + p) p).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAadd_graphP => /eqP -> /eqP.
apply/inSAtot => x; exists (lsubmx x + rsubmx x)%R.
by rewrite SAadd_graphP eqxx.
Qed.

Definition SAadd p := MkSAfun (SAfun_SAadd p).

Lemma SAaddE p x y : SAadd p (row_mx x y) = (x + y)%R.
Proof. by apply/eqP; rewrite inSAfun SAadd_graphP row_mxKl row_mxKr. Qed.

Definition SAfun_add n p (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAadd p) (SAjoin f g).

Lemma SAfun_addE n p (f g : {SAfun F^n -> F^p}) x :
  SAfun_add f g x = (f x + g x)%R.
Proof. by rewrite SAcompE/= SAjoinE SAaddE. Qed.

Definition opp_formula p : formula F :=
  (\big[And/True]_(i : 'I_p) ('X_(p + i) == - 'X_i))%oT.

Lemma nvar_opp_formula p : nvar (p + p) (opp_formula p).
Proof.
apply/fsubsetP => x; rewrite formula_fv_bigAnd => /bigfcupP [i _] /fset2P.
case=> ->; rewrite seq_fsetE mem_iota /= add0n; last exact/ltn_addl.
by rewrite ltn_add2l.
Qed.

Definition SAopp_graph p :=
  \pi_{SAset F^(p + p)} (MkFormulan (nvar_opp_formula p)).

Lemma SAopp_graphP p u v :
  (row_mx u v \in SAopp_graph p) = (v == - u)%R.
Proof.
rewrite rowPE.
apply/(sameP (rcf_satP _ _))/(equivP _ (iff_sym (holds_repr_pi _ _))) => /=.
apply/(equivP _ (iff_sym (holdsAnd _ _ _ _)))/forallPP => /= i.
rewrite mem_index_enum.
rewrite (nth_map (unsplit (inr i))) ?size_enum_ord ?rshift_subproof//.
rewrite (nth_ord_enum _ (rshift p i)) row_mxEr mxE.
rewrite (nth_map (unsplit (inr i))) ?size_enum_ord ?lshift_subproof//.
rewrite (nth_ord_enum _ (lshift p i)) row_mxEl.
by apply/(iffP eqP) => // /(_ Logic.eq_refl) /(_ Logic.eq_refl).
Qed.

Fact SAfun_SAopp p :
  (SAopp_graph p \in @SAfunc _ p p) && (SAopp_graph p \in @SAtot _ p p).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAopp_graphP => /eqP -> /eqP.
by apply/inSAtot => x; exists (-x)%R; rewrite SAopp_graphP eqxx.
Qed.

Definition SAopp p := MkSAfun (SAfun_SAopp p).

Lemma SAoppE p x : SAopp p x = - x.
Proof. by apply/eqP; rewrite inSAfun SAopp_graphP. Qed.

Definition SAfun_opp n p (f : {SAfun F^n -> F^p}) :=
  SAcomp (SAopp p) f.

Lemma SAfun_oppE n p (f : {SAfun F^n -> F^p}) x :
  SAfun_opp f x = - f x.
Proof. by rewrite SAcompE/= SAoppE. Qed.

Definition SAfun_sub n p (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAadd p) (SAjoin f (SAcomp (SAopp p) g)).

Lemma SAfun_subE n p (f g : {SAfun F^n -> F^p}) x :
  SAfun_sub f g x = f x - g x.
Proof. by rewrite SAcompE/= SAjoinE SAcompE/= SAoppE SAaddE. Qed.

Lemma SAfun_addA n p : associative (@SAfun_add n p).
Proof.
move=> f g h; apply/eqP/SAfunE => x.
by rewrite !SAfun_addE addrA.
Qed.

Lemma SAfun_addC n p : commutative (@SAfun_add n p).
Proof.
move=> f g; apply/eqP/SAfunE => x.
by rewrite !SAfun_addE addrC.
Qed.

Lemma SAfun_add0r n p : left_id (SAfun_const n (0 : 'rV[F]_p)) (@SAfun_add n p).
Proof.
move=> f; apply/eqP/SAfunE => x.
by rewrite SAfun_addE SAfun_constE add0r.
Qed.

Lemma SAfun_addNr n p :
  left_inverse (SAfun_const n (0 : 'rV[F]_p)) (@SAfun_opp n p) (@SAfun_add n p).
Proof.
move=> f; apply/eqP/SAfunE => x.
by rewrite SAfun_addE SAfun_oppE SAfun_constE addNr.
Qed.

HB.instance Definition _ n p := GRing.isZmodule.Build {SAfun F^n -> F^p}
  (@SAfun_addA n p) (@SAfun_addC n p) (@SAfun_add0r n p) (@SAfun_addNr n p).

Definition SAmul_graph p : {SAset F^(p + p + p)} :=
  [set| \big[And/True]_(i < p) ('X_(p.*2 + i) == 'X_i * 'X_(p + i))].

Lemma SAmul_graphP p u v :
  (row_mx u v \in SAmul_graph p)
  = (v == \row_i (lsubmx u 0 i * rsubmx u 0 i))%R.
Proof.
rewrite inE rcf_sat_repr_pi rcf_sat_subst -[_ (ngraph _)]cats0.
rewrite subst_env_iota_catl ?size_ngraph// rcf_sat_forall rowPE.
apply/eq_forallb => /= i.
rewrite !simp_rcf_sat/= enum_ordD map_cat !nth_cat 2!size_map size_enum_ord.
rewrite ltnNge -addnn leq_addr/= subDnCA// subnn addn0.
rewrite (leq_trans (ltn_ord i) (leq_addr _ _))/=.
rewrite ltn_add2l ltn_ord/= -map_comp nth_map_ord.
have iE: i = lshift p i :> nat by [].
rewrite [X in _`_X]iE -map_comp nth_map_ord.
have {}iE: p + i = rshift p i :> nat by [].
by rewrite [X in _`_X]iE nth_map_ord !mxE/= (unsplitK (inr _)) !(unsplitK (inl _)).
Qed.

Fact SAfun_SAmul p :
  (SAmul_graph p \in @SAfunc _ (p + p) p)
  && (SAmul_graph p \in @SAtot _ (p + p) p).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAmul_graphP => /eqP -> /eqP.
apply/inSAtot => x; exists (\row_i (lsubmx x 0 i * rsubmx x 0 i))%R.
by rewrite SAmul_graphP eqxx.
Qed.

Definition SAmul p := MkSAfun (SAfun_SAmul p).

Lemma SAmulE p x y : SAmul p (row_mx x y) = \row_i (x 0 i * y 0 i)%R.
Proof. by apply/eqP; rewrite inSAfun SAmul_graphP row_mxKl row_mxKr. Qed.

Definition SAfun_mul n p (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAmul p) (SAjoin f g).

Lemma SAfun_mulE n p (f g : {SAfun F^n -> F^p}) x :
  SAfun_mul f g x = \row_i (f x 0 i * g x 0 i)%R.
Proof. by rewrite SAcompE/= SAjoinE SAmulE. Qed.

Definition SAinv_graph n : {SAset F^(n + n)} :=
  [set| \big[And/True]_(i < n)
      ('X_i * 'X_(n + i) == Const 1%R
      \/ 'X_i == Const 0%R /\ 'X_(n + i) == Const 0%R)].

Lemma SAinv_graphP n x y :
  row_mx x y \in SAinv_graph n = (y == \row_i (x 0 i)^-1).
Proof.
rewrite inE rcf_sat_repr_pi rcf_sat_subst -[_ (ngraph _)]cats0.
rewrite subst_env_iota_catl ?size_ngraph// rcf_sat_forall rowPE.
apply/eq_forallb => /= i.
rewrite !simp_rcf_sat/= enum_ordD map_cat !nth_cat 2!size_map size_enum_ord.
rewrite (ltn_ord i) ltnNge leq_addr/= subDnCA// subnn addn0.
rewrite -map_comp nth_map_ord -map_comp nth_map_ord !mxE/=.
rewrite (unsplitK (inl _)) (unsplitK (inr _)).
have [->|x0] := eqVneq (x 0 i) 0.
  by rewrite invr0 mul0r eq_sym oner_eq0/=.
by rewrite orbF -(divff x0) -subr_eq0 -mulrBr mulf_eq0 (negPf x0)/= subr_eq0.
Qed.

Fact SAfun_SAinv p :
  (SAinv_graph p \in @SAfunc _ p p) && (SAinv_graph p \in @SAtot _ p p).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAinv_graphP => /eqP -> /eqP.
by apply/inSAtot => x; exists (\row_i (x 0 i)^-1)%R; rewrite SAinv_graphP eqxx.
Qed.

Definition SAinv p := MkSAfun (SAfun_SAinv p).

Lemma SAinvE p x : SAinv p x = \row_i (x 0 i)^-1.
Proof. by apply/eqP; rewrite inSAfun SAinv_graphP. Qed.

Definition SAfun_inv n p (f : {SAfun F^n -> F^p}) :=
  SAcomp (SAinv p) f.

Lemma SAfun_invE n p (f : {SAfun F^n -> F^p}) x :
  SAfun_inv f x = \row_i (f x 0 i)^-1.
Proof. by rewrite SAcompE/= SAinvE. Qed.

Definition SAfun_div n p (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAmul p) (SAjoin f (SAcomp (SAinv p) g)).

Lemma SAfun_divE n p (f g : {SAfun F^n -> F^p}) x :
  SAfun_div f g x = \row_i (f x 0 i / g x 0 i).
Proof.
rewrite SAcompE/= SAjoinE SAcompE/= SAinvE SAmulE.
by apply/rowP => i; rewrite !mxE.
Qed.

Definition SAfun_le n (f g : {SAfun F^n -> F^1}) :=
  SAgraph (SAfun_sub g f) :<=: (SAsetT F n) :*: (SAset_itv `[0, +oo[%R).

Lemma SAfun_leP n (f g : {SAfun F^n -> F^1}) :
  reflect (forall x, f x ord0 ord0 <= g x ord0 ord0) (SAfun_le f g).
Proof.
apply/(iffP (SAset_subP _ _)) => fg x.
  move/(_ (row_mx x (g x - f x))) : fg.
  rewrite -inSAfun SAfun_subE => /(_ (eqxx _)).
  rewrite inSAsetX row_mxKl row_mxKr inSAset_itv in_itv/= !mxE subr_ge0 andbT.
  by move=> /andP[_].
rewrite -[x]hsubmxK -inSAfun SAfun_subE inSAsetX row_mxKl row_mxKr => /eqP <-.
move/(_ (lsubmx x)): fg.
by rewrite inSAsetT inSAset_itv in_itv/= !mxE subr_ge0 andbT.
Qed.

(* alias on which we define the porder on functions *)
Definition SAfunleType n := {SAfun F^n -> F^1}.

HB.instance Definition _ n := Equality.on (SAfunleType n).
HB.instance Definition _ n := Choice.on (SAfunleType n).

Lemma SAfun_le_refl n : reflexive (@SAfun_le n).
Proof. by move=> f; apply/SAfun_leP => x; apply/lexx. Qed.

Lemma SAfun_le_anti n : antisymmetric (@SAfun_le n).
Proof.
move=> f g /andP[] /SAfun_leP fg /SAfun_leP gf; apply/eqP/SAfunE => x.
apply/rowP; case; case => [|//] lt01; apply/le_anti.
have ->: Ordinal lt01 = 0 by apply/val_inj.
by apply/andP; split.
Qed.

Lemma SAfun_le_trans n : transitive (@SAfun_le n).
Proof.
move=> f g h /SAfun_leP gf /SAfun_leP fh; apply/SAfun_leP => x.
exact/(le_trans (gf x) (fh x)).
Qed.

HB.instance Definition _ n :=
  Order.Le_isPOrder.Build ring_display (SAfunleType n) (@SAfun_le_refl n)
    (@SAfun_le_anti n) (@SAfun_le_trans n).

Definition SAfun_lt n (f g : {SAfun F^n -> F^1}) :=
  SAgraph (SAfun_sub g f) :<=: (SAsetT F n) :*: (SAset_pos F).

Lemma SAfun_ltP n (f g : {SAfun F^n -> F^1}) :
  reflect (forall x, f x ord0 ord0 < g x ord0 ord0) (SAfun_lt f g).
Proof.
apply/(iffP (SAset_subP _ _)) => fg x.
  move/(_ (row_mx x (g x - f x))) : fg.
  rewrite -inSAfun SAfun_subE => /(_ (eqxx _)).
  by rewrite inSAsetX row_mxKl row_mxKr inSAset_pos !mxE subr_gt0 => /andP[_].
rewrite -[x]hsubmxK -inSAfun SAfun_subE inSAsetX row_mxKl row_mxKr => /eqP <-.
by move/(_ (lsubmx x)): fg; rewrite inSAsetT inSAset_pos !mxE  subr_gt0.
Qed.

(* alias on which we define the strict order on functions *)
Definition SAfunltType n := {SAfun F^n -> F^1}.

HB.instance Definition _ n := Equality.on (SAfunltType n).
HB.instance Definition _ n := Choice.on (SAfunltType n).

Lemma SAfun_lt_irr n : irreflexive (@SAfun_lt n).
Proof. by move=> f; apply/negP => /SAfun_ltP /(_ 0); rewrite ltxx. Qed.

Lemma SAfun_lt_trans n : transitive (@SAfun_lt n).
Proof.
move=> f g h /SAfun_ltP gf /SAfun_ltP fh; apply/SAfun_ltP => x.
exact/(lt_trans (gf x) (fh x)).
Qed.

HB.instance Definition _ n :=
  Order.Lt_isPOrder.Build ring_display (SAfunltType n) (@SAfun_lt_irr n)
    (@SAfun_lt_trans n).

Definition SAmpoly_graph n (p : {mpoly F[n]}) : {SAset F^(n + 1)} :=
  [set | 'X_n == term_mpoly p (fun i => 'X_i)].

Lemma SAmpoly_graphP n (p : {mpoly F[n]}) x y :
  (row_mx x y \in SAmpoly_graph p) = (y ord0 ord0 == p.@[x ord0]).
Proof.
by apply/SAin_setP/eqP; rewrite /= eval_term_mpoly enum_ordD/= map_cat;
  rewrite nth_cat/= -map_comp size_map size_enum_ord ltnn subnn enum_ordSl;
  rewrite enum_ord0/= row_mxEr => ->; apply/meval_eq => i /=;
  rewrite nth_cat size_map size_enum_ord (ltn_ord i);
  rewrite (nth_map i) ?size_enum_ord// nth_ord_enum/= row_mxEl.
Qed.

Lemma SAfun_SAmpoly n p :
  (SAmpoly_graph p \in @SAfunc _ n 1) && (SAmpoly_graph p \in @SAtot _ n 1).
Proof.
apply/andP; split.
  apply/inSAfunc => x y1 y2; rewrite !SAmpoly_graphP => /eqP <- /eqP y12.
  apply/rowP; case; case=> //= lt01.
  by move/esym: y12; congr (_ = _); congr (_ _ _); apply/val_inj.
by apply/inSAtot => x; exists (\row__ p.@[x ord0]); rewrite SAmpoly_graphP mxE.
Qed.

Definition SAmpoly n (p : {mpoly F[n]}) := MkSAfun (SAfun_SAmpoly p).

Lemma SAmpolyE n (p : {mpoly F[n]}) x :
  SAmpoly p x = \row__ p.@[x ord0].
Proof. by apply/eqP; rewrite inSAfun SAmpoly_graphP !mxE. Qed.

Definition SAselect_graph n m s : {SAset F^(n + m)} :=
  [set| \big[And/True]_(i : 'I_m)
      ('X_(n + i) == 'X_(if (n <= (s`_i)%R)%N then ((s`_i)%R + m)%N else s`_i))].

Lemma SAselect_graphP n m s u v :
  (row_mx u v \in SAselect_graph n m s) = (v == \row_i (ngraph u)`_(s`_i))%R.
Proof.
apply/SAin_setP/eqP => /= [|->].
  move=> /holdsAnd vE; apply/rowP => i.
  move: vE => /(_ i (mem_index_enum _) isT)/=.
  rewrite enum_ordD map_cat nth_catr 2?size_map ?size_enum_ord//.
  rewrite -map_comp (nth_map i) ?size_enum_ord// nth_ord_enum/= !mxE.
  rewrite (unsplitK (inr i)) nth_cat 2!size_map size_enum_ord.
  case: (ltnP (s`_i)%R n) => ni ->.
    rewrite ni -map_comp (nth_map (Ordinal ni)) ?size_enum_ord//.
    rewrite (nth_map (Ordinal ni)) ?size_enum_ord//.
    rewrite -[s`_i]/(nat_of_ord (Ordinal ni)) nth_ord_enum/= mxE.
    by rewrite (unsplitK (inl (Ordinal ni))).
  rewrite ltnNge (leq_trans ni (leq_addr _ _))/= nth_default.
    by rewrite nth_default// size_map size_enum_ord.
  by rewrite size_map size_enum_ord -addnBAC// leq_addl.
apply/holdsAnd => i _ _ /=.
rewrite enum_ordD map_cat nth_catr 2?size_map ?size_enum_ord//.
rewrite -map_comp (nth_map i) ?size_enum_ord// nth_ord_enum/= !mxE.
rewrite (unsplitK (inr i)) mxE nth_cat 2!size_map size_enum_ord.
case: (ltnP (s`_i)%R n) => ni.
  rewrite ni -map_comp (nth_map (Ordinal ni)) ?size_enum_ord//.
  rewrite (nth_map (Ordinal ni)) ?size_enum_ord//.
  rewrite -[s`_i]/(nat_of_ord (Ordinal ni)) nth_ord_enum/= mxE.
  by rewrite (unsplitK (inl (Ordinal ni))).
rewrite ltnNge (leq_trans ni (leq_addr _ _))/= nth_default; last first.
  by rewrite size_map size_enum_ord.
by rewrite nth_default// size_map size_enum_ord -addnBAC// leq_addl.
Qed.

Fact SAfun_SAselect n m s :
  (SAselect_graph n m s \in @SAfunc _ n m)
  && (SAselect_graph n m s \in @SAtot _ n m).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAselect_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row_i (ngraph u)`_(s`_i))%R.
by rewrite SAselect_graphP eqxx.
Qed.

Definition SAselect n m s := MkSAfun (SAfun_SAselect n m s).

Lemma SAselectE n m s u :
  SAselect n m s u = \row_i (ngraph u)`_(s`_i).
Proof. by apply/eqP; rewrite inSAfun SAselect_graphP. Qed.

Lemma SAselect_iotal n m x :
  SAselect (n + m) n (iota 0 n) x = lsubmx x.
Proof.
apply/rowP => i; rewrite SAselectE !mxE nth_iota//.
have ->: (0 + i = lshift m i)%N by [].
by rewrite nth_ngraph.
Qed.

Lemma SAselect_iotar n m (x : 'rV[F]_(n + m)) :
  SAselect _ _ (iota n m) x = rsubmx x.
Proof.
apply/rowP => i; rewrite SAselectE !mxE/= nth_iota//.
by rewrite -[X in _`_X]/(nat_of_ord (rshift n i)) nth_map_ord.
Qed.

Lemma SAset_castE_select n m s :
  SAset_cast m s = SAimset (SAselect n m (iota 0 m)) s.
Proof.
apply/eqP/SAsetP => x.
case: (ltnP n m) => nm.
  move: x; rewrite -(subnKC (ltnW nm)) => x.
  rewrite inSAset_castnD; apply/andP/SAimsetP => -[]; last first.
    move=> y ys ->; rewrite SAselectE; split.
      move: ys; congr (_ \in s); apply/rowP => i.
        by rewrite !mxE nth_iota// nth_ngraph.
    apply/eqP/rowP => i; rewrite !mxE nth_iota// nth_default// size_ngraph.
    exact/leq_addr.
  move=> xs /eqP x0; exists (lsubmx x) => //.
  apply/rowP => i; rewrite SAselectE mxE nth_iota// add0n.
  case: (ltnP i n) => ni.
    have ->: i = Ordinal ni :> nat by [].
    by rewrite nth_ngraph mxE; congr (x _ _); apply/val_inj.
  rewrite nth_default ?size_ngraph// -[x]hsubmxK mxE. 
  have ilt: (i - n < m - n)%N by rewrite leq_ltn_subLR.
  have ->: i = rshift n (Ordinal ilt).
    by apply/val_inj => /=; rewrite [(n + (i - n))%N]subnKC.
  by rewrite (unsplitK (inr _)) x0 mxE.
move: s; rewrite -(subnKC nm) => s.
apply/inSAset_castDn/SAimsetP => -[] y.
  move=> [] ys ->; exists y => //.
  apply/rowP => i; rewrite SAselectE !mxE nth_iota//.
  have iE: i = lshift (n - m) i :> nat by [].
  by rewrite [X in _`_X]iE nth_ngraph.
move=> ys ->; exists y; split=> //.
apply/rowP => i; rewrite SAselectE !mxE nth_iota//.
have iE: i = lshift (n - m) i :> nat by [].
by rewrite [X in _`_X]iE nth_ngraph.
Qed.

Fixpoint SAsum n : {SAfun F^n -> F^1}.
Proof.
case: n => [|n]; first exact: (SAfun_const 0 0).
apply/(SAcomp (SAadd 1) (SAjoin _ (SAselect _ 1 [:: n]))).
apply/(SAcomp (SAsum n) _).
exact/(SAselect _ _ (iota 0 n)).
Defined.
  
Lemma SAsumE n u : SAsum n u = \row__ \sum_i (u ord0 i)%R.
Proof.
apply/eqP; rewrite rowPE forall_ord1 mxE; apply/eqP.
elim: n u => [|n IHn] u; first by rewrite /SAsum SAfun_constE big_ord0 mxE.
rewrite /= SAcompE/= SAjoinE SAaddE SAcompE/= !SAselectE !mxE IHn/=.
rewrite (nth_map ord0) ?size_enum_ord//.
rewrite -[X in nth _ _ X]/(nat_of_ord (@ord_max n)) nth_ord_enum big_ord_recr/=.
congr (_ + _)%R; apply/eq_bigr => i _.
rewrite mxE nth_iota// (nth_map ord0); last first.
  by rewrite size_enum_ord ltnS ltnW//= add0n.
congr (u _ _).
have ->: i = lift ord_max i :> nat by rewrite /= /bump leqNgt (ltn_ord i).
rewrite nth_ord_enum; apply/val_inj => /=.
by rewrite /bump leqNgt (ltn_ord i).
Qed.

(* Evaluates a polynomial represented in big-endian in F^n at a point in F. *)
Definition SAhorner_graph n : {SAset F^(n + 1 + 1)} :=
  [set| nquantify n.+2 n Exists (
  subst_formula (rcons (iota n.+2 n) n.+1) (SAsum n) /\
  \big[And/True]_(i < n) ('X_(n.+2 + i) == ('X_i * 'X_n ^+ i)))].

Lemma SAhorner_graphP n (u : 'rV[F]_(n + 1)) (v : 'rV[F]_1) :
  (row_mx u v \in SAhorner_graph n)
  = (v == \row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
Proof.
rewrite /SAhorner_graph -2![X in nquantify X]addn1.
rewrite -[X in nquantify X](size_ngraph (row_mx u v)).
apply/SAin_setP/eqP => [/nexistsP[x]/= []|vE].
  move=> /holds_subst + /holdsAnd/= xE.
  rewrite -cats1 subst_env_cat/= subst_env_iota_catr; first last.
  - exact/size_tuple.
  - by rewrite size_map size_enum_ord !addn1.
  rewrite nth_cat size_map size_enum_ord 2!{1}addn1 leqnn.
  have nsE: n.+1 = rshift (n + 1)%N (@ord0 0) by rewrite /= addn0 addn1.
  rewrite [X in _`_X]nsE nth_map_ord mxE (unsplitK (inr _)) => xv.
  have {xv} <-: SAsum _ (\row_(i < n) tnth x i) = v.
    apply/eqP; rewrite inSAfun.
    apply/rcf_satP; rewrite ngraph_cat ngraph_tnth.
    suff ->: ngraph v = [:: v ord0 ord0] :> seq _ by [].
    apply/(@eq_from_nth _ 0); first exact/size_ngraph.
    rewrite size_ngraph; case=> // ltn01.
    by rewrite -[X in _`_X]/(nat_of_ord (@ord0 0)) nth_mktuple.
  rewrite SAsumE; apply/eqP; rewrite rowPE forall_ord1 !mxE horner_poly. 
  apply/eqP/eq_bigr => /= i _.
  have {1}->: i = lshift 1 (lshift 1 i) :> nat by [].
  rewrite mxE nth_map_ord.
  move: xE => /(_ i (mem_index_enum _) isT).
  rewrite nth_cat size_map size_enum_ord 2!{1}addn1 ltnNge (leq_addr _)/=.
  rewrite 2!{1}addn1 subDnCA// subnn addn0.
  rewrite nth_cat size_map size_enum_ord 2!{1}addn1.
  rewrite (ltn_trans (ltn_ord i) (leqnSn n.+1)).
  rewrite nth_cat size_map size_enum_ord [X in (_ < X + 1)%N]addn1 leq_addr.
  have nE: n = lshift 1 (rshift n (@ord0 0)) by rewrite /= addn0.
  have {2}->: i = lshift 1 (lshift 1 i) :> nat by [].
  by rewrite [X in _`_X ^+ _]nE !nth_map_ord !mxE !(unsplitK (inl _)) -tnth_nth.
apply/nexistsP.
exists ([tuple ((ngraph u)`_i * u ord0 (rshift n ord0) ^+ i)%R | i < n]) => /=.
split.
  apply/holds_subst.
  rewrite -cats1 subst_env_cat/= subst_env_iota_catr; first last.
  - by rewrite size_map size_enum_ord.
  - by rewrite size_map size_enum_ord !addn1.
  rewrite nth_cat size_map size_enum_ord 2![in X in (_ < X)%N]addn1 leqnn.
  have nsE: n.+1 = rshift (n + 1) (@ord0 0) by rewrite /= addn0 addn1.
  rewrite [X in _`_X]nsE nth_map_ord mxE (unsplitK (inr _)).
  suff: SAsum _ (\row_(i < n) ((ngraph u)`_i * u ord0 (rshift n ord0) ^+ i)%R)
        = v.
    move=> /eqP; rewrite inSAfun => /rcf_satP.
    rewrite ngraph_cat; congr holds; congr cat; last first.
      by rewrite /= enum_ordSl enum_ord0/=.
    apply/(@eq_from_nth _ 0).
      by rewrite size_ngraph size_map size_enum_ord.
    rewrite size_ngraph => i ilt.
    by rewrite -/(nat_of_ord (Ordinal ilt)) nth_mktuple nth_map_ord mxE.
  rewrite SAsumE; apply/eqP; rewrite rowPE forall_ord1 vE horner_poly !mxE. 
  apply/eqP/eq_bigr => /= i _; rewrite mxE.
  have {1 3}->: i = lshift 1 (lshift 1 i) :> nat by [].
  by rewrite nth_map_ord.
apply/holdsAnd => i _ _ /=.
rewrite nth_cat size_map size_enum_ord 2!{1}addn1 ltnNge (leq_addr _)/=.
rewrite 2![in X in (_ - X)%N]addn1 subDnCA// subnn addn0.
rewrite nth_cat size_map size_enum_ord 2![in X in (_ - X)%N]addn1.
rewrite -[X in (_ < X)%N]addnA (leq_trans (ltn_ord i) (leq_addr _ _)).
rewrite nth_cat size_map size_enum_ord [X in (_ < X + 1)%N]addn1 leq_addr.
rewrite nth_map_ord.
have nE: n = lshift 1 (rshift n (@ord0 0)) by rewrite /= addn0.
have {1 3}->: i = lshift 1 (lshift 1 i) :> nat by [].
by rewrite [X in _`_X ^+ _]nE !nth_map_ord !mxE !(unsplitK (inl _)).
Qed.

Fact SAfun_SAhorner n :
  (SAhorner_graph n \in @SAfunc _ (n + 1) 1)
  && (SAhorner_graph n \in @SAtot _ (n + 1) 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAhorner_graphP => /eqP -> /eqP.
apply/inSAtot => u.
exists (\row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
by rewrite SAhorner_graphP eqxx.
Qed.

Definition SAhorner n := MkSAfun (SAfun_SAhorner n).

Lemma SAhornerE n u :
  SAhorner n u
  = (\row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
Proof. by apply/eqP; rewrite inSAfun SAhorner_graphP. Qed.

Definition rootsR_formula n i :=
  (((\big[And/True]_(j < n) ('X_j == 0)) /\ (if i == 0%N then True else False))
  \/ \big[And/True]_(j < i) subst_formula
                            (iota 0 n ++ [:: (n + j)%N; (n + i)%N])
                            (SAhorner_graph n)
    /\ \big[And/True]_(j < i.-1) ('X_(n + j) <% 'X_(n + j.+1))%oT /\
     ('forall 'X_(n + i),
        subst_formula (iota 0 n ++ [:: (n + i)%N; (n + i).+1])
          (SAhorner_graph n) ==>
        \big[Or/False]_(j < i) ('X_(n + i) == 'X_(n + j))))%oT.

Lemma rootsR_formulaE n (u : 'rV[F]_n) d (r : d.-tuple F) :
  rcf_sat (ngraph u ++ r) (rootsR_formula n d)
  = (tval r == rootsR (\poly_(i0 < n) (ngraph u)`_i0)).
Proof.
have subst_envE (v : 'rV[F]_n) (x : F) (m : nat) (s : m.-tuple F) :
  (subst_env (iota 0 n ++ [:: (n + m)%N; (n + m).+1])
     (set_nth 0 (ngraph v ++ s) 
        (n + m) x))
        = ngraph v ++ [:: x; 0].
  rewrite set_nth_cat size_map size_enum_ord ltnNge leq_addr/=.
  rewrite subst_env_cat subst_env_iota_catl/=; last first.
    by rewrite size_map size_enum_ord.
  rewrite !subDnCA// subnn !addn0 !nth_cat size_map size_enum_ord.
  rewrite ltnNge leq_addr -addnS ltnNge leq_addr/= !subDnCA// subnn !addn0.
  rewrite !nth_set_nth/= eqxx -[X in X == _]addn1 -[X in _ == X]addn0.
  by rewrite eqn_add2l/= [_`_m.+1]nth_default// size_tuple.
rewrite /rootsR_formula !simp_rcf_sat !rcf_sat_forall.
under eq_forallb => /= i.
  rewrite simp_rcf_sat/= nth_cat size_map size_enum_ord (ltn_ord i) nth_map_ord.
  over.
have ->: [forall i, u ord0 i == 0] = (u == 0).
  by rewrite rowPE; apply/eq_forallb => /= i; rewrite mxE.
under [X in [&& X, _ & _]]eq_forallb => /= i.
  rewrite rcf_sat_subst subst_env_cat subst_env_iota_catl/=; last first.
    by rewrite size_map size_enum_ord.
  rewrite !nth_cat size_map size_enum_ord ltnNge leq_addr ltnNge leq_addr/=.
  rewrite !subDnCA// subnn !addn0 [_`_d]nth_default ?size_tuple//.
  over.
under [X in [&& _, X & _]]eq_forallb => /= i.
  rewrite simp_rcf_sat/=.
  rewrite !nth_cat size_map size_enum_ord ltnNge leq_addr ltnNge leq_addr/=.
  rewrite !subDnCA// subnn !addn0.
  over.
have [->|u0] /= := eqVneq u 0.
  have p0: \poly_(i0 < n) [seq (0 : 'rV[F]_n) ord0 i | i <- enum 'I_n]`_i0 = 0.
    apply/polyP => i; rewrite coef_poly coef0.
    case: (ltnP i n) => [ilt|//].
    by rewrite -/(nat_of_ord (Ordinal ilt)) nth_map_ord mxE.
  rewrite p0 rootsR0 -size_eq0 size_tuple; case: d r => [//|d] r /=.
  apply/negP => /= /andP[_] /andP[] /forallP/= rsort /rcf_satP/=.
  move=> /(_ (r`_(@ord0 d) - 1))/(_ _)/wrap[].
    apply/holds_subst; rewrite subst_envE.
    suff: SAhorner n (row_mx 0 (\row__ (r`_0 - 1))) = 0.
      move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      by congr (holds (_ ++ _) _); rewrite /= enum_ordSl enum_ord0/= !mxE.
    rewrite SAhornerE !mxE (unsplitK (inr _)) !mxE.
    apply/rowP => j; rewrite ord1 !mxE.
    under eq_poly => i ilt.
      rewrite ngraph_cat nth_cat size_ngraph ilt.
      over.
    by rewrite p0 horner0.
  move=> /holdsOr[/=] i [_][_].
  rewrite !nth_set_nth/= eqxx eqn_add2l.
  move: (ltn_ord i); have [->|_ _] := eqVneq (i : nat) d.+1.
    by rewrite ltnn.
  rewrite nth_cat size_map size_enum_ord ltnNge leq_addr/=.
  rewrite subDnCA// subnn addn0 => /eqP iE.
  case: (posnP i) => i0.
    by move: iE; rewrite i0 -subr_eq0 addrAC subrr add0r oppr_eq0 oner_eq0.
  have: sorted <%O r.
    apply/(sortedP 0) => j; rewrite size_tuple ltnS => jd.
    exact/(rsort (Ordinal jd)).
  rewrite lt_sorted_pairwise => /(pairwiseP 0)/(_ 0 i).
  rewrite !inE size_tuple ltnS => /(_ (leq0n _) (ltn_ord i) i0).
  by rewrite -(eqP iE) -subr_gt0 addrAC subrr add0r oppr_gt0 ltr10.
case: d r => [|d]r.
  rewrite !forall_ord0/= tuple0/= => {r}.
  move rE: (rootsR _) => r; case: r rE => [|x r] rE.
    apply/rcf_satP => /= x /holds_subst; rewrite big_ord0/= subst_envE => x0.
    suff: x \in [::] by [].
    rewrite -rE in_rootsR; apply/andP; split.
      move: u0; apply/contraNN => /eqP/polyP u0.
      apply/eqP/rowP => i; rewrite mxE.
      by move: (u0 i); rewrite coef0 coef_poly (ltn_ord i) nth_map_ord.
    have: SAhorner n (row_mx u (\row__ x)) = 0.
      apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
      move: x0; congr (holds (_ ++ _) _).
      by rewrite /= enum_ordSl enum_ord0/= !mxE.
    rewrite SAhornerE !mxE (unsplitK (inr _)) !mxE => /eqP.
    rewrite rowPE forall_ord1 !mxE /root.
    congr (_.[_] == 0); apply/polyP => i.
    rewrite !coefE; case: (ltnP i n) => [ilt|//].
    by rewrite ngraph_cat nth_cat size_ngraph ilt.
  apply/rcf_satP => /= /(_ x); rewrite big_ord0/= => /(_ _)/wrap[]//.
  apply/holds_subst; rewrite subst_envE.
  move: (mem_head x r); rewrite -rE in_rootsR => /andP[_] x0.
  suff: SAhorner n (row_mx u (\row__ x)) = 0.
      move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      by congr (holds (_ ++ _) _); rewrite /= enum_ordSl enum_ord0/= !mxE.
    rewrite SAhornerE !mxE (unsplitK (inr _)) !mxE.
    apply/rowP => j; rewrite ord1 !mxE.
    under eq_poly => i ilt.
      rewrite ngraph_cat nth_cat size_ngraph ilt.
      over.
    exact/eqP.
apply/andP/eqP => /=.
  move=> [] /forallP/= r0 /andP[] /forallP/= rsort /rcf_satP/= rall.
  apply/rootsRPE.
  - move=> i.
    move: r0 {rsort rall} => /(_ i) /rcf_satP ri0.
    suff: SAhorner n (row_mx u (\row__ r`_i)) = 0.
      move=> /eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
      rewrite !mxE -tnth_nth /root; congr (_.[_]%R == 0).
      by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
    apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
    move: ri0; congr (holds (_ ++ _) _).
    by rewrite /= enum_ordSl enum_ord0/= !mxE.
  - move=> x x0; move: rall {r0 rsort} => /(_ x)/(_ _)/wrap[].
      apply/holds_subst; rewrite subst_envE.
      have: SAhorner n (row_mx u (\row__ x)) = 0.
        apply/eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
        rewrite mxE; move: x0; rewrite /root; congr (_.[_]%R == 0).
        by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
      move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      congr (holds (_ ++ _) _).
      by rewrite /= enum_ordSl enum_ord0/= !mxE.
    move=> /holdsOr[/=] i [_][_].
    rewrite !nth_set_nth/= eqxx eqn_add2l.
    move: (ltn_ord i); have [->|_ _ ->] := eqVneq (i : nat) d.+1.
      by rewrite ltnn.
    rewrite nth_cat size_map size_enum_ord ltnNge leq_addr/=.
    rewrite subDnCA// subnn addn0.
    by apply/mem_nth; rewrite size_tuple.
  - apply/(sortedP 0) => i; rewrite size_tuple.
    rewrite -ltn_predRL => id.
    exact/(rsort (Ordinal id)).
move=> rE; split.
  apply/forallP => /= i.
  have: r`_i \in r by apply/mem_nth; rewrite size_tuple.
  rewrite memtE {2}rE in_rootsR => /andP[_] r0; apply/rcf_satP.
  have {}r0: SAhorner n (row_mx u (\row__ r`_i)) = 0.
    apply/eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
    move: r0; rewrite !mxE /root; congr (_.[_]%R == 0).
    by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
  move/eqP : r0; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
  congr (holds (_ ++ _) _); last first.
  by rewrite /= enum_ordSl enum_ord0/= !mxE.
apply/andP; split.
  apply/forallP => /= i.
  have /sortedP: sorted <%R r by rewrite rE; apply/sorted_roots.
  by move=> /(_ 0 i); rewrite size_tuple ltnS; apply.
apply/rcf_satP => /= x /holds_subst; rewrite subst_envE => x0.
suff: x \in tval r.
  move=> /(nthP 0)[] i; rewrite size_tuple => ir <-.
  apply/holdsOr; exists (Ordinal ir).
  split; first exact/mem_index_enum.
  split=> //=; rewrite !nth_set_nth/= eqxx eqn_add2l.
  move: ir; have [->|_ ir] := eqVneq (i : nat) d.+1.
    by rewrite ltnn.
  rewrite nth_cat size_map size_enum_ord ltnNge leq_addr/=.
  by rewrite subDnCA// subnn addn0.
rewrite rE in_rootsR; apply/andP; split.
move: u0; apply/contraNN => /eqP/polyP u0.
  apply/eqP/rowP => i; rewrite mxE.
  by move: (u0 i); rewrite coef0 coef_poly (ltn_ord i) nth_map_ord.
have: SAhorner n (row_mx u (\row__ x)) = 0.
  apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
  move: x0; congr (holds (_ ++ _) _).
  by rewrite /= enum_ordSl enum_ord0/= !mxE.
rewrite SAhornerE !mxE (unsplitK (inr _)) !mxE => /eqP.
rewrite rowPE forall_ord1 !mxE /root.
congr (_.[_] == 0); apply/polyP => i.
rewrite !coefE; case: (ltnP i n) => [ilt|//].
by rewrite ngraph_cat nth_cat size_ngraph ilt.
Qed.

(* Function giving the number of roots of a polynomial of degree at most n.-1
   encoded in big endian in F^n *)
Definition SAnbroots_graph n : {SAset F^(n + 1)} :=
  [set| (\big[And/True]_(i < n.+1) ('X_i == 0))
    \/ \big[Or/False]_(i < n) (('X_n == Const i%:R%R)
      /\ nquantify n.+1 i Exists (
        subst_formula (iota 0 n ++ iota n.+1 i) (rootsR_formula n i)))].

Lemma SAnbroots_graphP n u v :
  (row_mx u v \in SAnbroots_graph n) = (v == \row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R).
Proof.
rewrite inE rcf_sat_repr_pi rcf_sat_subst -[_ (ngraph _)]cats0.
rewrite subst_env_iota_catl ?size_ngraph// rcf_sat_Or rcf_sat_forall rcf_sat_exists.
set p := \poly_(i < n) (ngraph u)`_i.
set P := [forall _, _].
have ->: P = ((u == 0) && (v == 0)).
  rewrite /P; apply/forallP/andP => /= [uv0|[] /eqP -> /eqP -> i]; last first.
    rewrite simp_rcf_sat/=.
    have ilt: (val i < n + 1)%N by rewrite addn1 ltn_ord.
    rewrite (nth_map_ord _ _ (Ordinal ilt)) mxE.
    by case: (split _) => j; rewrite mxE.
  split.
    apply/eqP/rowP => i; move: (uv0 (lift ord_max i)).
    rewrite simp_rcf_sat/= /bump leqNgt (ltn_ord i)/=.
    by rewrite (nth_map_ord _ _ (lshift 1 i)) !mxE (unsplitK (inl _)) => /eqP.
  rewrite rowPE forall_ord1; move: (uv0 ord_max).
  rewrite simp_rcf_sat/=.
  have nE: n = rshift n (@ord0 0) by rewrite /= addn0.
  by rewrite [X in _`_X] nE nth_map_ord !mxE (unsplitK (inr _)).
under eq_existsb => /= i.
  rewrite simp_rcf_sat.
  have nE: size (ngraph (row_mx u v)) = n.+1 by rewrite size_ngraph addn1.
  rewrite -[X in nquantify X]nE.
  rewrite -[X in nquantify _ X](size_resize 0 (rootsR p) i).
  rewrite rcf_sat_nexists; last first.
    move=> r; rewrite size_resize => ri.
    rewrite rcf_sat_subst subst_env_cat ngraph_cat -{1}catA.
    rewrite subst_env_iota_catl ?size_ngraph//.
    rewrite subst_env_iota_catr//; last first.
      by rewrite size_cat !size_ngraph addn1.
    move/eqP: ri => ri.
    rewrite -[r]/(val (Tuple ri)) rootsR_formulaE => /= /eqP rE.
    move: ri; rewrite rE => /eqP ri.
    by rewrite -ri resize_id.
  rewrite simp_rcf_sat/=.
  have nE': n = rshift n (@ord0 0) by rewrite /= addn0.
  rewrite [X in _`_X]nE' nth_map_ord mxE (unsplitK (inr _)).
  rewrite rcf_sat_subst subst_env_cat ngraph_cat -{1}catA.
  rewrite subst_env_iota_catl ?size_ngraph//.
  rewrite subst_env_iota_catr//; first last.
  - exact/size_resize.
  - by rewrite -ngraph_cat.
  move/eqP: (size_resize 0 (rootsR p) i) => ri.
  rewrite -[resize _ _ _]/(val (Tuple ri)) rootsR_formulaE/= resize_idE.
  over.
apply/orP/eqP.
  case=> [/andP[] /eqP uE /eqP ->|/existsP[] /=]; last first.
    move=> i /andP[] /eqP vi /eqP ri.
    by apply/rowP => j; rewrite ord1 vi mxE -ri.
  apply/rowP => i; rewrite ord1 !mxE.
  suff ->: p = 0 by rewrite rootsR0.
  apply/polyP => {}i; rewrite coef_poly coef0.
  case: (ltnP i n) => [ni|//] /=.
  by rewrite (nth_map_ord _ _ (Ordinal ni)) uE mxE.
have [uE vE|u0 vE] /= := eqVneq u 0; [left|right].
  rewrite rowPE forall_ord1 vE !mxE.
  suff ->: p = 0 by rewrite rootsR0.
  apply/polyP => i; rewrite coef_poly coef0.
  case: (ltnP i n) => [ni|//] /=.
  by rewrite (nth_map_ord _ _ (Ordinal ni)) uE mxE.
apply/existsP => /=.
suff pn: (size (rootsR p) < n)%N.
  by exists (Ordinal pn); rewrite /= vE mxE !eqxx.
rewrite ltnNge; apply/negP.
have pn: (size p <= n)%N by apply/size_poly.
move=> /(leq_trans pn)/poly_ltsp_roots/(_ (uniq_roots _ _ _))/(_ _)/wrap[].
  by apply/allP => x; rewrite in_rootsR => /andP[_].
suff/eqP: p != 0 by [].
move: u0; apply/contraNN => /eqP/polyP/= p0.
apply/eqP/rowP => i; move: (p0 i).
by rewrite coef_poly coef0 (ltn_ord i) nth_map_ord mxE.
Qed.

Fact SAfun_SAnbroots n :
  (SAnbroots_graph n \in @SAfunc _ n 1) && (SAnbroots_graph n \in @SAtot _ n 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAnbroots_graphP => /eqP -> /eqP.
apply/inSAtot => u.
exists (\row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R)%R.
by rewrite SAnbroots_graphP eqxx.
Qed.

Definition SAnbroots n := MkSAfun (SAfun_SAnbroots n).

Lemma SAnbrootsE n u :
  SAnbroots n u = (\row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R)%R.
Proof. by apply/eqP; rewrite inSAfun SAnbroots_graphP. Qed.

Definition SAnthroot_graph n i : {SAset F^(n + 1)} :=
  [set| (\big[And/True]_(d < n.+1) ('X_d == 0)) \/ \big[Or/False]_(d < n) (
    nquantify n.+1 d Exists ('X_n == 'X_(n.+1 + i) /\
      subst_formula ((iota 0 n) ++ (iota n.+1 d)) (rootsR_formula n d)))].

Lemma SAnthroot_graphP n m (u : 'rV[F]_n) (v : 'rV[F]_1) :
  (row_mx u v \in SAnthroot_graph n m) = (v
  == \row__ ((rootsR (\poly_(i < n) (ngraph u)`_i))`_m)).
Proof.
rewrite inE rcf_sat_repr_pi rcf_sat_subst -[_ (ngraph _)]cats0.
rewrite subst_env_iota_catl ?size_ngraph// rcf_sat_Or rcf_sat_forall.
rewrite rcf_sat_exists.
set p := \poly_(i < n) (ngraph u)`_i.
set P := [forall _, _].
have ->: P = ((u == 0) && (v == 0)).
  rewrite /P; apply/forallP/andP => /= [uv0|[] /eqP -> /eqP -> i]; last first.
    rewrite simp_rcf_sat/=.
    have ilt: (val i < n + 1)%N by rewrite addn1 ltn_ord.
    rewrite (nth_map_ord _ _ (Ordinal ilt)) mxE.
    by case: (split _) => j; rewrite mxE.
  split.
    apply/eqP/rowP => i; move: (uv0 (lift ord_max i)).
    rewrite simp_rcf_sat/= /bump leqNgt (ltn_ord i)/=.
    by rewrite (nth_map_ord _ _ (lshift 1 i)) !mxE (unsplitK (inl _)) => /eqP.
  rewrite rowPE forall_ord1; move: (uv0 ord_max).
  rewrite simp_rcf_sat/=.
  have nE: n = rshift n (@ord0 0) by rewrite /= addn0.
  by rewrite [X in _`_X] nE nth_map_ord !mxE (unsplitK (inr _)).
under eq_existsb => /= i.
  have nE: size (ngraph (row_mx u v)) = n.+1 by rewrite size_ngraph addn1.
  rewrite -[X in nquantify X]nE.
  rewrite -[X in nquantify _ X](size_resize 0 (rootsR p) i).
  rewrite rcf_sat_nexists; last first.
    move=> r; rewrite size_resize => ri.
    rewrite simp_rcf_sat rcf_sat_subst subst_env_cat ngraph_cat -{2}catA.
    move=> /andP[_].
    rewrite subst_env_iota_catl ?size_ngraph// subst_env_iota_catr//; last first.
      by rewrite size_cat !size_ngraph addn1.
    move/eqP: ri => ri.
    rewrite -[r]/(val (Tuple ri)) rootsR_formulaE => /= /eqP rE.
    move: ri; rewrite rE => /eqP ri.
    by rewrite -ri resize_id.
  rewrite !simp_rcf_sat/= !nth_cat size_map size_enum_ord.
  rewrite -{1}[n]addn0 ltn_add2l/= [X in (_ < X)%N]addn1 ltnNge leq_addr/=.
  rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
  have nE': n = rshift n (@ord0 0) by rewrite /= addn0.
  rewrite [X in _`_X]nE' nth_map_ord mxE (unsplitK (inr _)).
  rewrite rcf_sat_subst subst_env_cat ngraph_cat -{1}catA.
  rewrite subst_env_iota_catl ?size_ngraph//.
  rewrite subst_env_iota_catr//; first last.
  - exact/size_resize.
  - by rewrite -ngraph_cat.
  move/eqP: (size_resize 0 (rootsR p) i) => ri.
  rewrite -[resize _ _ _]/(val (Tuple ri)) rootsR_formulaE/= resize_idE.
  over.
apply/orP/eqP.
  case=> [/andP[] /eqP uE /eqP ->|/existsP[] /=]; last first.
    move=> i /andP[] /eqP vi /eqP ri.
    by apply/rowP => j; rewrite ord1 vi mxE ri resize_id.
  apply/rowP => i; rewrite ord1 !mxE.
  suff ->: p = 0 by rewrite rootsR0 nth_nil.
  apply/polyP => {}i; rewrite coef_poly coef0.
  case: (ltnP i n) => [ni|//] /=.
  by rewrite (nth_map_ord _ _ (Ordinal ni)) uE mxE.
have [uE vE|u0 vE] /= := eqVneq u 0; [left|right].
  rewrite rowPE forall_ord1 vE !mxE.
  suff ->: p = 0 by rewrite rootsR0 nth_nil.
  apply/polyP => i; rewrite coef_poly coef0.
  case: (ltnP i n) => [ni|//] /=.
  by rewrite (nth_map_ord _ _ (Ordinal ni)) uE mxE.
apply/existsP => /=.
suff pn: (size (rootsR p) < n)%N.
  by exists (Ordinal pn); rewrite /= vE mxE resize_id !eqxx.
rewrite ltnNge; apply/negP.
have pn: (size p <= n)%N by apply/size_poly.
move=> /(leq_trans pn)/poly_ltsp_roots/(_ (uniq_roots _ _ _))/(_ _)/wrap[].
  by apply/allP => x; rewrite in_rootsR => /andP[_].
suff/eqP: p != 0 by [].
move: u0; apply/contraNN => /eqP/polyP/= p0.
apply/eqP/rowP => i; move: (p0 i).
by rewrite coef_poly coef0 (ltn_ord i) nth_map_ord mxE.
Qed.

Fact SAfun_SAnthroot n i :
  (SAnthroot_graph n i \in @SAfunc _ n 1)
  && (SAnthroot_graph n i \in @SAtot _ n 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAnthroot_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row__ (rootsR (\poly_(i < n) (ngraph u)`_i))`_i)%R.
by rewrite SAnthroot_graphP eqxx.
Qed.

Definition SAnthroot n i := MkSAfun (SAfun_SAnthroot n i).

Lemma SAnthrootE n i (u : 'rV[F]_n) :
  SAnthroot n i u = (\row__ (rootsR (\poly_(i < n) (ngraph u)`_i))`_i)%R.
Proof. by apply/eqP; rewrite inSAfun SAnthroot_graphP. Qed.

(* TODO: See if rcf_sat_nexists shortens the previous proofs. *)

Definition SAmulc_graph : {SAset F^((2 + 2) + 2)} :=
  [set| 'X_4 == ('X_0 * 'X_2 - 'X_1 * 'X_3)
     /\ 'X_5 == ('X_0 * 'X_3 + 'X_1 * 'X_2)].

Lemma SAmulc_graphP (u v w : 'rV[F]_2) :
  row_mx (row_mx u v) w \in SAmulc_graph =
  (let x :=
    ((u ord0 ord0 +i* u ord0 ord_max) * (v ord0 ord0 +i* v ord0 ord_max))%C in
  (w == \row_i if i == 0 then complex.Re x else complex.Im x)).
Proof.
rewrite inE rcf_sat_repr_pi rcf_sat_subst -[_ (ngraph _)]cats0.
rewrite subst_env_iota_catl ?size_ngraph// rcf_sat_And !rcf_sat_Equal/=.
have nE: 4 = rshift 4 (@ord0 1) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inr _)).
have {}nE: 0 = lshift 2 (lshift 2 (@ord0 1)) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inl _)).
have {}nE: 2 = lshift 2 (rshift 2 (@ord0 1)) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord !mxE !(unsplitK (inl _)).
have {}nE: 1 = lshift 2 (lshift 2 (@ord_max 1)) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord !mxE (unsplitK (inl _)) (unsplitK (inr _)).
have {}nE: 3 = lshift 2 (rshift 2 (@ord_max 1)) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord !mxE !(unsplitK (inl _)).
have {}nE: 5 = rshift 4 (@ord_max 1) :> nat by [].
rewrite [X in _`_X]nE nth_map_ord !mxE !(unsplitK (inr _)).
by rewrite rowPE forall_ord2 !mxE/=.
Qed.

Fact SAfun_SAmulc :
  (SAmulc_graph \in @SAfunc _ (2 + 2) 2)
  && (SAmulc_graph \in @SAtot _ (2 + 2) 2).
Proof.
apply/andP; split.
  apply/inSAfunc => u y1 y2; rewrite -[u]hsubmxK !SAmulc_graphP.
  by move=> /eqP -> /eqP.
apply/inSAtot => u.
pose x := ((lsubmx u ord0 ord0 +i* lsubmx u ord0 ord_max)
  * (rsubmx u ord0 ord0 +i* rsubmx u ord0 ord_max))%C.
exists (\row_i if i == 0 then complex.Re x else complex.Im x).
by rewrite -[u]hsubmxK SAmulc_graphP.
Qed.

Definition SAmulc := MkSAfun SAfun_SAmulc.

Lemma SAmulcE u v :
  SAmulc (row_mx u v) = 
    (let x := ((u ord0 ord0 +i* u ord0 ord_max)
      * (v ord0 ord0 +i* v ord0 ord_max))%C in
    \row_i if i == 0 then complex.Re x else complex.Im x).
Proof. by apply/eqP; rewrite inSAfun SAmulc_graphP. Qed.

Fixpoint SAexpc_subdef n :
  {f : {SAfun F^2 -> F^2} |
    forall u : 'rV[F]_2,
      let x := (u ord0 ord0 +i* u ord0 ord_max)%C ^+ n in
      (f u = \row_(i < 2) if i == 0 then complex.Re x else complex.Im x)}.
Proof.
case: n => [|n].
  exists (SAfun_const 2 (\row_(i < 2) (i == 0)%:R)) => u/=.
  by rewrite SAfun_constE; apply/rowP => i; rewrite !mxE mulrb.
case: (SAexpc_subdef n) => f fE.
exists (SAcomp SAmulc (SAjoin f (SAid 2))) => u/=.
rewrite SAcompE/= SAjoinE SAidE fE SAmulcE/=.
apply/rowP => i; rewrite !mxE/= exprSr.
apply/complexI; rewrite [RHS]fun_if complexRe complexIm ReM ImM.
rewrite -!complexRe/= -!complexIm/= -!rmorphM/= -rmorphB/= -rmorphD/=.
by rewrite -fun_if [u ord0 ord0 * _]mulrC.
Qed.

Definition SAexpc n := proj1_sig (SAexpc_subdef n).

Lemma SAexpcE n u :
  SAexpc n u = let x := (u ord0 ord0 +i* u ord0 ord_max)%C ^+ n in
    \row_(i < 2) if i == 0 then complex.Re x else complex.Im x.
Proof. exact: (proj2_sig (SAexpc_subdef n) u). Qed.

Lemma SAhornerRC_subdef n :
  {f : {SAfun F^(n + 2) -> F^2} | forall (u : 'rV[F]_(n + 2)),
    let x := (u ord0 (rshift n ord0) +i* u ord0 (rshift n ord_max))%C in
    let r := (\poly_(i < n) ((ngraph u)`_i)%:C).[x]%C in
    f u = (\row_i (if i == 0 then complex.Re r else complex.Im r))%R}.
Proof.
elim: n => [|n [f] fP].
  exists (SAfun_const 2 0) => u x r.
  suff ->: r = 0.
    by apply/eqP; rewrite SAfun_constE rowPE forall_ord2 !mxE/= eqxx.
  rewrite -[RHS](horner0 x); congr horner.
  by apply/eqP; rewrite -size_poly_eq0 -leqn0; apply/size_poly.
exists (
  SAfun_add
    (SAcomp f (SAselect _ _ (iota 0 n ++ iota n.+1 2)))
    (SAcomp SAmulc
      (SAjoin
        (SAselect _ _ [:: n; n.+3])
        (SAcomp (SAexpc n) (SAselect _ _ (iota n.+1 2)))))).
move=> u x r.
rewrite SAfun_addE !SAcompE/= SAjoinE SAcompE/= 3!SAselectE SAmulcE SAexpcE.
apply/rowP => i; rewrite !mxE.
have reE (a b : F) : complex.Re (a +i* b)%C = a by [].
have imE (a b : F) : complex.Im (a +i* b)%C = b by [].
rewrite reE imE/=.
have nE: n = lshift 2 (@ord_max n) by [].
rewrite [X in (ngraph u)`_X]nE nth_map_ord.
have n1E: n.+1 = rshift n.+1 (@ord0 1) by apply/esym/addn0.
rewrite [X in (ngraph u)`_X]n1E nth_map_ord.
have n2E: n.+2 = rshift n.+1 (@ord_max 1) by apply/esym/addn1.
rewrite [X in (ngraph u)`_X]n2E nth_map_ord.
rewrite [(ngraph u)`__]nth_default; last by rewrite size_ngraph addn2.
rewrite !mul0r subr0 addr0 fP !mxE.
have ->: forall a (b c d e : F),
  ((if a then b else c) + (if a then d else e)) = if a then b + d else (c + e).
  by case.
have ->: forall (a : F) b, a * complex.Re b = complex.Re (a *: b).
  by move=> a; case=> /=.
have ->: forall (a : F) b, a * complex.Im b = complex.Im (a *: b).
  by move=> a; case=> /=.
rewrite -!raddfD/=.
set g := (fun x : F[i] => if i == 0 then complex.Re x else complex.Im x).
rewrite -[LHS]/(g _) -[RHS]/(g _); congr g.
rewrite /r !horner_poly big_ord_recr/=.
rewrite [X in _ = _ + (_`_X)%:C%C * _]nE nth_map_ord -/x.
have ->: forall (a : F) (b : F[i]), a%:C%C * b = a *: b.
  by move=> a; case=> b c; rewrite /GRing.mul/= !mul0r subr0 addr0.
apply/(subIr (u ord0 (lshift 2 ord_max) *: x ^+ n)).
rewrite -[LHS]addrA -[RHS]addrA subrr [LHS]addr0 [RHS]addr0.
apply/eq_bigr => j _.
have jE: j = lshift 2 j :> nat by [].
rewrite {1}jE nth_map_ord mxE/=.
rewrite !nth_cat size_iota (ltn_ord j) nth_iota; last by [].
rewrite addn0 ltnn subnn/= ltnNge leq_addr/=.
rewrite subDnCA; last by [].
rewrite subnn/=.
have {}jE: j = lshift 2 (lift ord_max j) :> nat.
  by rewrite /= /bump leqNgt (ltn_ord j).
rewrite [X in (ngraph u)`_X]jE nth_map_ord.
rewrite [X in (ngraph u)`_X]n1E nth_map_ord.
by rewrite [X in (ngraph u)`_X]n2E nth_map_ord.
Qed.

Definition SAhornerRC n := proj1_sig (SAhornerRC_subdef n).

Lemma SAhornerRCE n (u : 'rV[F]_(n + 2)) :
  let x := (u ord0 (rshift n ord0) +i* u ord0 (rshift n ord_max))%C in
  let r := (\poly_(i < n) ((ngraph u)`_i)%:C).[x]%C in
  SAhornerRC n u = (\row_i (if i == 0 then complex.Re r else complex.Im r))%R.
Proof. exact/(proj2_sig (SAhornerRC_subdef n)). Qed.

(* Function giving the number of complex roots of a polynomial of degree at most
   n.-1 encoded in big endian in F^n *)
Definition SAnbrootsC_graph n : {SAset F^(n + 1)} :=
  [set| (\big[And/True]_(i < n.+1) ('X_i == 0))
    \/ \big[Or/False]_(d < n) (('X_n == Const d%:R%R)
      /\ nquantify n.+1 d.*2 Exists (
        \big[And/True]_(j < d)
          subst_formula
            (iota 0 n ++
              [:: n.+1 + j.*2; n.+1 + j.*2.+1; n.+1 + d.*2; n.+1 + d.*2]%N)
            (SAhornerRC n)
        /\ \big[And/True]_(i < d) \big[And/True]_(j < d | j != i)
            ('X_(n.+1 + i.*2) != 'X_(n.+1 + j.*2)
            \/ 'X_(n.+1 + i.*2.+1) != 'X_(n.+1 + j.*2.+1))
        /\ nquantify (n.+1 + d.*2) 2 Forall
          (subst_formula
            (iota 0 n ++
              [:: n.+1 + d.*2; n.+1 + d.*2.+1; n.+1 + d.*2.+2;
                n.+1 + d.*2.+2]%N)
            (SAhornerRC n) ==> \big[Or/False]_(j < d)
              ('X_(n.+1 + d.*2) == 'X_(n.+1 + j.*2)
              /\ 'X_(n.+1 + d.*2.+1) == 'X_(n.+1 + j.*2.+1)))))].

Lemma SAnbrootsC_graphP n u v :
  (row_mx u v \in SAnbrootsC_graph n)
  = (v == \row__ (size (dec_roots (\poly_(i < n) ((ngraph u)`_i)%:C%C)))%:R).
Proof.
move uvE: (tval (ngraph (row_mx u v))) => uv.
move: uvE; have [->|u0] := eqVneq u 0 => uvE.
  have ->: \poly_(i < n) ((@ngraph F n 0)`_i)%:C%C = 0.
    apply/polyP => i; rewrite coef_poly coef0.
    case: (ltnP i n) => [ilt|//].
    by rewrite (nth_mktuple _ _ (Ordinal ilt)) mxE.
  rewrite dec_roots0/=.
  apply/SAin_setP/eqP => [/= [/holdsAnd|/holdsOr-[] i]| ->].
  - move=> /(_ ord_max (mem_index_enum _) isT) /=.
    have nE: n = rshift n (@ord0 0) by rewrite /= addn0.
    rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inr _)) => v0.
    by apply/eqP; rewrite rowPE forall_ord1 mxE; apply/eqP.
  - move=> [_][_]/= [_]; rewrite -[X in nquantify X]addn1.
    rewrite -[X in nquantify X](size_ngraph (row_mx 0 v)).
    move=> /nexistsP[r]/= [_][_]; rewrite uvE.
    have suvr: (n.+1 + i.*2)%N = size (uv ++ r).
      by rewrite -uvE size_cat size_ngraph size_tuple addn1.
    rewrite suvr => /nforallP.
    move=> /(_ (mktuple (fun=> 1 + \big[Order.max/0]_(x <- r) x)))%R /=.
    mp.
      apply/holds_subst; rewrite subst_env_cat.
      rewrite -{1}uvE/= {1}enum_ordD map_cat -!catA.
      rewrite subst_env_iota_catl; last by rewrite 2!size_map size_enum_ord.
      rewrite catA nth_cat ltnn subnn enum_ordSl/=.
      rewrite nth_cat [X in (X < _)%N]addnS suvr ltnNge leqnSn/=.
      rewrite -suvr subnDl subSn// subnn enum_ordSl/=.
      rewrite nth_default; last first.
        by rewrite !addnS suvr size_cat/= enum_ord0/= addn2.
      have: SAhornerRC n (row_mx 0 (\row__ (1 + \big[maxr/0]_(x <- r) x)%R))
            = \row__ 0.
        apply/eqP; rewrite SAhornerRCE rowPE forall_ord2 !mxE/=.
        rewrite !(unsplitK (inr _)).
        move pE : (poly _ _) => p.
        suff ->: p = 0 by rewrite horner0/= eqxx.
        apply/polyP => j; rewrite -pE coef0 coef_poly.
        case: (ltnP j n) => [jn|//].
        rewrite ngraph_cat nth_cat size_ngraph jn.
        by rewrite (nth_mktuple _ _ (Ordinal jn)) mxE.
      move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      congr (holds (_ ++ _) _); last by rewrite /= !enum_ordSl enum_ord0/= !mxE.
      apply/(@eq_from_nth _ 0) => [|k]; rewrite size_ngraph.
        by rewrite 2!size_map size_enum_ord.
      move=> kn; rewrite /= -map_comp !(nth_map_ord _ _ (Ordinal kn)).
      by rewrite [in RHS]mxE (unsplitK (inl _)).
    move=> /holdsOr[j] [_][_]/= [] + _.
    rewrite nth_cat ltnn subnn {1}enum_ordSl/=.
    rewrite nth_cat -suvr ltn_add2l ltn_double ltn_ord nth_cat.
    rewrite -{1 3}uvE size_ngraph addn1 ltnNge leq_addr/=.
    rewrite subDnCA// subnn addn0 => rE.
    suff: r`_j.*2 <= \big[maxr/0]_(x <- r) x.
      by rewrite -rE; rewrite -subr_ge0 opprD addrCA subrr addr0 oppr_ge0 ler10.
    rewrite le_bigmax; apply/orP; right; apply/hasP; exists r`_j.*2.
      by apply/mem_nth; rewrite size_tuple ltn_double.
    exact/lexx.
  left; apply/holdsAnd; case=> i /= ilt _ _ /=.
  rewrite enum_ordD map_cat -2!map_comp nth_cat size_map size_enum_ord.
  case: (ltnP i n) => iltn.
    rewrite -/(nat_of_ord (Ordinal iltn)) nth_map_ord mxE (unsplitK (inl _)).
    by rewrite mxE.
  have ->: i = n by apply/le_anti/andP.
  rewrite subnn -[X in _`_X]/(nat_of_ord (@ord0 0)) nth_map_ord mxE.
  by rewrite (unsplitK (inr _)) mxE.
have pu0: \poly_(i < n) (([seq u ord0 i0 | i0 <- enum 'I_n]`_i)%:C)%C != 0.
  apply/eqP => /polyP pu0.
  move/eqP: u0 => /rowP; apply => i.
  move: (pu0 i); rewrite coef_poly ltn_ord nth_map_ord mxE coef0.
  by move/complexI.
have ComplexK (x : F[i]): (complex.Re x +i* complex.Im x)%C = x.
  by apply/eqP; rewrite eq_complex !eqxx.
rewrite inE rcf_sat_repr_pi rcf_sat_subst uvE -[uv]cats0.
rewrite subst_env_iota_catl; last by rewrite -uvE size_ngraph.
rewrite rcf_sat_Or rcf_sat_forall.
have /negP/negPf -> /=: ~ [forall i : 'I_(n.+1), rcf_sat uv ('X_i == 0)].
  move=> /forallP /= uv0.
  move: u0; rewrite rowPE => /forallPn/= [] i.
  move: (uv0 (lift ord_max i)) => /rcf_satP/=.
  rewrite -uvE ngraph_cat nth_cat /bump [(n <= i)%N]leqNgt size_ngraph.
  by rewrite !(ltn_ord i)/= nth_map_ord mxE => -> /eqP.
apply/rcf_satP/eqP => [/holdsOr/=[] d [_][_]|vE].
  rewrite -{1}uvE ngraph_cat nth_cat size_ngraph ltnn.
  rewrite subnn (nth_map_ord _ _ ord0) => -[] vE.
  rewrite -[X in nquantify X]addn1.
  rewrite -[X in nquantify X](size_ngraph (row_mx u v)) uvE.
  move=> /nexistsP[r]/= [] /holdsAnd/= rroot [] runiq rall.
  set r' := (mktuple (fun i : 'I_d => (r`_(val i).*2 +i* r`_(val i).*2.+1)%C)).
  apply/eqP; rewrite rowPE forall_ord1 vE mxE eqr_nat -(size_tuple r').
  apply/eqP/perm_size/uniq_perm.
  - apply/negP => /negP/(uniqPn 0)/= [] i [] j [] ij.
    rewrite size_map size_enum_ord => jd.
    rewrite (nth_map_ord _ _ (Ordinal (ltn_trans ij jd))).
    rewrite (nth_map_ord _ _ (Ordinal jd)) => -[] rij rij1.
    move/holdsAnd: runiq => /=.
    move=> /(_ (Ordinal (ltn_trans ij jd)) (mem_index_enum _) isT).
    move=> /holdsAnd /= /(_ (Ordinal jd) (mem_index_enum _)).
    rewrite -(inj_eq val_inj)/=.
    mp; first by apply/eqP => ji; rewrite ji ltnn in ij.
    rewrite !nth_cat -[X in size X]uvE size_ngraph addn1.
    do 4 (rewrite ltnNge leq_addr/= subDnCA// subnn addn0).
    by rewrite rij rij1; case.
  - exact/uniq_dec_roots.
  move=> x; rewrite mem_dec_roots pu0/= rootE.
  apply/(nthP 0)/eqP => [[] i|x0].
    rewrite size_map size_enum_ord => id <-.
    rewrite (nth_map_ord _ _ (Ordinal id)).
    move: rroot => /(_ (Ordinal id) (mem_index_enum _) isT) /holds_subst.
    rewrite subst_env_cat -{1}uvE ngraph_cat -catA.
    rewrite subst_env_iota_catl ?size_ngraph//=.
    rewrite !nth_cat -![X in size X]uvE size_ngraph addn1.
    do 3 (rewrite ltnNge leq_addr/= subDnCA// subnn addn0).
    rewrite [r`_d.*2]nth_default ?size_tuple// => ru0.
    have /eqP: SAhornerRC n (row_mx u (\row_j r`_(j + i.*2))) = \row__ 0.
      apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
      by rewrite /= !enum_ordSl enum_ord0/= !mxE/= /bump/=.
    rewrite SAhornerRCE/= !mxE !(unsplitK (inr _)) !mxE.
    rewrite rowPE forall_ord2 !mxE/=.
    move pE: (poly _ _) => p.
    move qE: (poly _ _) => q.
    rewrite [q.[_]]complexE.
    suff ->: p = q by move=> /andP[] /eqP -> /eqP ->; rewrite mulr0 addr0.
    apply/polyP => j; rewrite -pE -qE !coef_poly/=.
    case: (ltnP j n) => [jn|//].
    rewrite (nth_map_ord _ _ (lshift 2 (Ordinal jn))) mxE (unsplitK (inl _)).
    by rewrite (nth_map_ord _ _ (Ordinal jn)).
  move: rall.
  have suvr: size (uv ++ r) = (n.+1 + d.*2)%N.
    by rewrite size_cat -uvE size_ngraph size_tuple addn1.
  rewrite -suvr => /nforallP.
  move=> /(_ (mktuple
    (fun i => if i == 0 then complex.Re x else complex.Im x)))/=.
  mp.
    apply/holds_subst.
    rewrite subst_env_cat -{1}uvE ngraph_cat -!catA.
    rewrite subst_env_iota_catl ?size_ngraph//= catA !nth_cat ltnn subnn suvr.
    rewrite !addnS ltnNge leqnSn/= ltnNge (leq_trans (leqnSn _) (leqnSn _))/=.
    rewrite subSn// subnn subSn// subSn// subnn !enum_ordSl enum_ord0/=.
    suff: SAhornerRC n
            (row_mx u (\row_j if j == 0 then complex.Re x else complex.Im x))
          = \row__ 0.
      move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      by rewrite /= !enum_ordSl enum_ord0/= !mxE/= /bump/=.
    rewrite SAhornerRCE/= !mxE !(unsplitK (inr _)) !mxE.
    apply/eqP; rewrite rowPE forall_ord2 !mxE/=.
    move: x0; move pE: (poly _ _) => p; move qE: (poly _ _) => q.
    suff ->: p = q by rewrite ComplexK => ->; rewrite !eqxx.
    apply/esym/polyP => j; rewrite -pE -qE !coef_poly/=.
    case: (ltnP j n) => [jn|//].
    rewrite (nth_map_ord _ _ (lshift 2 (Ordinal jn))) mxE (unsplitK (inl _)).
    by rewrite (nth_map_ord _ _ (Ordinal jn)).
  move=> /holdsOr/= [] i [_][_].
  rewrite !nth_cat ltnn subnn suvr !ltn_add2l ltn_double (ltn_ord i).
  rewrite -[X in size X]uvE size_ngraph addn1 ltnNge leq_addr/=.
  rewrite subDnCA// subnn addn0.
  rewrite ltnNge (leqnSn _)/= 2!addnS subSn// subnn.
  rewrite ltn_Sdouble (ltn_ord i) -addnS ltnNge leq_addr/=.
  rewrite subDnCA// subnn addn0 !enum_ordSl enum_ord0/= => -[] ri ris.
  exists i; first by rewrite size_map size_enum_ord.
  by apply/eqP; rewrite nth_map_ord eq_complex/= ri ris !eqxx.
apply/holdsOr => /=.
move pE: (poly _ _) vE => p vE.
have sn: (size (dec_roots p) < n)%N.
  rewrite size_dec_roots; last exact/char_num.
  apply/(leq_ltn_trans (leq_predn (leq_divp p _))).
  case: (posnP n) => n0.
    move/eqP: u0; elim; apply/rowP; case=> i ilt; exfalso.
    by rewrite n0 in ilt.
  case sp: (size p) => [//|k]; rewrite succnK.
  by move: sp => <-; rewrite -pE; apply/size_poly.
exists (Ordinal sn) => /=.
split; first exact/mem_index_enum.
split=> //.
split.
  rewrite -uvE ngraph_cat nth_cat size_ngraph ltnn subnn vE/= enum_ordSl/=.
  by rewrite mxE.
have ->: n.+1 = size uv by rewrite -uvE size_ngraph addn1.
apply/nexistsP.
exists (mktuple (fun i =>
  if odd i
  then complex.Im (dec_roots p)`_i./2
  else complex.Re (dec_roots p)`_i./2)%N).
split.
  apply/holdsAnd => /= i _ _; apply/holds_subst.
  rewrite subst_env_cat -{1}uvE ngraph_cat -!catA.
  rewrite subst_env_iota_catl ?size_ngraph//=.
  do 3 rewrite nth_cat ltnNge leq_addr/= subDnCA// subnn addn0.
  move: (ltn_ord i); rewrite -ltn_double => i2lt.
  rewrite (nth_map_ord _ _ (Ordinal i2lt))/= odd_double doubleK.
  move: (ltn_ord i); rewrite -ltn_Sdouble => i2slt.
  rewrite (nth_map_ord _ _ (Ordinal i2slt))/= odd_double/= uphalf_double.
  rewrite [(map _ _)`__]nth_default; last by rewrite size_map size_enum_ord.
  suff: SAhornerRC n (row_mx u (\row_j
          if j == 0
          then complex.Re (dec_roots p)`_i
          else complex.Im (dec_roots p)`_i))
        = \row__ 0.
    move=> /eqP; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
    by rewrite /= !enum_ordSl enum_ord0/= !mxE/= /bump/=.
  rewrite SAhornerRCE/= !mxE !(unsplitK (inr _)) !mxE.
  apply/eqP; rewrite rowPE forall_ord2 !mxE/= ComplexK.
  move qE: (poly _ _) => q.
  have <-: p = q.
    apply/esym/polyP => j; rewrite -pE -qE !coef_poly/=.
    case: (ltnP j n) => [jn|//].
    rewrite (nth_map_ord _ _ (lshift 2 (Ordinal jn))) mxE (unsplitK (inl _)).
    by rewrite (nth_map_ord _ _ (Ordinal jn)).
  have: (dec_roots p)`_i \in dec_roots p by apply/mem_nth.
  rewrite mem_dec_roots => /andP[_] /rootP ->.
  by rewrite eqxx.
split.
  apply/holdsAnd => /= i _ _.
  apply/holdsAnd => /= j _; rewrite eq_sym => /negPf ji.
  do 4 rewrite nth_cat ltnNge leq_addr/= subDnCA// subnn addn0.
  move: (ltn_ord i); rewrite -ltn_double => i2lt.
  rewrite (nth_map_ord _ _ (Ordinal i2lt))/= odd_double doubleK.
  move: (ltn_ord i); rewrite -ltn_Sdouble => i2slt.
  rewrite (nth_map_ord _ _ (Ordinal i2slt))/= odd_double/= uphalf_double.
  move: (ltn_ord j); rewrite -ltn_double => j2lt.
  rewrite (nth_map_ord _ _ (Ordinal j2lt))/= odd_double doubleK.
  move: (ltn_ord j); rewrite -ltn_Sdouble => j2slt.
  rewrite (nth_map_ord _ _ (Ordinal j2slt))/= odd_double/= uphalf_double.
  move: (uniq_dec_roots p) => /(nth_uniq 0)/= /(_ i j (ltn_ord i) (ltn_ord j)).
  rewrite (inj_eq val_inj) ji => /negP/negP.
  by rewrite eq_complex negb_and => /orP [/eqP|/eqP] ij; [left|right].
move tE: (mktuple _) => t.
rewrite -[X in (_ + X)%N](size_tuple t) -size_cat.
apply/nforallP => w/= /holds_subst.
rewrite subst_env_cat -{1}uvE ngraph_cat -!catA.
rewrite subst_env_iota_catl ?size_ngraph//= !addnS.
rewrite -[in X in (_ + X)%N](size_tuple t) -size_cat catA.
rewrite nth_cat ltnNge leqnn/= subnn.
rewrite nth_cat ltnNge leqnSn/= subSn// subnn.
rewrite [(_ ++ _)`__]nth_default => [w0|]; last first.
  by rewrite size_cat size_tuple addn2.
have: (w`_0 +i* w`_1)%C \in dec_roots p.
  rewrite mem_dec_roots -{1}pE pu0/= rootE.
   have: SAhornerRC n (row_mx u (\row_j w`_j)) == \row__ 0.
    rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
    by rewrite /= !enum_ordSl enum_ord0/= !mxE/= /bump/=.
  rewrite SAhornerRCE/= !mxE !(unsplitK (inr _)) !mxE.
  rewrite rowPE forall_ord2 !mxE/=.
  move qE: (poly _ _) => q.
  suff <-: p = q by rewrite eq_complex.
  apply/esym/polyP => j; rewrite -pE -qE !coef_poly/=.
  case: (ltnP j n) => [jn|//].
  rewrite (nth_map_ord _ _ (lshift 2 (Ordinal jn))) mxE (unsplitK (inl _)).
  by rewrite (nth_map_ord _ _ (Ordinal jn)).
move=> /(nthP 0)/= [] i ip iE.
apply/holdsOr => /=; exists (Ordinal ip).
split; first exact/mem_index_enum.
split=> //.
split; rewrite nth_cat.
  rewrite ltnn subnn -catA nth_cat ltnNge leq_addr/= subDnCA// subnn addn0. 
  rewrite -ltn_double in ip.
  rewrite nth_cat size_tuple ip -tE (nth_map_ord _ _ (Ordinal ip))/=.
  by rewrite odd_double doubleK iE.
rewrite ltnNge leqnSn/= -catA subSn// subnn.
rewrite nth_cat ltnNge leq_addr/= subDnCA// subnn addn0.
rewrite -ltn_Sdouble in ip.
rewrite nth_cat size_tuple ip -tE (nth_map_ord _ _ (Ordinal ip))/=.
by rewrite odd_double uphalf_double iE.
Qed.

Fact SAfun_SAnbrootsC n :
  (SAnbrootsC_graph n \in @SAfunc _ n 1)
  && (SAnbrootsC_graph n \in @SAtot _ n 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAnbrootsC_graphP => /eqP -> /eqP.
apply/inSAtot => u.
exists (\row__ (size (dec_roots (\poly_(i < n) ((ngraph u)`_i)%:C%C)))%:R)%R.
by rewrite SAnbrootsC_graphP.
Qed.

Definition SAnbrootsC n := MkSAfun (SAfun_SAnbrootsC n).

Lemma SAnbrootsCE n u :
  SAnbrootsC n u
  = (\row__ (size (dec_roots (\poly_(i < n) ((ngraph u)`_i)%:C%C)))%:R)%R.
Proof. by apply/eqP; rewrite inSAfun SAnbrootsC_graphP. Qed.

Definition SAset_lt (s t : {SAset F^1}) :=
  (t != SAset0 F 1)
  && rcf_sat [::]
    ('forall 'X_0, s ==> 'forall 'X_1, subst_formula [:: 1%N] t
      ==> ('X_0 <% 'X_1))%oT.

Lemma SAset_ltP (s t : {SAset F^1}) :
  reflect (t != SAset0 F 1 /\ forall x y, x \in s -> y \in t -> x 0 0 < y 0 0)
    (SAset_lt s t).
Proof.
apply/andPP; first exact/idP.
apply/(iffP (rcf_satP _ _)) => /=.
  move=> + x y /rcf_satP + /rcf_satP.
  rewrite /ngraph/= enum_ordSl enum_ord0/= => /(_ (x 0 0)) /[apply].
  move=> /(_ (y 0 0)) + yt.
  have /[swap]/[apply]// : holds [:: x 0 0; y 0 0] (subst_formula [:: 1%N] t).
  exact/holds_subst.
move=> + x xs y /holds_subst/= yt => /(_ (\row__ x) (\row__ y)).
have /[swap]/[apply] : \row__ x \in s.
  by apply/rcf_satP; rewrite /ngraph/= enum_ordSl enum_ord0 /= mxE.
have /[swap]/[apply] : \row__ y \in t.
  by apply/rcf_satP; rewrite /ngraph/= enum_ordSl enum_ord0 /= mxE.
by rewrite !mxE.
Qed.

Definition SAsetltType := {SAset F^1}.

Lemma SAset_lt_irr : irreflexive SAset_lt.
Proof.
move=> s; apply/negP => /SAset_ltP [].
have [->|[x xs]] := set0Vmem s; first by rewrite eqxx.
by move=> _ /(_ x x xs xs); rewrite ltxx.
Qed.

Lemma SAset_lt_trans : transitive SAset_lt.
Proof.
move=> s t u /SAset_ltP [].
have [->|[x xs] _ ts /SAset_ltP [u0] su] := set0Vmem s; first by rewrite eqxx.
by apply/SAset_ltP; split=> // y z yt zu; apply/(lt_trans (ts y x yt xs))/su.
Qed.

HB.instance Definition _ := Equality.on SAsetltType.
HB.instance Definition _ := Choice.on SAsetltType.
HB.instance Definition _ := Order.Lt_isPOrder.Build ring_display SAsetltType
  SAset_lt_irr SAset_lt_trans.

Lemma SAset_lt_trivI (S : seq SAsetltType) :
  path.sorted <%O S -> SAset_trivI [fset x | x in S].
Proof.
set T := [fset x | x in S].
have inT x : x \in T = (x \in S).
  by apply/imfsetP/idP => [[] y yS -> //|xS]; exists x.
move=> /(lt_sorted_ltn_nth (SAset0 F 1 : SAsetltType)) Ssort.
apply/forallP => /= -[] /= s; rewrite inT => sS.
(* What ??? *)
move: (elimT (nthP (SAset0 F 1)) sS) => {sS} [] i iS <-.
apply/forallP => /= -[] /= t; rewrite inT => tS.
move: (elimT (nthP (SAset0 F 1)) tS) => {tS} [] j jS <-.
apply/implyP; move: iS jS; wlog: i j / (i < j)%N => ij iS jS ijE.
  have /lt_total : i != j.
    by move: ijE; apply/contra => /eqP ->; apply/eqP.
  move=> /orP [ij'|ji]; first exact/ij.
  by rewrite SAset_disjointC; apply/ij => //; rewrite eq_sym.
move: (Ssort i j); rewrite !inE => /(_ iS jS).
rewrite ij => /SAset_ltP [_] {}ij.
rewrite /SAset_disjoint -subset0; apply/SAset_subP => x.
by rewrite inSAsetI => /andP[] /ij /[apply]; rewrite ltxx.
Qed. (* ~4'' *)

Definition SAset_fiber n m (s : {SAset F^(n + m)}) (x : 'rV[F]_n) :=
  SApreimset (SAjoin (SAfun_const m x) (SAid m)) s.

Lemma inSAset_fiber n m (s : {SAset F^(n + m)}) x y :
  (y \in SAset_fiber s x) = (row_mx x y \in s).
Proof. by rewrite inSApreimset SAjoinE SAfun_constE SAidE. Qed.

Definition partition_of_pts (xi : seq F) : seq {SAset F^1} :=
  [seq
    if i == 0 then
      \big[@SAsetI F 1/SAsetT F 1]_(x <- xi) SAset_itv `]-oo, x[%R
    else if i == (size xi).*2 then
      \big[@SAsetI F 1/SAsetT F 1]_(x <- xi) SAset_itv `]x, +oo[%R
    else if odd i then
      [set \row__ xi`_i./2]
    else SAset_itv `]xi`_i./2.-1, xi`_i./2[%R
  | i <- iota 0 (size xi).*2.+1].

Lemma partition_of_pts0 : partition_of_pts [::] = [:: SAsetT F _].
Proof. by rewrite /partition_of_pts /= big_nil. Qed.

Lemma sorted_partition_of_pts xi :
  path.sorted <%O xi ->
  path.sorted <%O (partition_of_pts xi : seq SAsetltType).
Proof.
move=> /[dup] /(lt_sorted_ltn_nth 0) xilt /(lt_sorted_leq_nth 0) xile.
apply/(path.sortedP (SAset0 F 1)) => i /[dup].
rewrite /partition_of_pts size_map size_iota {1}ltnS => ilt islt.
rewrite (nth_map 0) ?size_iota ?ltnS 1?ltnW// nth_iota// ?ltnS 1?ltnW// add0n.
rewrite (nth_map 0) ?size_iota// nth_iota// add0n/=.
have xi0: (0 < size xi)%N by rewrite -double_gt0 (leq_ltn_trans (leq0n i)).
rewrite (ltn_eqF ilt).
apply/SAset_ltP; rewrite -subset0; case: (posnP i) => [->|i0].
  have -> : 0.+1 == (size xi).*2 = false by case: (size xi).
  split=> [|x y].
    apply/negP => /SAset_subP /(_ (\row__ xi`_0)).
    by rewrite inSAset_seq mem_seq1 eqxx inSAset0 => /(_ isT).
  rewrite inSAset_bigcap inSAset1 => /allP/(_ xi`_0)/= + /eqP ->.
  rewrite inSAset_itv in_itv/= mxE; apply.
  by apply/mem_nth; move: ilt; case: (size xi).
move: islt; rewrite leq_eqVlt ltnS eqSS => /orP[/[dup] /eqP iE ->|islt].
  split=> [|x y].
    apply/negP => /SAset_subP /(_ (\row__ (last 0 xi + 1))%R).
    rewrite inSAset_bigcap inSAset0.
    move=> H; (suff: false by []); apply: H.
    apply/allP => x /(nthP 0) [j] jlt <- /=.
    rewrite inSAset_itv in_itv/= mxE andbT.
    move: (xile j (size xi).-1); rewrite !inE ltn_predL => /(_ jlt xi0).
    rewrite -ltnS prednK// jlt => xj.
    by apply/(le_lt_trans xj); rewrite -nth_last -subr_gt0 addrAC subrr add0r.
  have -> /=: odd i by rewrite -[odd i]negbK -oddS iE odd_double.
  rewrite inSAset_seq mem_seq1 inSAset_bigcap => /eqP -> /allP/(_ xi`_i./2) /=.
  rewrite inSAset_itv in_itv/= andbT mxE; apply.
  by apply/mem_nth; rewrite ltn_half_double.
rewrite (ltn_eqF islt).
case/boolP: (odd i) => /= i2; (split=> [|x y];
    [apply/negP => /SAset_subP|
    rewrite inSAset_seq mem_seq1 inSAset_itv in_itv/=]); first last.
- by move=> /andP[_] xlt /eqP ->; rewrite mxE uphalf_half (negPf i2).
- move=> /(_ (\row__ xi`_(uphalf i))); rewrite inSAset_seq mem_head inSAset0.
  by move=> /(_ isT).
- by move=> /eqP -> /andP[] + _; rewrite mxE uphalf_half i2 add1n succnK.
move=> /(_ (\row__ (2^-1 * (xi`_(uphalf i) + xi`_(uphalf i).-1)))%R).
rewrite inSAset_itv in_itv/= mxE inSAset0.
move=> H; (suff: false by []); apply: H.
have ltr02 : 0 < 2 :> F by [].
have neq20 : 2 != 0 :> F by rewrite pnatr_eq0.
move: (xilt (uphalf i).-1 (uphalf i)); rewrite !inE.
rewrite prednK ?uphalf_gt0// leq_uphalf_double ltn_uphalf_double.
move=> /(_ (ltnW ilt) islt); rewrite leqnn => xii.
by apply/andP; split; rewrite -subr_gt0 -(pmulr_rgt0 _ ltr02) mulrBr mulrA
  divff// mul1r mulr_natl mulr2n opprD addrACA subrr ?add0r ?addr0 subr_gt0.
Qed.

Lemma SAset_partition_of_ptsU (xi : seq F) :
  path.sorted <=%O xi ->
  \big[@SAsetU F 1/SAset0 F 1]_(s <- partition_of_pts xi) s = SAsetT F 1.
Proof.
elim: xi => [|x xi IHxi]; first by rewrite partition_of_pts0 big_seq1.
move=> /[dup] xile /path.path_sorted xile'.
apply/eqP; rewrite -subTset; apply/SAset_subP => y.
rewrite -IHxi// inSAset_bigcup => /hasP[] /= s sxi.
(* What??? *)
move: (elimT (nthP (SAset0 F _)) sxi) => {sxi} [] i.
rewrite size_map size_iota => ilt <-.
rewrite (nth_map 0) ?size_iota// nth_iota// add0n.
case: (posnP i) => i0.
  rewrite inSAset_bigcap => yxi.
  case: (ltP (y 0 0) x) => [yx|].
    rewrite inSAset_bigcup; apply/hasP.
    exists (nth (SAset0 F 1) (partition_of_pts (x :: xi)) 0).
      by apply/mem_nth; rewrite size_map size_iota.
    rewrite (nth_map 0)// nth_iota//= inSAset_bigcap/=.
    by rewrite inSAset_itv in_itv/= yx.
  rewrite le_eqVlt => /orP[/eqP ->|xy].
    rewrite inSAset_bigcup; apply/hasP.
    exists (nth (SAset0 F 1) (partition_of_pts ((y 0 0) :: xi)) 1).
      by apply/mem_nth; rewrite size_map size_iota/= doubleS.
    rewrite (nth_map 0)// nth_iota//= inSAset_seq mem_seq1 rowPE forall_ord1.
    by rewrite mxE.
  rewrite inSAset_bigcup; apply/hasP.
  exists (nth (SAset0 F 1) (partition_of_pts (x :: xi)) 2).
    by apply/mem_nth; rewrite size_map size_iota/= doubleS.
  rewrite (nth_map 0)// nth_iota//=.
  case: xi {IHxi ilt xile xile'} yxi => /= [|z xi] yxi.
    by rewrite big_seq1 inSAset_itv in_itv/= xy.
  rewrite inSAset_itv in_itv/= xy.
  by move: yxi => /andP[+] _; rewrite inSAset_itv in_itv/=.
case/boolP: (_ == _) => [_|im].
  rewrite inSAset_bigcap => /= yxi.
  rewrite inSAset_bigcup; apply/hasP.
  exists (nth (SAset0 F 1) (partition_of_pts (x :: xi)) ((size xi).+1.*2)).
    by apply/mem_nth; rewrite size_map size_iota.
  rewrite (nth_map 0) ?size_iota// nth_iota//= eqxx.
  rewrite inSAset_bigcap/= inSAset_itv in_itv/= yxi.
  case: xi {IHxi xile'} i0 ilt xile yxi; first by case: i.
  move=> z xi _ _ /= /andP[] xz _ /andP[].
  by rewrite inSAset_itv in_itv/= => /andP[] /(le_lt_trans xz) ->.
case/boolP: (odd i) => i2 yE;
  rewrite inSAset_bigcup; apply/hasP;
  (exists (nth (SAset0 F 1) (partition_of_pts (x :: xi)) i.+2);
    first by apply/mem_nth; rewrite size_map size_iota/= doubleS 2!ltnS);
  (rewrite (nth_map 0); last by rewrite size_iota/= doubleS 2!ltnS);
  rewrite nth_iota/= doubleS 2?ltnS// 2!eqSS (negPf im) i2//.
rewrite -[X in (x :: xi)`_X]prednK// half_gt0.
by case: i {ilt im yE} i0 i2 => [//|]; case.
Qed.

Lemma SAset_partition_of_pts (xi : seq F) :
  path.sorted <%O xi -> SAset_partition [fset x | x in partition_of_pts xi].
Proof.
move=> /[dup] /[dup] xisort.
move=> /(lt_sorted_ltn_nth 0) xilt /(lt_sorted_leq_nth 0) xile.
set S := [fset x | x in partition_of_pts xi].
have inS x : x \in S = (x \in partition_of_pts xi).
  by apply/imfsetP/idP => [[] y yS -> //|xS]; exists x.
apply/andP; split; last first.
  move: xisort; rewrite lt_sorted_uniq_le => /andP[_].
  move=> /SAset_partition_of_ptsU <-.
  apply/SAsetP => x; rewrite 2!inSAset_bigcup.
  apply/hasP/hasP => /= -[].
    by move=> [] /= s + _ /=; rewrite inS => sxi xs; exists s.
  move=> s; rewrite -inS => sS xs.
  by exists [` sS] => //; apply/mem_index_enum.
apply/andP; split; last exact/SAset_lt_trivI/sorted_partition_of_pts.
rewrite inS; apply/negP => xi0.
(* What??? *)
move: (elimT (nthP (SAset0 F 1)) xi0) => {xi0} [] i.
rewrite size_map size_iota; case: (posnP i) => [->|i0] ixi; last first.
  move: xisort => /sorted_partition_of_pts.
  move=> /(lt_sorted_ltn_nth (SAset0 F 1 : SAsetltType)).
  move=> /(_ 0 i); rewrite !inE size_map size_iota => /(_ isT ixi).
  by rewrite i0 => /SAset_ltP[] /eqP + _.
rewrite (nth_map 0) ?size_iota// nth_iota//= => xi0.
suff: \row__ (xi`_0 - 1) \in SAset0 F 1 by rewrite inSAset0.
rewrite -xi0 inSAset_bigcap; apply/allP => /= x /(nthP 0) [j] jxi <-.
rewrite inSAset_itv in_itv/= mxE.
move: (xile 0 j); rewrite !inE => /(_ (leq_ltn_trans (leq0n _) jxi) jxi).
rewrite leq0n => x0j; apply/(lt_le_trans _ x0j).
by rewrite -subr_gt0 opprB addrCA subrr addr0.
Qed.

Definition partition_of_graphs n
    (xi : seq {SAfun F^n -> F^1}) : seq {SAset F^(n + 1)%N} :=
  [seq
    if i == 0 then
      \big[@SAsetI F (n + 1)/SAsetT F (n + 1)]_(f <- xi) SAhypograph f
    else if i == (size xi).*2 then
      \big[@SAsetI F (n + 1)/SAsetT F (n + 1)]_(f <- xi) SAepigraph f
    else if odd i then
      SAgraph xi`_i./2
    else SAepigraph (xi`_i./2.-1) :&: SAhypograph (xi`_i./2)
  | i <- iota 0 (size xi).*2.+1].

Lemma SApreimsetI n m (f : {SAfun F^n -> F^m}) s t :
  SApreimset f (s :&: t) = (SApreimset f s) :&: SApreimset f t.
Proof.
by apply/eqP/SAsetP => x; rewrite inSApreimset !inSAsetI !inSApreimset.
Qed.

Lemma SApreimsetU n m (f : {SAfun F^n -> F^m}) s t :
  SApreimset f (s :|: t) = SApreimset f s :|: SApreimset f t.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetU !inSApreimset inSAsetU. Qed.

Lemma SApreimsetT n m f : SApreimset f (SAsetT F n) = SAsetT F m.
Proof.
apply/eqP; rewrite -subTset; apply/SAset_subP => x _.
by rewrite inSApreimset inSAsetT.
Qed.

Lemma SApreimset_bigcap n m (I : Type) (r : seq I) (P : pred I)
  (S : I -> {SAset F^m}) (f : {SAfun F^n -> F^m}) :
  SApreimset f (\big[SAsetI (n:=m)/SAsetT F m]_(i <- r | P i) S i) =
      \big[SAsetI (n:=n)/SAsetT F n]_(i <- r | P i) SApreimset f (S i).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil SApreimsetT.
rewrite 2!big_cons; case: (P i) => //.
by rewrite SApreimsetI IHr.
Qed.

Lemma SAset_fiber_fun n m (f : {SAfun F^n -> F^m}) (x : 'rV[F]_n) :
  SAset_fiber f x = [set f x].
Proof.
apply/eqP/SAsetP => y; rewrite inSApreimset SAjoinE -inSAfun.
by rewrite SAfun_constE SAidE inSAset_seq mem_seq1 eq_sym.
Qed.

Lemma SAset_fiber_epigraph n (f : {SAfun F^n -> F^1}) (x : 'rV[F]_n) :
  SAset_fiber (SAepigraph f) x = SAset_itv `]f x 0 0, +oo[%R.
Proof.
apply/eqP/SAsetP => y; rewrite inSApreimset inSAepigraph SAjoinE row_mxKl.
by rewrite row_mxKr SAfun_constE SAidE inSAset_itv in_itv/= andbT.
Qed.

Lemma SAset_fiber_hypograph n (f : {SAfun F^n -> F^1}) (x : 'rV[F]_n) :
  SAset_fiber (SAhypograph f) x = SAset_itv `]-oo, f x 0 0[%R.
Proof.
apply/eqP/SAsetP => y; rewrite inSApreimset inSAhypograph SAjoinE row_mxKl.
by rewrite row_mxKr SAfun_constE SAidE inSAset_itv in_itv/=.
Qed.

Lemma SAset_fiber_partition_of_graphs (n : nat)
  (xi : seq {SAfun F^n -> F^1}) (x : 'rV[F]_n) :
  [seq SAset_fiber s x | s <- partition_of_graphs xi] =
      partition_of_pts [seq (f : {SAfun F^n -> F^1}) x 0 0 | f <- xi].
Proof.
apply/(@eq_from_nth _ (SAset0 F 1)) => [|i]; first by rewrite !size_map.
rewrite 2!size_map size_iota => ilt.
rewrite (nth_map 0); last by rewrite size_iota size_map.
rewrite (nth_map (SAset0 F _)); last by rewrite size_map size_iota.
rewrite (nth_map 0) ?size_iota// nth_iota// nth_iota ?size_map// add0n.
case: (posnP i) => [_|i0].
  rewrite big_map /SAset_fiber SApreimset_bigcap.
  apply/eq_bigr => f _; exact/SAset_fiber_hypograph.
case/boolP: (_ == _) => [_|im].
  rewrite big_map /SAset_fiber SApreimset_bigcap.
  apply/eq_bigr => f _; exact/SAset_fiber_epigraph.
case/boolP: (odd i) => i2.
  rewrite SAset_fiber_fun (nth_map 0); last first.
    by rewrite -ltn_double odd_halfK// prednK.
  by congr [set _]; apply/eqP; rewrite rowPE forall_ord1 mxE.
rewrite /SAset_fiber SApreimsetI [X in X :&: _]SAset_fiber_epigraph.
rewrite [X in _ :&: X]SAset_fiber_hypograph.
apply/eqP/SAsetP => y; rewrite inSAsetI !inSAset_itv !in_itv/= andbT.
rewrite (nth_map 0).
  by rewrite (nth_map 0)// -ltn_double even_halfK// ltn_neqAle im -ltnS.
rewrite -ltn_double double_pred even_halfK// prednK; last first.
  by case: i {ilt im} i0 i2 => //; case.
by rewrite -ltnS prednK// ltnW.
Qed.

Lemma SApreimset0 n m f : SApreimset f (SAset0 F n) = SAset0 F m.
Proof.
apply/eqP; rewrite -subset0; apply/SAset_subP => x.
by rewrite inSApreimset [_ _ \in _]inSAset0.
Qed.

Lemma SAset_partition_of_graphs (n : nat) (xi : seq (SAfunltType n)) :
  path.sorted <%O xi -> SAset_partition [fset x | x in partition_of_graphs xi].
Proof.
set S := [fset x | x in partition_of_graphs xi].
have inS x : x \in S = (x \in partition_of_graphs xi).
  by apply/imfsetP/idP => [[] y yS -> //|xS]; exists x.
move=> /(lt_sorted_ltn_nth (0 : SAfunltType n)) xisort.
have {}xisort x :
    path.sorted <%O [seq (f : {SAfun F^n -> F^1}) x 0 0 | f <- xi].
  apply/path.pairwise_sorted/(pairwiseP 0) => i j.
  rewrite !inE size_map => ilt jlt ij.
  move: (xisort i j); rewrite !inE => /(_ ilt jlt); rewrite ij.
  by rewrite (nth_map 0)// (nth_map 0)// => /SAfun_ltP.
apply/andP; split; last first.
  rewrite -subTset; apply/SAset_subP => x _.
  move: (SAset_partition_of_pts (xisort (lsubmx x))).
  set T := [fset x | x in _].
  move=> /andP[_]; rewrite -subTset => /SAset_subP/(_ (rsubmx x)).
  rewrite inSAsetT => /(_ isT).
  rewrite 2!inSAset_bigcup => /= /hasP[[]] /= s + _.
  move=> /imfsetP [t] /= + ->.
  rewrite -SAset_fiber_partition_of_graphs => /mapP[u].
  rewrite -inS => uS ->.
  rewrite inSAset_fiber hsubmxK => xu.
  by apply/hasP; exists [` uS ] => //; apply/mem_index_enum.
apply/andP; split.
  apply/negP; rewrite inS => xi0.
  move: (elimT (nthP (SAset0 F _)) xi0) => {xi0} [] i.
  rewrite size_map size_iota => ilt i0.
  have: SAset_fiber (SAset0 F (n + 1)) 0 = SAset0 F _.
    by rewrite /SAset_fiber SApreimset0.
  rewrite -i0 -[LHS](@nth_map _ _ _ (SAset0 F _) (fun s => SAset_fiber s 0));
      last by rewrite size_map size_iota.
  rewrite SAset_fiber_partition_of_graphs => {}i0.
  move: (SAset_partition_of_pts (xisort 0)).
  set T := [fset x | x in _] => /andP[] /andP[] + _ _ => /imfsetP; apply.
  exists (SAset0 F 1) => //=.
  by rewrite -i0 mem_nth// size_map size_iota size_map.
apply/forallP => -[] /= s; rewrite inS => sxi.
move: (elimT (nthP (SAset0 F _)) sxi) => {sxi} [] i + <-.
rewrite size_map size_iota => ilt.
apply/forallP => -[] /= t; rewrite inS => txi.
move: (elimT (nthP (SAset0 F _)) txi) => {txi} [] j + <-.
rewrite size_map size_iota => jlt.
apply/implyP => ij.
case/boolP: (i == j) => [/eqP ijE|{}ij]; first by rewrite ijE eqxx in ij.
rewrite /SAset_disjoint -subset0; apply/SAset_subP => x.
rewrite inSAsetI => /andP[] xii xj.
move: (SAset_partition_of_pts (xisort (lsubmx x))).
set xi' := [seq (f : {SAfun F^n -> F^1}) (lsubmx x) 0 0 | f <- xi].
set T := [fset x | x in _] => /andP[] /andP[_] + _.
have inT y : y \in T = (y \in partition_of_pts xi').
  by apply/imfsetP/idP => [[] z zS -> //|yS]; exists y.
have nk k: (k < (size xi).*2.+1)%N ->
    nth (SAset0 F _) (partition_of_pts xi') k \in T.
  by rewrite inT => klt; apply/mem_nth; rewrite size_map size_iota size_map.
move=> /forallP/(_ [` nk i ilt]) /forallP/(_ [` nk j jlt]) /implyP/=.
rewrite nth_uniq ?size_map ?size_iota//; last first.
  by move: (xisort (lsubmx x)) => /sorted_partition_of_pts /lt_sorted_uniq.
move=> /(_ ij) /eqP ij0.
suff: rsubmx x \in SAset0 F 1 by rewrite inSAset0.
rewrite -ij0 -!SAset_fiber_partition_of_graphs inSAsetI.
rewrite (nth_map (SAset0 F _)) ?size_map ?size_iota//.
rewrite (nth_map (SAset0 F _)) ?size_map ?size_iota//.
by rewrite !inSAset_fiber hsubmxK xii.
Qed.

Definition partition_of_graphs_above n (s : {SAset F^n})
    (xi : seq {SAfun F^n -> F^1}) : {fset {SAset F^(n + 1)%N}} :=
  [fset x :&: (s :*: SAsetT F 1) | x in partition_of_graphs xi].

Lemma SAset_partition_of_graphs_above n (S : {fset {SAset F^n}})
    (xi : S -> seq (SAfunltType n)) :
  SAset_partition S ->
  (forall s, path.sorted <%O (xi s)) -> 
  SAset_partition
    (\big[fsetU/fset0]_(s : S)
      partition_of_graphs_above (val s) (in_tuple (xi s))).
Proof.
move=> /andP[] /andP[] S0 SI /eqP SU xisort.
have {}xisort (s : S) x :
    path.sorted <%O [seq (f : {SAfun F^n -> F^1}) x 0 0 | f <- xi s].
  apply/path.pairwise_sorted/(pairwiseP 0) => i j.
  rewrite !inE size_map => ilt jlt ij.
  move: (xisort s) => /(lt_sorted_ltn_nth (0 : SAfunltType n))/(_ i j).
  rewrite !inE => /(_ ilt jlt); rewrite ij.
  by rewrite (nth_map 0)// (nth_map 0)// => /SAfun_ltP.
apply/andP; split; last first.
  rewrite -subTset; apply/SAset_subP => x _.
  have: lsubmx x \in SAsetT F n by rewrite inSAsetT.
  rewrite -SU inSAset_bigcup => /hasP[] /= s _ xs.
  move: (SAset_partition_of_pts (xisort s (lsubmx x))).
  set T := [fset x | x in _] => /andP[_].
  rewrite -subTset => /SAset_subP/(_ (rsubmx x)).
  rewrite inSAsetT => /(_ isT).
  rewrite 2!inSAset_bigcup => /= /hasP[[]] /= t + _.
  move=> /imfsetP [u] /= + ->.
  rewrite -SAset_fiber_partition_of_graphs => /mapP[v] vxi ->.
  rewrite inSAset_fiber hsubmxK => xv.
  have vS:
      v :&: \val s :*: SAsetT F 1
        \in \bigcup_(s | true) partition_of_graphs_above (val s) (xi s).
    apply/bigfcupP; exists s; first by rewrite mem_index_enum.
    by apply/imfsetP; exists v.
  apply/hasP; exists [` vS ] => /=; first exact/mem_index_enum.
  by rewrite inSAsetI xv inSAsetX xs inSAsetT.
apply/andP; split.
  apply/negP => /bigfcupP [] /= s _ /imfsetP [t] /= txi.
  move: (elimT (nthP (SAset0 F _)) txi) => {txi} [] i.
  rewrite size_map size_iota => ilt <- i0.
  have [s0|[x xs]] := set0Vmem (val s).
    by move: S0; rewrite -s0 => /negP; apply; apply/(fsvalP s).
  have: SAset_fiber (SAset0 F (n + 1)) x = SAset0 F _.
    by rewrite /SAset_fiber SApreimset0.
  rewrite i0 /SAset_fiber SApreimsetI -/(SAset_fiber _ _).
  have ->:
      SApreimset (SAjoin (SAfun_const 1 x) (SAid 1)) (fsval s :*: SAsetT F 1)
      = SAsetT F _.
    apply/eqP/SAsetP => y; rewrite inSApreimset SAjoinE SAfun_constE inSAsetX.
    by rewrite row_mxKl xs !inSAsetT.
  rewrite SAsetIT.
  rewrite -[LHS](@nth_map _ _ _ (SAset0 F _) (fun s => SAset_fiber s x));
      last by rewrite size_map size_iota.
  rewrite SAset_fiber_partition_of_graphs => {}i0.
  move: (SAset_partition_of_pts (xisort s x)).
  set T := [fset x | x in _] => /andP[] /andP[] + _ _ => /imfsetP; apply.
  exists (SAset0 F 1) => //=.
  by rewrite -i0 mem_nth// size_map size_iota size_map.
apply/forallP => -[] /= a /bigfcupP [s] _ /imfsetP [sa] /= saxi.
move: (elimT (nthP (SAset0 F _)) saxi) => {saxi} [] i + <- ->.
rewrite size_map size_iota => ilt.
apply/forallP => -[] /= b /bigfcupP [t] _ /imfsetP [tb] /=.
move=>/(nthP (SAset0 F _)) [j] + <- ->.
rewrite size_map size_iota => jlt; apply/implyP.
move: jlt; have [<- jlt ij|st _ _] := eqVneq s t; last first.
  rewrite /SAset_disjoint -subset0; apply/SAset_subP => x.
  rewrite !inSAsetI 2!inSAsetX.
  move=> /andP[] /andP[_] /andP[xs] _ /andP[_] /andP[xt] _.
  move: SI => /forallP/(_ s) /forallP /(_ t) /implyP.
  rewrite (inj_eq val_inj) => /(_ st).
  rewrite /SAset_disjoint /subset0 => /eqP st0.
  suff: lsubmx x \in SAset0 F n by rewrite inSAset0.
  by rewrite -st0 inSAsetI xs.
case/boolP: (i == j) => [/eqP ijE|{}ij]; first by rewrite ijE eqxx in ij.
rewrite /SAset_disjoint -subset0; apply/SAset_subP => x.
rewrite !inSAsetI => /andP[] /andP[] xii _ /andP[] xj _.
move: (SAset_partition_of_pts (xisort s (lsubmx x))).
set xi' := [seq (f : {SAfun F^n -> F^1}) (lsubmx x) 0 0 | f <- xi s].
set T := [fset x | x in _] => /andP[] /andP[_] + _.
have inT y : y \in T = (y \in partition_of_pts xi').
  by apply/imfsetP/idP => [[] z zS -> //|yS]; exists y.
have nk k: (k < (size (xi s)).*2.+1)%N ->
    nth (SAset0 F _) (partition_of_pts xi') k \in T.
  by rewrite inT => klt; apply/mem_nth; rewrite size_map size_iota size_map.
move=> /forallP/(_ [` nk i ilt]) /forallP/(_ [` nk j jlt]) /implyP/=.
rewrite nth_uniq ?size_map ?size_iota//; last first.
  by move: (xisort s (lsubmx x)) => /sorted_partition_of_pts /lt_sorted_uniq.
move=> /(_ ij) /eqP ij0.
suff: rsubmx x \in SAset0 F 1 by rewrite inSAset0.
rewrite -ij0 -!SAset_fiber_partition_of_graphs inSAsetI.
rewrite (nth_map (SAset0 F _)) ?size_map ?size_iota//.
rewrite (nth_map (SAset0 F _)) ?size_map ?size_iota//.
by rewrite !inSAset_fiber hsubmxK xii.
Qed.

Lemma SAset_cast_partition_of_graphs_above n (s : {SAset F^n})
  (xi : seq (SAfunltType n)) t :
  sorted <%O xi ->
  t \in partition_of_graphs_above s xi -> SAset_cast n t = s.
Proof.
move=> xisort /imfsetP[] /= u uxi ->.
apply/eqP/SAsetP => x; apply/inSAset_castDn/idP => [|xs].
  by move=> [y] [+] ->; rewrite inSAsetI inSAsetX => /andP[_] /andP[].
move: uxi => /(nthP (SAset0 F _)) [] i.
rewrite size_map size_iota => ilt <-.
set xi' := [seq (f : {SAfun F^n -> F^1}) x ord0 ord0 | f <- xi].
have: sorted <%O xi' by apply/(homo_sorted _ _ xisort) => f g /SAfun_ltP /(_ x).
move=> /SAset_partition_of_pts.
set S := [fset x0 | x0 in _] => /andP[] /andP[] + _ _.
have [<-|[y] yi _] := set0Vmem (nth (SAset0 F _) (partition_of_pts xi') i).
  move=> /negP; elim; apply/imfsetP.
  exists (nth (SAset0 F 1) (partition_of_pts xi') i) => //=.
  by apply/mem_nth; rewrite 2!size_map size_iota.
exists (row_mx x y); split; last by rewrite row_mxKl.
move: yi; rewrite -SAset_fiber_partition_of_graphs.
rewrite (nth_map (SAset0 F _)) ?size_map ?size_iota// inSAset_fiber inSAsetI.
by move=> ->; rewrite inSAsetX row_mxKl row_mxKr xs inSAsetT.
Qed.

Lemma SAset_partition_cast n m (S : {fset {SAset F^n}}) :
  n = m -> SAset_partition [fset SAset_cast m x | x in S] = SAset_partition S.
Proof.
move=> nm; move: S; rewrite nm => S; congr SAset_partition.
apply/fsetP => /= x; apply/imfsetP/idP => [|xS].
  by move=> /= [y] yS ->; rewrite SAset_cast_id.
by exists x => //; rewrite SAset_cast_id.
Qed.

End SAfunOps.

Lemma SAset_formula (F : rcfType) (n : nat) (s : {SAset F^n}) :
  {f : formula F | rformula f /\ qf_form f /\ s = [set | f]}.
Proof.
exists (qf_elim s); split; first exact/rform_qf_elim.
split; first exact/qf_elim_qf.
apply/eqP/SAsetP => x.
apply/rcf_satP/SAin_setP => [xs|/rcf_satP/qf_elim_holdsP//].
exact/rcf_satP/qf_elim_holdsP.
Qed.

Lemma SAset_nf (F : rcfType) (n : nat) (s : {SAset F^n}) :
  {P : seq ({mpoly F[n]} * seq {mpoly F[n]}) |
      s = \big[@SAsetU F n/SAset0 F n]_(p <- P)
        (SApreimset (SAmpoly (fst p)) (SAset_seq [:: 0])
        :&: \big[@SAsetI F n/SAsetT F n]_(q <- (snd p))
              SApreimset (SAmpoly q) (SAset_pos F))}.
Proof.
pose has_nf (f : {SAset F^n}) :=
  {P : seq ({mpoly F[n]} * seq {mpoly F[n]})
    | f =
    \big[SAsetU (n:=n)/SAset0 F n]_(p <- P)
      (SApreimset (SAmpoly (p.1)%PAIR) [ set 0]
        :&: \big[SAsetI (n:=n)/SAsetT F n]_(q <- (p.2)%PAIR)
              SApreimset (SAmpoly q) (SAset_pos F))}.
have IHI (f g : {SAset F^n}) :
  has_nf f -> has_nf g -> has_nf (f :&: g).
  move=> [Pf] fE [Pg] gE.
  exists ([seq ((fst pf) ^+ 2 + (fst pg) ^+ 2, (snd pf) ++ (snd pg))
    | pf <- Pf, pg <- Pg])%R.
  rewrite fE gE SAsetIbigcup/=.
  apply/eqP/SAsetP => x; rewrite !inSAset_bigcup/=.
  apply/hasP/hasP => /= -[[i j]] /allpairsP /= [[pf pg]] /= [] pfP pgP
    /pair_equal_spec [-> ->].
    rewrite !inSAsetI 2!inSApreimset !inSAset1 !SAmpolyE !inSAset_bigcap/=.
    rewrite !rowPE !forall_ord1 !mxE.
    move=> /andP[]/andP[] /eqP pf10 /allP pf20 /andP[] /eqP pg10 /allP pg20.
    exists ((fst pf) ^+ 2 + (fst pg) ^+ 2, (snd pf) ++ (snd pg))%R.
      by apply/allpairsP => /=; exists (pf, pg).
    rewrite inSAsetI inSApreimset inSAset1 SAmpolyE inSAset_bigcap/=.
    rewrite rowPE forall_ord1 !mxE mevalD !mevalXn pf10 pg10 expr0n/= addr0
      eqxx/=.
    by apply/allP => p; rewrite mem_cat => /orP [/pf20|/pg20].
  rewrite inSAsetI inSApreimset inSAset1 SAmpolyE inSAset_bigcap/= rowPE
    forall_ord1 !mxE mevalD !mevalXn paddr_eq0 ?sqr_ge0// !sqrf_eq0.
  move=> /andP[]/andP[] pf10 pg10 /allP pfg20.
  exists (pf, pg); first by apply/allpairsP => /=; exists (pf, pg).
  rewrite !inSAsetI 2!inSApreimset !SAmpolyE !inSAset1 !rowPE !forall_ord1 !mxE.
  rewrite pf10 pg10/= !inSAset_bigcap; apply/andP.
  by split; apply/allP => p pP /=; apply/pfg20; rewrite mem_cat pP// orbT.
have IHIs (I : Type) (r : seq I) (f : I -> {SAset F^n}) :
  (forall i, has_nf (f i))
  -> has_nf (\big[@SAsetI F n/SAsetT F n]_(i <- r) f i).
  move=> P; elim: r => [|i r IHr]; last by rewrite big_cons; apply/IHI.
  exists [:: (0, [::])]; rewrite big_seq1 !big_nil SAsetIT; apply/esym/eqP.
  rewrite -subTset; apply/SAset_subP => x _.
  by rewrite inSApreimset inSAset1 SAmpolyE/= meval0 rowPE forall_ord1 !mxE.
have IHC (f : {SAset F^n}) : has_nf f -> has_nf (~: f).
  move=> [P] ->; rewrite SAsetCbigcup; apply/IHIs => pf.
  rewrite SAsetCI SAsetCbigcap.
  exists ((0, [:: fst pf]) :: (0, [:: - (fst pf)]) ::
    [seq (p, [::]) | p <- snd pf] ++ [seq (0, [:: - p]) | p <- snd pf]).
  rewrite big_cons big_seq1 big_cons big_seq1/=; apply/eqP/SAsetP => x.
  rewrite !inSAsetU !inSAsetI inSAsetC 4!inSApreimset !SAmpolyE 2!inSAset1
    !rowPE !forall_ord1 !inSAset_pos !mxE meval0 eqxx/= mevalN oppr_gt0
    !inSAset_bigcup/=.
  apply/orP/orP => [[/lt_total pf10|/hasP [p pP]]|[pf10|/orP [pf10|/hasP [p]]]].
  - by apply/orP; rewrite orbCA orbA pf10.
  - rewrite inSAsetC inSApreimset inSAset_pos SAmpolyE mxE -leNgt
      le_eqVlt => /orP p0.
    right; apply/orP; right; apply/hasP; case: p0 => p0.
      exists (p, [::]).
        by rewrite mem_cat; apply/orP; left; apply/mapP; exists p.
      by rewrite big_nil SAsetIT inSApreimset SAmpolyE inSAset1 rowPE
        forall_ord1 !mxE/=.
    exists (0, [:: -p]).
      by rewrite mem_cat; apply/orP; right; apply/mapP; exists p.
    rewrite inSAsetI/= big_seq1 2!inSApreimset inSAset1 inSAset_pos !SAmpolyE.
    by rewrite rowPE forall_ord1 !mxE meval0 eqxx mevalN oppr_gt0.
  - by left; rewrite eq_sym (lt_eqF pf10).
  - by left; rewrite (lt_eqF pf10).
  rewrite mem_cat => /= /orP [|] /mapP [q]/= qf ->.
    rewrite big_nil SAsetIT inSApreimset inSAset1 SAmpolyE rowPE forall_ord1
      !mxE/= => /eqP q0.
    right; apply/hasP; exists q => //.
    by rewrite inSAsetC inSApreimset inSAset_pos SAmpolyE !mxE q0 ltxx.
  rewrite big_seq1 inSAsetI 2!inSApreimset inSAset1 inSAset_pos !SAmpolyE
    rowPE forall_ord1 !mxE/= meval0 eqxx mevalN oppr_gt0/= => q0.
  right; apply/hasP; exists q => //.
  by rewrite inSAsetC inSApreimset inSAset_pos SAmpolyE !mxE -leNgt le_eqVlt
    q0 orbT.
case: (SAset_formula s) => + [+][+] -> {s}; elim=> //=.
- move=> + _ _; case; last first.
    exists [::]; rewrite big_nil; apply/eqP/SAsetP => x.
    by rewrite inSAset0; apply/negP => /SAin_setP.
  exists [:: (0, [::])]; apply/esym/eqP.
  rewrite -subTset big_seq1 big_nil SAsetIT; apply/SAset_subP => x _.
  rewrite inSApreimset inSAset1 SAmpolyE/= meval0.
  by apply/eqP/rowP => i; rewrite !mxE.
- move=> t u /andP[] rt ru _.
  exists [:: (mpoly_rterm n (to_rterm (GRing.Add t (GRing.Opp u))), [::])].
  rewrite big_seq1/= big_nil SAsetIT; apply/eqP/SAsetP => x.
  rewrite inSApreimset SAmpolyE [RHS]inSAset1 rowPE forall_ord1 !mxE mevalB subr_eq0.
  by rewrite !meval_mpoly_rterm !evalE !eval_rterm//; apply/SAin_setP/eqP.
- move=> t u /andP[] rt ru _.
  exists [:: (0, [:: mpoly_rterm n (to_rterm (GRing.Add u (GRing.Opp t)))])].
  rewrite big_seq1/= big_seq1; apply/eqP/SAsetP => x.
  rewrite inSAsetI 2!inSApreimset !SAmpolyE [in RHS]inSAset1 rowPE forall_ord1.
  rewrite inSAset_pos !mxE meval0 eqxx/= mevalB subr_gt0 !meval_mpoly_rterm.
  by rewrite !evalE !eval_rterm//; apply/SAin_setP/idP.
- move=> t u /andP[] rt ru _.
  pose v := GRing.Add u (GRing.Opp t).
  exists [:: (mpoly_rterm n (to_rterm v), [::]);
    (0, [:: mpoly_rterm n (to_rterm v)])].
  rewrite big_cons big_nil big_seq1/= big_seq1 SAsetIT; apply/eqP/SAsetP => x.
  rewrite inSAsetU inSAsetI 3!inSApreimset !SAmpolyE 2![in RHS]inSAset1 !rowPE.
  rewrite !forall_ord1 inSAset_pos !mxE meval0 eqxx/= mevalB subr_gt0.
  rewrite subr_eq0 eq_sym -le_eqVlt !meval_mpoly_rterm !evalE !eval_rterm//.
  exact/SAin_setP/idP.
- move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg.
  move=> /andP[] {}/IHf fnf {}/IHg gnf.
  by rewrite -SAsetI_comprehension; apply/IHI.
- move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg.
  move=> /andP[] {}/IHf [Pf]fE {}/IHg [Pg]gE.
  by exists (Pf ++ Pg); rewrite big_cat/= -fE -gE SAsetU_comprehension.
- move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg.
  move=> /andP[] {}/IHf fnf {}/IHg gnf.
  suff ->: [set| f ==> g] = ~: ([set| f] :&: ~: [set| g]) :> {SAset F^n}.
    by apply/IHC/IHI => //; apply/IHC.
  apply/eqP/SAsetP => x.
  rewrite inSAsetC inSAsetI inSAsetC negb_and negbK.
  apply/SAin_setP/orP => /= [fg|[/negP xf /SAin_setP|/SAin_setP xg _]//].
  case /boolP: (x \in [set| f]) => /SAin_setP xf; last by left.
  by right; apply/SAin_setP/fg.
- by move=> f /[apply]/[apply] /IHC; rewrite SAsetC_comprehension.
Qed.

Lemma SAset_nf_1Uitv (F : rcfType) (s : {SAset F^1}) :
  {r | s = \big[@SAsetU F 1/SAset0 F 1]_(i <- r) SAset_itv i}.
Proof.
pose has_nf (f : {SAset F^1}) :=
  {r | f = \big[@SAsetU F 1/SAset0 F 1]_(i <- r) SAset_itv i}.
have has_nfU2 f g : has_nf f -> has_nf g -> has_nf (f :|: g).
  by move=> [] fi -> [] gi ->; exists (fi ++ gi); rewrite big_cat.
have has_nfU (T : Type) (r : seq T) f :
    (forall i, has_nf (f i)) ->
    has_nf (\big[@SAsetU F 1/SAset0 F 1]_(i <- r) f i).
  elim: r => [|i r IHr] fP.
    by rewrite big_nil; exists [::]; rewrite big_nil.
  by rewrite big_cons; apply/has_nfU2 => //; apply/IHr.
have has_nfI2 f g : has_nf f -> has_nf g -> has_nf (f :&: g).
  move=> [] fi -> [] gi ->; rewrite SAsetIbigcup/=.
  exists [seq let: (Interval xl xr, Interval yl yr) := x in
    Interval (Order.max xl yl) (Order.min xr yr) | x <- allpairs pair fi gi].
  rewrite big_map; apply/eq_bigr => -[] [] xl xr [] yl yr _.
  apply/eqP/SAsetP => x.
  rewrite inSAsetI !inSAset_itv !in_itv'.
  by rewrite ge_max le_min/= andbACA.
have has_nfI (T : Type) (r : seq T) f :
    (forall i, has_nf (f i)) ->
    has_nf (\big[@SAsetI F 1/SAsetT F 1]_(i <- r) f i).
  elim: r => [|i r IHr] fP; last first.
    by rewrite big_cons; apply/has_nfI2 => //; apply/IHr.
  rewrite big_nil; exists [:: `]-oo, +oo[].
  rewrite big_cons big_nil SAsetUC SAset0U.
  apply/eqP/SAsetP => x.
  by rewrite inSAsetT inSAset_itv in_itv.
case: (SAset_nf s) => + -> => nf.
have mnm0 (m : 'X_{1.. 1}):
    [multinom [tuple m (widen_ord (leqnSn 0) i)  | i < 0]] == 0%MM.
  by apply/(@eqP (_.-tuple _))/eq_from_tnth; case.
have coeffp1 (p : {mpoly F[1]}) (m : 'X_{1.. 1}) :
    p@_m = (map_poly (mcoeff 0) (muni p))`_(m ord0).
  rewrite coef_map/= muniE coef_sum.
  under eq_bigr => n _.
    rewrite coefZ coefXn mulr_natr mulrb.
    have ->: (m ord0 == n ord_max) = (n == m).
      rewrite [RHS]eq_sym; case: m => m/=; case: n => n/=.
      apply/eqP/eqP => [mn|->]; last first.
        by congr (_ _); apply/val_inj.
      suff ->: m = n by [].
      apply/eq_from_tnth; case; case=> [|//] lt01.
      have {1}->: (Ordinal lt01) = ord0 by apply/val_inj.
      by rewrite [LHS]mn; congr tnth; apply/val_inj.
    over.
  rewrite -big_mkcond/= big_pred1_seq ?msupp_uniq//.
  case/boolP: (m \in _) => mp; first by rewrite mcoeffZ mcoeffX/= mnm0 mulr1.
  by apply/eqP; rewrite mcoeff0 mcoeff_eq0.
have mevalp1 (p : {mpoly F[1]}) (x : 'I_1 -> F) :
    p.@[x] = (map_poly (mcoeff 0) (muni p)).[x ord0].
  rewrite -[x 0](mpolyCK 0) horner_map/= muniE horner_sum.
  rewrite raddf_sum {1}(mpolyE p) raddf_sum/=.
  apply/eq_bigr => m _.
  rewrite mevalZ mevalX big_ord_recl big_ord0 mulr1.
  rewrite hornerZ hornerXn -rmorphXn/= [in RHS]mulrC mcoeffCM.
  rewrite mcoeffZ mcoeffX mnm0 mulr1 mulrC.
  by congr (_ ^+ (m _) * _); apply/val_inj.
apply/has_nfU => -[/=] p r; apply/has_nfI2.
  have [->|p0] := eqVneq p 0.
    exists [:: `]-oo, +oo[].
    apply/eqP/SAsetP => x.
    rewrite inSApreimset inSAset1 SAmpolyE rowPE forall_ord1 !mxE.
    rewrite meval0 big_cons big_nil SAsetUC SAset0U inSAset_itv in_itv/=.
    by rewrite eqxx.
  exists [seq `[x, x] | x <- rootsR (map_poly (mcoeff 0) (muni p))].
  apply/eqP/SAsetP => x.
  rewrite inSApreimset inSAset1 SAmpolyE rowPE forall_ord1 !mxE.
  rewrite inSAset_bigcup has_map/= /preim/=.
  under eq_has => y/=.
    rewrite inSAset_itv in_itv/=.
    have ->: (y <= x 0 0 <= y) = (y == x 0 0).
      by apply/idP/eqP => [/le_anti //| ->]; rewrite lexx.
    over.
  rewrite has_pred1 in_rootsR.
  suff -> /=: map_poly (mcoeff 0) (muni p) != 0.
    by rewrite rootE mevalp1.
  move: p0; apply/contraNN => /eqP/polyP p0.
  by apply/eqP/mpolyP => m; rewrite mcoeff0 coeffp1 p0 coef0.
apply/has_nfI => {nf r}p.
pose q := (map_poly (mcoeff 0) (muni p)).
move rE: (rootsR q) => r.
case: r rE => [|x r] rE.
  case/boolP: (0 < lead_coef q) => [|/negP] p0.
    exists [:: `]-oo, +oo[]; rewrite big_seq1.
    apply/eqP/SAsetP => x.
    rewrite inSApreimset inSAset_pos SAmpolyE mxE inSAset_itv in_itv/=.
    by rewrite -sgz_gt0 mevalp1 sgz_horner rE/= big_nil expr0 !mulr1 sgz_gt0.
  exists [::]; rewrite big_nil.
  apply/eqP; rewrite -subset0; apply/SAset_subP => x.
  rewrite inSApreimset inSAset_pos SAmpolyE mxE inSAset0.
  by rewrite -sgz_gt0 mevalp1 sgz_horner rE/= big_nil expr0 !mulr1 sgz_gt0.
move id_natE: (@id nat) => id_nat.
exists (
(if (0 < lead_coef q) (+) odd (\sum_(y0 <- rootsR q) \mu_y0 q) then
    cons `]-oo, x[ else id)
    ((if 0 < lead_coef q then
      cons `]last x r, +oo[ else id)
      [seq `](x :: r)`_i, r`_i[ |
          i <- iota 0 (size r) & sgz q.[((x :: r)`_i + r`_i) / 2] == 1])).
apply/eqP/SAsetP => y.
rewrite inSApreimset inSAset_pos SAmpolyE mxE inSAset_bigcup.
move: rE; have [->|q0 rE] := eqVneq q 0.
  by rewrite rootsR0.
rewrite mevalp1 -/q.
have /(pairwiseP 0) xr_sort: pairwise <%O (x :: r).
  by rewrite -lt_sorted_pairwise -rE; exact/sorted_roots.
have xr_sort':
    {in gtn (size (x :: r)) &,
      {homo nth 0 (x :: r) : i j / (i <= j)%N >-> i <= j}}.
  move=> i j ilt jlt.
  rewrite leq_eqVlt => /orP[/eqP ->|ij]; first exact/lexx.
  exact/ltW/xr_sort.
case /boolP: (root q (y 0 0)) => qy0 /=.
  rewrite -sgz_gt0 sgz_horner in_rootsR q0/= qy0.
  rewrite mulr0 mul0r ltxx; apply/esym/negP => /hasP[/=] I IE yI.
  have: y 0 0 \in x :: r by rewrite -rE in_rootsR q0.
  move=> /(nthP 0)[/=] i ir yE.
  move: yI; have [->|Ix] := eqVneq I `]-oo, x[.
    rewrite inSAset_itv in_itv/= -yE.
    case: (posnP i) => [->|i0]; first by rewrite ltxx.
    rewrite ltNge ltW//.
    by move: (xr_sort 0 i); rewrite inE ltn0Sn inE ir; apply.
  move: IE; rewrite if_arg 2!fun_if in_cons (negPf Ix)/= if_same.
  have [-> _|Ir] := eqVneq I `]last x r, +oo[.
    rewrite inSAset_itv in_itv/= andbT (last_nth 0) -yE.
    move: (xr_sort' i (size r)); rewrite !inE => /(_ ir (leqnn _)).
    rewrite -ltnS => /(_ ir) => {}ir.
    by move=> /(le_lt_trans ir); rewrite ltxx.
  rewrite if_arg 2!fun_if in_cons (negPf Ir)/= if_same.
  move=> /mapP[/=] n; rewrite mem_filter mem_iota/=.
  move=> /andP[_] nr ->.
  rewrite inSAset_itv in_itv/= -yE => /andP[] nlt ilt.
  case: (ltnP i n) => [iltn|].
    move: (xr_sort i n); rewrite !inE/= [(n < _)%N]ltnS.
    move=> /(_ ir (ltnW nr) iltn).
    by rewrite ltNge ltW.
  rewrite leq_eqVlt => /orP[/eqP nE|ni].
    by rewrite nE ltxx in nlt.
  move: xr_sort' => /(_ n.+1 i).
  by rewrite !inE/= ltnS => /(_ nr ir ni) /(lt_le_trans ilt); rewrite ltxx.
apply/idP/idP => [q0'|]; last first.
  move=> /hasP[] I.
  have [->|Ix] := eqVneq I `]-oo, x[.
    case/boolP: ((0 < lead_coef q) (+) odd (\sum_(y0 <- rootsR q) \mu_y0 q))
        => [q0'|] _; last first.
      case: (0 < lead_coef q); last by move=> /mapP[].
      by rewrite in_cons/= => /mapP[].
    rewrite inSAset_itv in_itv/= => yx.
    rewrite -sgz_gt0 sgz_horner in_rootsR (negPf qy0) andbF/= mulr1.
    rewrite big_mkcond big_seq -big_mkcondr/=.
    under eq_bigl => z.
      have ->: (z \in rootsR q) && (y 0 0 < z) = (z \in rootsR q).
        case/boolP: (z \in rootsR q) => [/=|//].
        rewrite rE => /(nthP 0)[] i iq <-.
        move: (xr_sort 0 i).
        rewrite !inE => /(_ (leq_trans (ltn0Sn _) iq) iq).
        by case: i {iq} => [//|i] /(_ isT)/(lt_trans yx).
      over.
    rewrite -big_seq -signr_odd; case: (odd _) q0'; last first.
      by rewrite addbF expr0 mulr1 sgz_gt0.
    rewrite addbT expr1 mulrN1 oppr_gt0 -leNgt le_eqVlt.
    by rewrite lead_coef_eq0 (negPf q0)/= sgz_lt0.
  have [->|Ir] := eqVneq I `]last x r, +oo[.
    case/boolP: (0 < lead_coef q) => [q0'|] _; last first.
      case: (odd _) => /=; last by move=> /mapP[].
      by rewrite in_cons/= => /mapP[].
    rewrite inSAset_itv in_itv/= andbT => ry.
    rewrite -sgz_gt0 sgz_horner in_rootsR (negPf qy0) andbF/= mulr1.
    rewrite big_mkcond big_seq -big_mkcondr/=.
    under eq_bigl => z.
      have ->: (z \in rootsR q) && (y 0 0 < z) = false.
        apply/negP => /andP[]; rewrite rE => /(nthP 0)[] i ir <-.
        move: (xr_sort i (size r)); rewrite !inE => /(_ ir (leqnn _)).
        move: ir; rewrite /= ltnS leq_eqVlt => /orP[/eqP -> _|].
          by rewrite nth_last/= => /(lt_trans ry); rewrite ltxx.
        move=> /[swap]/[apply]; rewrite nth_last/= => ir /(lt_trans ry).
        by move=> /(lt_trans ir); rewrite ltxx.
      over.
    by rewrite big_pred0// expr0 mulr1 sgz_gt0.
  rewrite 2!if_arg 2!fun_if in_cons (negPf Ix)/= 3!fun_if in_cons (negPf Ir)/=.
  rewrite 2!if_same => /mapP[]/= i; rewrite mem_filter sgz_cp0 mem_iota/=.
  move=> /andP[] q0' ilt ->.
  rewrite inSAset_itv in_itv/= => /andP[] iy yi.
  move: q0'; rewrite -sgz_gt0 -[X in _ -> _ X]sgz_gt0 !sgz_horner.
  congr (_ < _ * Posz (_ _) * _ ^+ _).
    rewrite [in RHS]in_rootsR (negPf qy0) andbF/= rE; apply/negP.
    move=> /(nthP 0)[] j jq ji.
    case: (ltnP i j) => ij.
      move: (xr_sort' i.+1 j); rewrite !inE/= ltnS => /(_ ilt jq ij).
      rewrite ji ler_pdivlMr// mulr_natr mulr2n -subr_ge0 addrKA subr_ge0.
      rewrite leNgt => /negP; apply.
      apply/(xr_sort i i.+1) => //.
      by rewrite inE/= ltnS; apply/ltnW.
    move: (xr_sort' j i).
    rewrite !inE/= [(i < _)%N]ltnS => /(_ jq (ltnW ilt) ij).
    rewrite ji ler_pdivrMr// mulr_natr mulr2n -subr_ge0 addrKA subr_ge0.
    rewrite leNgt => /negP; apply.
    apply/(xr_sort i i.+1) => //.
    by rewrite inE/= ltnS; apply/ltnW.
  rewrite big_mkcond big_seq -big_mkcondr [in RHS]big_mkcond [in RHS]big_seq.
  rewrite -big_mkcondr/=.
  apply/eq_bigl => z; case/boolP: (z \in rootsR q) => // /(nthP 0)[] j.
  rewrite rE => jlt <- /=.
  rewrite ltr_pdivrMr// mulr_natr mulr2n.
  case: (ltnP i j) => ij.
    move: (xr_sort' i.+1 j); rewrite !inE/= ltnS => /(_ ilt jlt ij) rij.
    rewrite (lt_le_trans yi rij); apply/ltr_leD => //.
    exact/(lt_le_trans _ rij)/(lt_trans iy).
  move: (xr_sort' j i).
  rewrite !inE/= [(i < _)%N]ltnS => /(_ jlt (ltnW ilt) ij) rji.
  rewrite [RHS]ltNge (ltW (le_lt_trans rji iy))/=; apply/negP/negP.
  rewrite -leNgt; apply/lerD => //.
  exact/(le_trans rji)/ltW/(lt_trans iy).
rewrite 2!if_arg 2!fun_if/= inSAset_itv in_itv/=.
case: (ltP (y 0 0) x) => yx /=.
  move: q0'; rewrite -sgz_gt0 sgz_horner in_rootsR (negPf qy0) andbF/= mulr1.
  rewrite big_mkcond big_seq -big_mkcondr/=.
  under eq_bigl => z.
    have ->: (z \in rootsR q) && (y 0 0 < z) = (z \in rootsR q).
      case/boolP: (z \in rootsR q) => [/=|//].
      rewrite rE => /(nthP 0)[] i iq <-.
      move: (xr_sort 0 i).
      rewrite !inE => /(_ (leq_trans (ltn0Sn _) iq) iq).
      by case: i {iq} => [//|i] /(_ isT)/(lt_trans yx).
    over.
  rewrite -big_seq -signr_odd; case: (odd _); last first.
    by rewrite expr0 mulr1 sgz_gt0 => ->.
  rewrite expr1 mulrN1 oppr_gt0 sgz_lt0 addbT -leNgt.
  by rewrite le_eqVlt lead_coef_eq0 (negPf q0) => ->.
rewrite if_same fun_if/= inSAset_itv in_itv/= andbT.
case: (ltP (last x r) (y 0 0)) => ry.
  move: q0'; rewrite -sgz_gt0 sgz_horner in_rootsR (negPf qy0) andbF/= mulr1.
  rewrite big_mkcond big_seq -big_mkcondr/=.
  under eq_bigl => z.
    have ->: (z \in rootsR q) && (y 0 0 < z) = false.
      apply/negP => /andP[]; rewrite rE => /(nthP 0)[] i ir <-.
      move: (xr_sort i (size r)); rewrite !inE => /(_ ir (leqnn _)).
      move: ir; rewrite /= ltnS leq_eqVlt => /orP[/eqP -> _|].
        by rewrite nth_last/= => /(lt_trans ry); rewrite ltxx.
      move=> /[swap]/[apply]; rewrite nth_last/= => ir /(lt_trans ry).
      by move=> /(lt_trans ir); rewrite ltxx.
    over.
  by rewrite big_pred0// expr0 mulr1 sgz_gt0 => ->.
rewrite if_same has_map; apply/hasP => /=.
move: yx; rewrite le_eqVlt => /orP[/eqP|] xy.
  by move: (mem_head x r); rewrite -rE in_rootsR xy (negPf qy0) andbF.
move: ry; rewrite le_eqVlt => /orP[/eqP|] ry.
  by move: (mem_last x r); rewrite -rE in_rootsR -ry (negPf qy0) andbF.
case: (@arg_maxnP 'I_(size r).+1 0 (fun i => (x :: r)`_i < y 0 0) val xy).
move=> j jy/= yj.
move: (ltn_ord j); rewrite ltnS leq_eqVlt => /orP[/eqP|] jr.
  by move: jy; rewrite jr -last_nth => /(lt_trans ry); rewrite ltxx.
exists j; last first.
  rewrite inSAset_itv in_itv/= jy/= ltNge le_eqVlt.
  apply/negP => /orP[/eqP|] yr; last first.
    by rewrite -ltnS in jr; move: (yj (Ordinal jr) yr); rewrite ltnn.
  have /=: (x :: r)`_j.+1 \in x :: r by apply/mem_nth; rewrite ltnS.
  by rewrite yr -rE in_rootsR (negPf qy0) andbF.
rewrite mem_filter mem_iota/= jr andbT sgz_cp0.
move: q0'; rewrite -sgz_gt0 -[X in _ X -> _]sgz_gt0 !sgz_horner.
congr (_ < _ * Posz (_ _) * _ ^+ _).
  rewrite in_rootsR (negPf qy0) andbF/= rE; apply/esym/negP.
  move=> /(nthP 0)[] k kq kj.
  case: (ltnP j k) => jk.
    move: (xr_sort' j.+1 k); rewrite !inE/= ltnS => /(_ jr kq jk).
    rewrite kj ler_pdivlMr// mulr_natr mulr2n -subr_ge0 addrKA subr_ge0.
    rewrite leNgt => /negP; apply.
    apply/(xr_sort j j.+1) => //.
    by rewrite inE/= ltnS; apply/ltnW.
  move: (xr_sort' k j); rewrite !inE/= => /(_ kq (ltn_ord j) jk).
  rewrite kj ler_pdivrMr// mulr_natr mulr2n -subr_ge0 addrKA subr_ge0.
  rewrite leNgt => /negP; apply.
  apply/(xr_sort j j.+1) => //.
  by rewrite inE/= ltnS; apply/ltnW.
rewrite big_mkcond big_seq -big_mkcondr [in RHS]big_mkcond [in RHS]big_seq.
rewrite -big_mkcondr/=.
apply/eq_bigl => z; case/boolP: (z \in rootsR q) => // /(nthP 0)[] k.
rewrite rE => klt <- /=.
rewrite ltr_pdivrMr// mulr_natr mulr2n.
case: (ltnP j k) => jk.
  rewrite -ltnS in jr.
  move: (xr_sort' j.+1 k); rewrite !inE/= => /(_ jr klt jk) rjk.
  move: (yj (Ordinal klt)) => /implyP; rewrite -implybNN -ltnNge jk/= -leNgt.
  rewrite le_eqVlt => /orP[/eqP jE|yk].
    by move: (mem_nth 0 klt); rewrite -jE -rE in_rootsR (negPf qy0) andbF.
  rewrite yk; apply/esym/ltr_leD; first by apply/xr_sort => //; rewrite inE.
  by rewrite -[r`_j]/((x :: r)`_j.+1); apply/xr_sort'.
move: (xr_sort' k j).
rewrite !inE/= [(j < _)%N]ltnS => /(_ klt (ltnW jr) jk) rjk.
rewrite ltNge (ltW (le_lt_trans rjk jy))/=; apply/esym/negP/negP.
rewrite -leNgt; apply/lerD => //.
apply/(le_trans rjk)/ltW/(lt_trans jy).
rewrite -ltnS in jr.
move: (yj (Ordinal jr)) => /implyP; rewrite -implybNN ltnn/= -leNgt.
rewrite le_eqVlt => /orP[/eqP yE|//].
have /=: (x :: r)`_j.+1 \in x :: r by exact/mem_nth.
by rewrite -yE -rE in_rootsR (negPf qy0) andbF.
Qed.

Section SAorder.
Variables (F : rcfType) (n : nat).
Implicit Types (s : {SAset F^n}).

Definition SAsetUB (s : {SAset F^1}) : {SAset F^1} :=
  [set | 'forall 'X_1, (subst_formula [:: 1%N] s ==> ('X_1 <=% 'X_0))%oT].

Lemma inSAsetUB (s : {SAset F^1}) (x : 'rV[F]_1) :
  reflect (forall y, y \in s -> y ord0 ord0 <= x ord0 ord0) (x \in SAsetUB s).
Proof.
apply/(iffP (SAin_setP _ _)) => /= [+ y ys|yx y].
move=> /(_ (y ord0 ord0)); rewrite holds_subst/= !nth_set_nth/= enum_ordSl/=.
apply; move: ys => /rcf_satP; congr holds => /=.
by rewrite enum_ordSl enum_ord0.
rewrite holds_subst/= !nth_set_nth/= enum_ordSl/= => ys.
move: yx => /(_ (\row__ y)); rewrite inE/= mxE; apply.
by rewrite enum_ordSl enum_ord0/= mxE; apply/rcf_satP.
Qed.

Lemma inSAsetUBC (s : {SAset F^1}) (x : 'rV[F]_1) :
  reflect (exists y, y \in s /\ x ord0 ord0 < y ord0 ord0) (x \in ~: SAsetUB s).
Proof.
rewrite SAsetC_comprehension.
apply/(iffP (SAin_setP _ _)) => [/n_forall_formula /= [y]|[y][ys] xy].
rewrite holds_subst/= !nth_set_nth/= enum_ordSl/= => yP.
exists (\row__ y); case/boolP: (\row__ y \in s) => [|/negP ys].
  by move=> /rcf_satP => ys; split=> //; rewrite mxE ltNge; apply/negP => xy.
exfalso; apply/yP => /rcf_satP => ys'; exfalso; apply/ys; move: ys'.
by congr rcf_sat; rewrite /= enum_ordSl enum_ord0/= mxE.
apply/n_forall_formula; exists (y ord0 ord0).
rewrite /= holds_subst/= !nth_set_nth/= enum_ordSl/= => yP.
move: xy; rewrite ltNge => /negP; apply; apply/yP.
move: ys => /rcf_satP; congr holds.
by rewrite /= enum_ordSl enum_ord0/=.
Qed.

Lemma SAsetUB0 : SAsetUB (SAset0 F 1) = SAsetT F 1.
Proof.
apply/eqP; rewrite -subTset; apply/SAset_subP => x _.
by apply/inSAsetUB => y; rewrite inSAset0.
Qed.

Lemma SAsetUBT : SAsetUB (SAsetT F 1) = SAset0 F 1.
Proof.
apply/eqP; rewrite -subset0; apply/SAset_subP.
move=> x /inSAsetUB/(_ (x+\row__ 1)%R); rewrite inSAsetT => /(_ isT).
by rewrite !mxE -subr_ge0 opprD addrA subrr add0r leNgt oppr_lt0 ltr01.
Qed.

Lemma SAsetUBU (s t : {SAset F^1}) :
  SAsetUB (s :|: t) = SAsetUB s :&: SAsetUB t.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetI.
apply/inSAsetUB/andP => [xst|[] /inSAsetUB xs/inSAsetUB xt y]; last first.
by rewrite inSAsetU => /orP [/xs|/xt].
by split; apply/inSAsetUB => y yst; apply/xst; rewrite inSAsetU yst// orbT.
Qed.

Lemma SAsetUBbigcup (I : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^1}) :
  SAsetUB (\big[@SAsetU F 1/SAset0 F 1]_(i <- r | P i) f i)
  = \big[@SAsetI F 1/SAsetT F 1]_(i <- r | P i) (SAsetUB (f i)).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil SAsetUB0.
by rewrite !big_cons; case: (P i) => //; rewrite SAsetUBU IHr.
Qed.

Definition SAsetLB (s : {SAset F^1}) : {SAset F^1} :=
  [set | 'forall 'X_1, (subst_formula [:: 1%N] s ==> ('X_0 <=% 'X_1))%oT].

Lemma inSAsetLB (s : {SAset F^1}) (x : 'rV[F]_1) :
  reflect (forall y, y \in s -> x ord0 ord0 <= y ord0 ord0) (x \in SAsetLB s).
Proof.
apply/(iffP (SAin_setP _ _)) => /= [+ y ys|yx y].
  move=> /(_ (y ord0 ord0)); rewrite holds_subst/= !nth_set_nth/= enum_ordSl/=.
  apply; move: ys => /rcf_satP; congr holds => /=.
  by rewrite enum_ordSl enum_ord0.
rewrite holds_subst/= !nth_set_nth/= enum_ordSl/= => ys.
move: yx => /(_ (\row__ y)); rewrite inE/= mxE; apply.
by rewrite enum_ordSl enum_ord0/= mxE; apply/rcf_satP.
Qed.

Lemma inSAsetLBC (s : {SAset F^1}) (x : 'rV[F]_1) :
  reflect (exists y, y \in s /\ y ord0 ord0 < x ord0 ord0) (x \in ~: SAsetLB s).
Proof.
rewrite SAsetC_comprehension.
apply/(iffP (SAin_setP _ _)) => [/n_forall_formula /= [y]|[y][ys] xy].
  rewrite holds_subst/= !nth_set_nth/= enum_ordSl/= => yP.
  exists (\row__ y); case/boolP: (\row__ y \in s) => [|/negP ys].
    by move=> /rcf_satP => ys; split=> //; rewrite mxE ltNge; apply/negP => xy.
  exfalso; apply/yP => /rcf_satP => ys'; exfalso; apply/ys; move: ys'.
  by congr rcf_sat; rewrite /= enum_ordSl enum_ord0/= mxE.
apply/n_forall_formula; exists (y ord0 ord0).
rewrite /= holds_subst/= !nth_set_nth/= enum_ordSl/= => yP.
move: xy; rewrite ltNge => /negP; apply; apply/yP.
move: ys => /rcf_satP; congr holds.
by rewrite /= enum_ordSl enum_ord0/=.
Qed.

Lemma SAsetLB0 : SAsetLB (SAset0 F 1) = SAsetT F 1.
Proof.
apply/eqP; rewrite -subTset; apply/SAset_subP => x _.
by apply/inSAsetLB => y; rewrite inSAset0.
Qed.

Lemma SAsetLBT : SAsetLB (SAsetT F 1) = SAset0 F 1.
Proof.
apply/eqP; rewrite -subset0; apply/SAset_subP.
move=> x /inSAsetLB/(_ (x-\row__ 1)%R); rewrite inSAsetT => /(_ isT).
by rewrite !mxE -subr_ge0 addrAC subrr add0r leNgt oppr_lt0 ltr01.
Qed.

Lemma SAsetLBU (s t : {SAset F^1}) :
  SAsetLB (s :|: t) = SAsetLB s :&: SAsetLB t.
Proof.
apply/eqP/SAsetP => x; rewrite inSAsetI.
apply/inSAsetLB/andP => [xst|[] /inSAsetLB xs/inSAsetLB xt y]; last first.
  by rewrite inSAsetU => /orP [/xs|/xt].
by split; apply/inSAsetLB => y yst; apply/xst; rewrite inSAsetU yst// orbT.
Qed.

Lemma SAsetLBbigcup (I : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^1}) :
  SAsetLB (\big[@SAsetU F 1/SAset0 F 1]_(i <- r | P i) f i)
      = \big[@SAsetI F 1/SAsetT F 1]_(i <- r | P i) (SAsetLB (f i)).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil SAsetLB0.
by rewrite !big_cons; case: (P i) => //; rewrite SAsetLBU IHr.
Qed.

Lemma SAset_supP (s : {SAset F^1}) :
  s != SAset0 F 1 -> SAsetUB s != SAset0 F 1
  -> {x : F | SAsetUB s = SAset_itv `[x, +oo[%R}.
Proof.
pose Goal (t : {SAset F^1}) := t != SAset0 F 1 ->
  SAsetUB t != SAset0 F 1 ->
  {x : F | SAsetUB t = SAset_itv `[x, +oo[%R}.
have supU : forall s t : {SAset F^1}, Goal s -> Goal t -> Goal (s :|: t).
  move=> {}s t; rewrite /Goal.
  have [-> _|s0 /(_ isT)] := eqVneq s (SAset0 F 1); first by rewrite SAset0U.
  have [-> + _|t0 + /(_ isT)] := eqVneq t (SAset0 F 1).
    by rewrite SAsetUC SAset0U.
  rewrite SAsetUBU.
  have [-> _ _ _|_ /(_ isT) []sm ->] := eqVneq (SAsetUB s) (SAset0 F 1).
    by rewrite SAset0I eqxx.
  have [-> _ _|_ /(_ isT) []tm -> _ _] := eqVneq (SAsetUB t) (SAset0 F 1).
    by rewrite SAsetI0 eqxx.
  exists (maxr sm tm).
  apply/eqP/SAsetP => x.
  by rewrite inSAsetI !inSAset_itv !in_itv/= ge_max !andbT.
have {}supU (I : Type) (r : seq I) (f : I -> {SAset F^1}) :
  (forall i, Goal (f i)) -> Goal (\big[@SAsetU F 1/SAset0 F 1]_(i <- r) f i).
  move=> iub; elim: r => [|i r IHr]; first by rewrite big_nil /Goal eqxx.
  by rewrite big_cons; apply/supU.
rewrite -/(Goal s); case: (SAset_nf_1Uitv s) => r ->.
apply/supU => I; rewrite /Goal.
case: (set0Vmem (SAset_itv I)) => [-> /[!eqxx]//|[]] x + _.
case: I => l; case=> [br xr|br] xI; last first.
  move=> /negP; elim; apply/SAsetP => y.
  rewrite inSAset0; apply/negP => /inSAsetUB.
  move=> /(_ (\row__ maxr (x 0 0) (y 0 0) + 1)).
  move: xI; rewrite !inSAset_itv !in_itv'/= !mxE eqxx/= => /andP[].
  case: br => // lx _.
  have ->: (l <= BLeft (maxr (x 0 0) (y 0 0) + 1))%O.
    apply/(le_trans lx).
    suff: x 0 0 <= maxr (x 0 0) (y 0 0) + 1 by [].
    rewrite -subr_ge0 -addrA -opprB subr_ge0 le_max -subr_ge0.
    by rewrite opprB addrCA subrr addr0 ler01.
  move=> /(_ isT); rewrite leNgt => /negP; apply.
  rewrite -subr_gt0 -addrA -opprB subr_gt0 lt_max.
  apply/orP; right.
  by rewrite -subr_gt0 opprB addrCA subrr addr0 ltr01.
move=> _; exists xr.
apply/eqP/SAsetP => y.
rewrite inSAset_itv in_itv/= andbT.
case: (ltP (y 0 0) xr) => yx.
  apply/negP => /inSAsetUB/(_ (\row__ (((maxr (y 0 0) (x 0 0)) + xr) / 2))).
  move: xI; rewrite !inSAset_itv !itv_boundlr => /andP[] lx xxr.
  rewrite mxE.
  have ->: (l <= BLeft ((maxr (y 0 0) (x 0 0) + xr) / 2))%O.
    apply/(le_trans lx).
    suff: (x 0 0 <= ((maxr (y 0 0) (x 0 0) + xr) / 2)) by [].
    rewrite ler_pdivlMr// mulr_natr mulr2n; apply/lerD.
      by rewrite le_max lexx orbT.
    by move: xxr; case: br => // /ltW.
  have -> /=: (BRight ((maxr (y 0 0) (x 0 0) + xr) / 2) <= BSide br xr)%O.
    move: xxr; rewrite !leBSide.
    case: br => /= xxr.
      rewrite ltr_pdivrMr// mulr_natr mulr2n; apply/ltr_leD; last exact/lexx.
      by rewrite gt_max yx.
    rewrite ler_pdivrMr// mulr_natr mulr2n; apply/lerD; last exact/lexx.
    by rewrite ge_max (ltW yx).
  move=> /(_ isT).
  rewrite ler_pdivrMr// mulr_natr mulr2n leNgt => /negP; apply.
  by apply/ler_ltD => //; rewrite le_max lexx.
apply/inSAsetUB => z.
rewrite inSAset_itv itv_boundlr => /andP[_].
rewrite leBSide => /lteifW zx.
exact/(le_trans zx yx).
Qed.

End SAorder. 

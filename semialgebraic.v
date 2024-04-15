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
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun generic_quotient bigop finset perm.
From mathcomp Require Import ssralg poly polydiv ssrnum mxpoly binomial interval finalg.
From mathcomp Require Import zmodp mxpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order finset classical_sets topology.

From SemiAlgebraic Require Import auxresults formula.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope quotient_scope.
Local Open Scope type_scope.
Local Open Scope classical_set_scope.

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
(row_mx t u) ord0 i = if (i < m)%N then nth x0 (ngraph t) i else nth x0 (ngraph u) (i - m).
Proof.
by rewrite mxE; case: splitP => j ->; rewrite ?(addnC, addnK) nth_ngraph.
Qed.

Fact ngraph_cat (m : nat) (t : 'rV[F]_m) (p : nat) (u : 'rV[F]_p) :
    ngraph (row_mx t u) = ngraph t ++ ngraph u :> seq F.
Proof.
case: m t => [|m] t.
  by rewrite row_thin_mx ngraph_nil.
apply: (@eq_from_nth _ (t ord0 ord0)) => [|i]; first by rewrite size_cat ?size_ngraph.
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

Lemma equivf_sym : symmetric equivf.
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

Definition set_of_SAset (s : {SAset F^n}) := [set x | x \in s].
Coercion set_of_SAset : SAtype_of >-> set.

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
have [lt_in|leq_ni] := ltnP i n; last first.
+ split=> [[x]|].
  - move/holds_fsubst.
    rewrite fsubst_id; last
      by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
    move=> holds_uf; exists x; apply/holds_fsubst.
    rewrite fsubst_id; last
      by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
    by move: holds_uf; move/(_ u) : h; rewrite cat0s /=; move => [].
  - move=> [x]; rewrite set_nth_over ?size_tuple // rcons_cat /=.
    move/holds_take; rewrite take_size_cat ?size_tuple // => holds_ug.
    exists 0; rewrite set_nth_nrcons ?size_tuple // rcons_nrcons -nseq_cat.
    by apply/holds_cat_nseq; move: holds_ug; move/(_ u) : h => [].
+ split.
  - move=> [x hxf]; exists x; move: hxf.
    move/(_ [tuple of (set_nth 0 u (Ordinal lt_in) x)]) : h.
    by rewrite cat0s /=; move=> [].
  - move=> [x hxf]; exists x; move: hxf.
    move/(_ [tuple of (set_nth 0 u (Ordinal lt_in) x)]) : h.
    by rewrite cat0s /=; move=> [].
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

Section Projection.

Variables (F : rcfType) (n : nat) (i : 'I_n).

Definition ex_proj (f : {formula_n F}) : {formula_n F} := ('exists 'X_i, f)%oT.

Definition SA_ex_proj := (lift_op1 {SAset F^n} ex_proj).

Lemma ex_proj_idem (s : {SAset F^n}) :
    SA_ex_proj (SA_ex_proj s) = SA_ex_proj s.
Proof.
move: s; apply: quotP => f eq_repr_pi_f.
rewrite /SA_ex_proj; unlock.
apply/eqP; rewrite eqmodE eq_repr_pi_f.
apply/rcf_satP/nforallP => u.
rewrite cat0s; split.
+ move=> [y hxy]; move/holds_repr_pi : hxy => [x hxy].
  by exists x; move: hxy; rewrite set_set_nth eqxx.
+ move=> [y hxy]; exists y; apply/holds_repr_pi.
  by exists y; rewrite set_set_nth eqxx.
Qed.

Definition all_proj (f : {formula_n F}) : {formula_n F} := ('forall 'X_i, f)%oT.

Definition SA_all_proj := (lift_op1 {SAset F^n} all_proj).

Lemma all_proj_idem (s : {SAset F^n}) :
    SA_all_proj (SA_all_proj s) = (SA_all_proj s).
Proof.
move : s; apply : quotP => f hf.
rewrite /SA_all_proj; unlock.
apply/eqP; rewrite eqmodE hf.
apply/rcf_satP/nforallP => u; rewrite cat0s.
split=> h x.
+ by move/(_ x)/holds_repr_pi/(_ x) : h; rewrite set_set_nth eqxx.
+ apply/holds_repr_pi => y; rewrite set_set_nth eqxx.
  by move/(_ y) : h.
Qed.

End Projection.

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

Definition SAset_pos (F : rcfType) : {SAset F^1} := [set | (0 <% 'X_0)%oT].

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

HB.instance Definition _ := Monoid.isComLaw.Build {SAset F^n} (SAset0 F n) (@SAsetU F n) SAsetUA SAsetUC SAset0U.

Lemma SAsetIC A B : A :&: B = B :&: A.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetI andbC. Qed.

Lemma SAsetIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/eqP/SAsetP => x; rewrite !inSAsetI andbA. Qed.

Lemma SAsetCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetI !inSAsetC inSAsetU negb_or.
Qed.

Lemma SAsetCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof.
by apply/eqP/SAsetP => x; rewrite inSAsetU !inSAsetC inSAsetI negb_and.
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

Lemma SAsubsetIl A B : A :&: B :<=: A.
Proof. by apply/SAset_subP => x; rewrite inSAsetI => /andP[]. Qed.

Lemma SAsubsetIidl A B : (A :<=: A :&: B) = (A :<=: B).
Proof.
apply/SAset_subP/SAset_subP => AB x /[dup] xA /AB; rewrite inSAsetI.
  by move=> /andP[].
by rewrite xA.
Qed.

Lemma SAsubsetEI A B : A :<=: B = (A :&: B == A).
Proof. by rewrite eqEsubset SAsubsetIl SAsubsetIidl. Qed.

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

Lemma SAsetIT A : A :&: SAsetT F n = A.
Proof. by apply/eqP/SAsetP => x; rewrite inSAsetI inSAsetT andbT. Qed.

Lemma SAsetUID A B : A :&: B :|: A :\: B = A.
Proof. by rewrite -SAsetIUr SAsetUCr SAsetIT. Qed.

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
  SAset_cast k A = [set | A /\ \big[And/True]_(i <- iota m (k - m)) ('X_i == 0)].
Proof.
rewrite -subn_eq0 => /eqP km; apply/eqP/SAsetP => x.
apply/Bool.eq_iff_eq_true.
rewrite [X in X <-> _](iff_sym (rwP (SAin_setP _ _))).
rewrite [X in _ <-> X](iff_sym (rwP (SAin_setP _ _))).
rewrite km nquantify0/=.
by split=> -[].
Qed.

Lemma inSAset_castDn m k (A : {SAset F^(m+k)}) (x : 'rV[F]_m) :
  reflect (exists y : 'rV[F]_(m+k), y \in A /\ x = lsubmx y) (x \in SAset_cast m A).
Proof.
rewrite SAset_cast_le ?leq_addr// subDnCA// subnn addn0 -[X in nquantify X](size_ngraph x).
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
apply/SAin_setP/andP => /=; rewrite -holds_take take_ngraph holdsAnd /= => -[/rcf_satP hx].
  move=> h0; split=> //; apply/eqP/rowP => i.
  move/(_ (@unsplit m k (inr i))): h0; rewrite nth_ngraph mem_iota subnKC ?leq_addr//= -addnS leq_add// => /(_ Logic.eq_refl Logic.eq_refl).
  by rewrite !mxE.
move=> /eqP /rowP x0; split=> // => i; rewrite mem_iota subnKC ?leq_addr// => /andP[mi im] _.
rewrite (nth_ngraph _ _ (Ordinal im)) -(splitK (Ordinal im)).
move: mi; rewrite leqNgt -{1}[i]/(Ordinal im : nat).
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
    apply/andP/SAin_setP => /=; rewrite holdsAnd -holds_take -(take_takel _ (@leq_addr (m-n) n)%N) !take_ngraph !row_mxKl (rwP (rcf_satP _ _)) subDnCA ?leq_addr// subDnCA// subnn addn0 addnC.
      move=> [] /andP[] llA /eqP -> /eqP ->; split=> //= i.
      rewrite mem_iota addnA => /andP[+ ilt] _.
      rewrite -[i]/(Ordinal ilt : nat) nth_ngraph mxE.
      case: (splitP (Ordinal ilt)) => j ->; rewrite mxE//.
      by case: (splitP j) => j' ->; rewrite leqNgt ?ltn_ord// mxE.
    move=> [llA /= h0]; split; last first.
      apply/eqP/rowP => i.
      move/(_ (unsplit (inr i) : 'I_(n + (m - n) + (k - m))%N)): h0.
      rewrite nth_ngraph !mxE unsplitK.
      by rewrite mem_iota addnA ltn_ord/= -addnA leq_addr; apply.
    apply/andP; split=> //.
    apply/eqP/rowP => i.
    move/(_ (unsplit (inl (unsplit (inr i))) : 'I_(n + (m - n) + (k - m))%N)): h0.
    rewrite nth_ngraph !mxE unsplitK mxE unsplitK.
    by rewrite mem_iota addnA ltn_ord/= leq_addr; apply.
  case/orP: (leq_total n k) => [nk|kn].
    rewrite -(subnKC km) -(subnKC nk) [X in (m-X)%N]subnKC//.
    apply/eqP/SAsetP => x.
    rewrite inSAset_castnD.
    move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
    apply/inSAset_castDn/andP => [[y]|[lA] /eqP ->];
        rewrite SAset_cast_ge -?addnA ?leq_addr//.
      move: (lsubmx y) (rsubmx y) (hsubmxK y) => yl yr <- {y} [] /[swap] <- {yl}.
      move=> /SAin_setP/= [] /holds_take.
      rewrite -(take_takel _ (@leq_addr (k - n)%N n)) !take_ngraph !row_mxKl => /rcf_satP lA /holdsAnd.
      rewrite subDnCA ?leq_addr// subDnCA// subnn addn0 addnC /= => h0.
      split=> //; apply/eqP/rowP => i.
      move/(_ (unsplit (inl (unsplit (inr i))) : 'I_(n + (k - n) + (m - k))%N)): h0.
      by rewrite nth_ngraph !mxE unsplitK mxE unsplitK mem_iota addnA ltn_ord/= leq_addr; apply.
    exists (row_mx (row_mx l 0) 0); rewrite row_mxKl; split=> //.
    apply/SAin_setP => /=; split.
      apply/holds_take.
      rewrite -(take_takel _ (@leq_addr (k - n)%N n)) !take_ngraph !row_mxKl.
      exact/rcf_satP.
    apply/holdsAnd => i; rewrite mem_iota subDnCA ?leq_addr// subDnCA// subnn addn0 [X in (n + X)%N]addnC /= addnA => /andP[+ ilt] _.
    rewrite -[i]/(Ordinal ilt : nat) nth_ngraph mxE.
    case: (splitP (Ordinal ilt)) => j ->; rewrite mxE//.
    by case: (splitP j) => j' ->; rewrite leqNgt ?ltn_ord// mxE.
  move: A; rewrite -(subnKC nm) -(subnKC kn) [X in (m - X)%N]subnKC// -addnA => A.
  apply/eqP/SAsetP => x; apply/inSAset_castDn/inSAset_castDn => -[y].
    rewrite [_ _ A]SAset_cast_ge ?addnA ?leq_addr// => -[] /SAin_setP /= [] /holds_take + _.
    rewrite takeD take_ngraph drop_ngraph take_ngraph -ngraph_cat => yA -> {x}.
    exists (row_mx (lsubmx y) (lsubmx (rsubmx y))); split; first exact/rcf_satP.
    by rewrite row_mxKl.
  move=> [] /rcf_satP yA -> {x}; exists (row_mx (lsubmx y) (row_mx (rsubmx y) 0)); split; last by rewrite row_mxKl.
  rewrite [_ _ A]SAset_cast_ge ?addnA ?leq_addr//; apply/SAin_setP => /=; split.
    apply/holds_take.
    by rewrite takeD take_ngraph drop_ngraph take_ngraph -ngraph_cat row_mxKr !row_mxKl hsubmxK.
    apply/holdsAnd => i; rewrite {1}addnA subnKC// subnKC// mem_iota -{1 2}(subnKC kn) -addnA => /andP[] + ilt _ /=.
    rewrite -[i]/(Ordinal ilt : nat) nth_ngraph.
    rewrite mxE; case: splitP => j ->.
      by rewrite leqNgt (leq_trans (ltn_ord j) (leq_addr _ _)).
    rewrite leq_add2l mxE; case: splitP => j' ->; last by rewrite mxE.
    by rewrite leqNgt ltn_ord.
rewrite geq_min leqNgt mn/= => km.
rewrite SAset_cast_le// SAset_cast_le ?(ltnW mn)// SAset_cast_le ?(ltnW (leq_ltn_trans km mn))//.
apply/eqP/SAsetP => x; rewrite -[X in nquantify X](size_ngraph x); apply/SAin_setP/SAin_setP => /nexistsP [y] => /rcf_satP.
  rewrite -[in X in rcf_sat _ X](subnKC km).
  rewrite -[y]ngraph_tnth -ngraph_cat => /SAin_setP.
  have mE: (k + (m - k))%N = size (ngraph x ++ y) by rewrite size_cat size_ngraph size_tuple subnKC.
  rewrite [X in nquantify X]mE -{2}[y]ngraph_tnth -ngraph_cat => /nexistsP [] {mE}.
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
have mE: (k + (m - k))%N = size (ngraph x ++ Tuple ts) by rewrite size_cat size_ngraph size_tuple subnKC.
rewrite [X in nquantify X]mE -{2}[Tuple ts]ngraph_tnth -ngraph_cat.
apply/nexistsP.
rewrite ngraph_cat subnKC//.
have /eqP ds: size (drop (m - k)%N y) = (n - m)%N.
  by rewrite size_drop size_tuple subnBA// addnC subnKC// (ltnW (leq_ltn_trans km mn)).
by exists (Tuple ds); rewrite -catA ngraph_tnth/= cat_take_drop.
Qed.

Definition SAset_proj m (s : {SAset F^n}) := SAset_cast n (SAset_cast m s).

Lemma SAset_proj_ge m (s : {SAset F^n}) : (n <= m)%N -> SAset_proj m s = s.
Proof. by move=> nm; rewrite /SAset_proj SAset_cast_trans ?minnn// SAset_cast_id. Qed.

Lemma inSAset_proj m (s : {SAset F^n}) (x : 'rV[F]_n) :
  reflect (exists y, y \in s /\ x = y *m @diag_mx F n (\row_i (i < m)%N%:R))%R (x \in SAset_proj m s).
Proof.
case: (ltnP m n) => [mn|nm]; last first.
  have ->: diag_mx (\row_i (i < m)%:R)%R = (1%:M)%R :> 'M[F]_n.
    by apply/matrixP => i j; rewrite !mxE (leq_trans (ltn_ord i) nm).
  rewrite SAset_proj_ge//; apply/(iffP idP) => [xs|[y][ys]->]; last by rewrite mulmx1.
  by exists x; split=> //; rewrite mulmx1.
rewrite /SAset_proj.
move: s x; rewrite -(subnKC (ltnW mn)) => s' x.
rewrite -(hsubmxK x); move: (lsubmx x) (rsubmx x) => l r {x}.
rewrite inSAset_castnD.
apply/(iffP andP) => [[] /inSAset_castDn [y][ys]|[y][ys]].
  rewrite row_mxKl row_mxKr => -> /eqP -> {l r}; exists y; split=> //.
  rewrite -(hsubmxK y); move: (lsubmx y) (rsubmx y) => l r {y ys}.
  rewrite row_mxKl -[X in diag_mx X]cat_ffun_id diag_mx_row.
  rewrite mul_row_block !mulmx0 addr0 add0r; congr row_mx.
    rewrite -[LHS]mulmx1; congr (_ *m _)%R.
    by apply/matrixP => i j; rewrite !mxE/= ltn_ord.
  rewrite -[LHS](mulmx0 _ r); congr (_ *m _)%R.
  by apply/matrixP => i j; rewrite !mxE/= ltnNge leq_addr/= mul0rn.
move: ys; rewrite row_mxKl row_mxKr -(hsubmxK y); move: (lsubmx y) (rsubmx y) => yl yr {y} ys.
rewrite -[X in diag_mx X]cat_ffun_id diag_mx_row.
rewrite mul_row_block !mulmx0 addr0 add0r => /eq_row_mx[] -> ->; split.
  apply/inSAset_castDn; exists (row_mx yl yr); split=> //.
  rewrite row_mxKl -[RHS]mulmx1; congr (_ *m _)%R.
  by apply/matrixP => i j; rewrite !mxE/= ltn_ord.
apply/eqP; rewrite -[RHS](mulmx0 _ yr); congr (_ *m _)%R.
by apply/matrixP => i j; rewrite !mxE/= ltnNge leq_addr/= mul0rn.
Qed.

Definition SAset_disjoint (s1 s2 : {SAset F^n}) :=
  s1 :&: s2 == SAset0 F n.

Definition SAset_trivI (I : {fset {SAset F^n}}) :=
  [forall s1 : I, [forall s2 : I, (val s1 != val s2) ==> SAset_disjoint (val s1) (val s2)]].

Definition SAset_partition (I : {fset {SAset F^n}}) :=
  (SAset0 F n \notin I) && SAset_trivI I && (\big[@SAsetU F n/SAset0 F n]_(s : I) val s == SAsetT F n).

End SAsetTheory.

Section POrder.

Variable F : rcfType.

Variable n : nat.

Fact SAset_disp : unit. Proof. exact tt. Qed.

HB.instance Definition SAset_latticeType :=
  Order.isMeetJoinDistrLattice.Build SAset_disp {SAset _}
  (@SAsubsetEI F n) (@properEneq' F n) (@SAsetIC F n) (@SAsetUC F n)
    (@SAsetIA F n) (@SAsetUA F n) (@SAsetKU' F n) (@SAsetKI' F n) (@SAsetIUl F n) (@SAsetI_idem F n).

HB.instance Definition _ :=
  Order.hasBottom.Build SAset_disp {SAset F^n} (@sub0set F n).

HB.instance Definition SAset_tblatticeType :=
  Order.hasTop.Build SAset_disp {SAset F^n} (@subsetT F n).

HB.instance Definition _ := Order.hasRelativeComplement.Build SAset_disp {SAset F^n} (@SAsetID0 F n) (@SAsetUID F n).

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
+ move/rcf_satP/nforallP/(_ x) : h.
  case: x => s /= /eqP -{1}<-.
  by move/nexistsP => [t h]; exists t; apply/rcf_satP.
+ apply/rcf_satP/nforallP => x /=.
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
    reflect
    (forall (x : 'rV[F]_n), exists (y : 'rV[F]_m), (row_mx x y) \in s)
    (s \in SAtot).
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
    (forall (x : 'rV[F]_n), forall (y1 y2 : 'rV[F]_m),
    (row_mx x y1) \in s -> (row_mx x y2) \in s -> y1 = y2)
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

Definition get_y (f : {formula_(n + m) F}) (x : 'rV[F]_n) : ('rV[F]_m):=
  match boolP (ex_y f x) with
| AltTrue p => proj1_sig (sigW (ex_yE f x p))
| AltFalse _ => (\row_(i < m) 0)
end.

Definition form_to_fun (f : {formula_(n + m) F}) : 'rV[F]_n -> 'rV[F]_m :=
    fun (x : 'rV[F]_n) => get_y f x.

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

Lemma SAfun_func (f : {SAfun}) (x : 'rV[F]_n) (y1 y2 : 'rV[F]_m) :
    row_mx x y1 \in SAgraph f -> row_mx x y2 \in SAgraph f -> y1 = y2.
Proof. by apply: inSAfunc; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Lemma SAfun_tot (f : {SAfun}) (x : 'rV[F]_n) :
    exists (y : 'rV[F]_m), row_mx x y \in SAgraph f.
Proof. by apply: inSAtot; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Definition SAfun_to_fun (f : SAfun) : 'rV[F]_n -> 'rV[F]_m :=
    fun x => proj1_sig (sigW (SAfun_tot f x)).

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

Lemma inSAgraph (f : {SAfun F^n -> F^m}) (x : 'rV[F]_n) :
    row_mx x (f x) \in SAgraph f.
Proof.
by rewrite /SAfun_to_fun; case: ((sigW (SAfun_tot f x))) => y h.
Qed.

Definition SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) : {SAset F^m} :=
  [set | nquantify m n Exists ((subst_formula ((iota m n)
          ++ (iota O m)) f) /\ (subst_formula (iota m n) s)) ].

Lemma inSAimset (x : 'rV[F]_n)
 (s : {SAset F^n}) (f : {SAfun F^n -> F^m}) :
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

Lemma SAimsetP (f : {SAfun F^n -> F^m})
  (s : {SAset F^n}) (y : 'rV[F]_m) :
   reflect (exists2 x : 'rV[F]_n, x \in s & y = f x)
            (y \in (SAimset f s)).
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

Lemma inSAfun (f : {SAfun F^n -> F^m})
   (x : 'rV[F]_n) (y : 'rV[F]_m):
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

Definition SAepigraph (f : {SAfun F^n -> F^1}) : {SAset F^(n + 1)} := 
  [set | nquantify (n + 1) 1 Exists ((subst_formula ((iota 0 n)
  ++ [:: n.+1; n]) f) /\ ('X_n.+1 <% 'X_n)) ].

Definition SAhypograph (f : {SAfun F^n -> F^1}) : {SAset F^(n + 1)} := 
  [set | nquantify (n + 1) 1 Exists ((subst_formula ((iota 0 n)
  ++ [:: n.+1; n]) f) /\ ('X_n <% 'X_n.+1)) ].

End SAfunTheory.

Lemma inSAepigraph (F : rcfType) (n : nat) (f : {SAfun F^n -> F^1}) (x : 'rV[F]_(n + 1)) :
  (x \in SAepigraph f) = (f (lsubmx x) ord0 ord0 < rsubmx x ord0 ord0).
Proof.
move: (lsubmx x) (rsubmx x) (hsubmxK x) => l r <- {x}.
apply/SAin_setP/idP; rewrite -[X in nquantify X _ _](size_ngraph (row_mx l r)).
  move=> /nexistsP [y] /= [] /holds_subst.
  rewrite nth_cat size_map size_enum_ord {11 20}addn1 ltnn subnn.
  rewrite nth_cat size_map size_enum_ord {11}addn1 leqnn (nth_map (unsplit (inr ord0))) ?size_enum_ord ?addn1//.
  have {26}->: n = @unsplit n 1 (inr ord0) by rewrite /= addn0.
  rewrite nth_ord_enum mxE unsplitK ngraph_cat -catA subst_env_cat.
  rewrite subst_env_iota_catl ?size_ngraph//= !nth_cat size_map size_enum_ord.
  rewrite ltnNge leqnSn/= subSnn size_ngraph/= ltnn !subnn/= (nth_map ord0) ?size_enum_ord//.
  rewrite -[X in nth ord0 _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
  move=> /holds_take; rewrite take_cat size_ngraph ltnNge {1}addn1 leqnSn/=.
  rewrite subDnCA// subnn/= => hf; congr (_ < _).
  transitivity ((\row_i tnth y i) ord0 ord0); first by rewrite mxE (tnth_nth 0).
  congr (_ _ ord0 ord0); apply/esym/eqP => /=; rewrite inSAfun.
  apply/rcf_satP; move: hf; congr holds; apply/(eq_from_nth (x0:=0)) => [|i].
    by rewrite size_cat size_map size_enum_ord size_ngraph.
  rewrite size_cat size_map size_enum_ord /= => ilt.
  have i0: 'I_(n+1) by rewrite addn1; exact: ord0.
  rewrite (nth_map (Ordinal ilt)) ?size_enum_ord// -[i]/(Ordinal ilt : nat) nth_ord_enum.
  rewrite mxE -{1}(splitK (Ordinal ilt)); case: (split _) => j.
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

Lemma inSAhypograph (F : rcfType) (n : nat) (f : {SAfun F^n -> F^1}) (x : 'rV[F]_(n + 1)) :
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
  rewrite ltnNge leqnSn/= subSnn size_ngraph/= ltnn !subnn/= (nth_map ord0) ?size_enum_ord//.
  rewrite -[X in nth ord0 _ X]/(@ord0 1 : nat) (@nth_ord_enum 1 ord0 ord0).
  move=> /holds_take; rewrite take_cat size_ngraph ltnNge {1}addn1 leqnSn/=.
  rewrite subDnCA// subnn/= => hf; congr (_ < _).
  transitivity ((\row_i tnth y i) ord0 ord0); first by rewrite mxE (tnth_nth 0).
  congr (_ _ ord0 ord0); apply/esym/eqP => /=; rewrite inSAfun.
  apply/rcf_satP; move: hf; congr holds; apply/(eq_from_nth (x0:=0)) => [|i].
    by rewrite size_cat size_map size_enum_ord size_ngraph.
  rewrite size_cat size_map size_enum_ord /= => ilt.
  have i0: 'I_(n+1) by rewrite addn1; exact: ord0.
  rewrite (nth_map (Ordinal ilt)) ?size_enum_ord// -[i]/(Ordinal ilt : nat) nth_ord_enum.
  rewrite mxE -{1}(splitK (Ordinal ilt)); case: (split _) => j.
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
rewrite /abs /=; split.
+ move=> [[->|-> h]]; first by move=> h; rewrite ger0_norm.
  by rewrite ler0_norm // -oppr_gte0.
+ move->.
  rewrite normr_ge0; split => //.
  have [le_e0|lt_0e] := ler0P e`_i; first by right.
  by left.
Qed.

Lemma absP2 (e : seq F) (i j : nat) : rcf_sat e (abs i j) = (e`_j == `|e`_i|).
Proof.
apply/rcf_satP/eqP; first by move/absP.
by move=> h; apply/absP.
Qed.

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
apply/holds_eq_vec; move: h1 h2; case: t => s sz //= {sz}.
case: s => // a s; case: s => // b s -> /= {b}; case: s => //.
  by move <-.
by move=> b // _ ->.
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
have [le_e0|lt_0e] := ler0P x; first by right.
by left.
Qed.

Fact SAfun_SAabs : (absset \in SAfunc) && (absset \in SAtot).
Proof. by rewrite functional_absset total_absset. Qed.

Definition SAabs := MkSAfun SAfun_SAabs.

Definition diagf_form (f : {formula_(1 + 1) F}) (n : nat) (v1 v2 : seq nat) :=
(if size v1 == size v2 then
(\big[And/True]_(i < size v1)
(subst_formula [::(nth O v1 (nat_of_ord i)); (nth O v2 (nat_of_ord i))] f)%oT)
                       else False).

Fact pre_nvar_diagf_form (a b n : nat) (f : {formula_(1 + 1) F}) :
@nvar F ((maxn a b) + n) (diagf_form f n (iota a n) (iota b n)).
Proof.
rewrite /diagf_form !size_iota eqxx /nvar formula_fv_bigAnd.
apply/bigfcupsP => /= i _.
rewrite (fsubset_trans (fv_subst_formula mnfset_key _ _)) //.
apply/fsubsetP=> j.
rewrite !seq_fsetE mem_iota /=.
rewrite in_cons mem_seq1 add0n !nth_iota //.
rewrite addn_maxl.
by move/orP => [/eqP -> | /eqP ->]; rewrite leq_max ltn_add2l ltn_ord //= orbT.
Qed.

Fact nvar_diagf_form (f : {formula_(1 + 1) F}) (n : nat) :
@nvar F (n + n) (diagf_form f n (iota 0 n) (iota n n)).
Proof. by rewrite -{1}[n]max0n pre_nvar_diagf_form. Qed.

Definition diagf (n : nat) (f : {formula_(1 + 1) F}) :=
  \pi_{SAset F ^ (n + n)} (MkFormulan (nvar_diagf_form f n)).

Lemma functional_diagf (f : {SAfun F^1 -> F^1}) (n : nat) :
  diagf n f \in SAfunc.
Proof.
apply/rcf_satP/nforallP => t [/holds_subst h1 /holds_subst h2].
move: h1 h2; rewrite !subst_env_cat /diagf.
move/holds_repr_pi/rcf_satP => h1.
move/holds_repr_pi/rcf_satP.
move: h1.
rewrite /= /diagf_form !size_iota eqxx !rcf_sat_forall=> /forallP h1 /forallP h2.
apply/holds_eq_vec.
apply: (@eq_from_nth _ 0) => [ | i ]; rewrite !size_subst_env // => lt_in.
rewrite !(nth_map O) ?size_iota //.
move/(_ (Ordinal lt_in))/rcf_satP/holds_subst : h2.
move/(_ (Ordinal lt_in))/rcf_satP/holds_subst : h1.
rewrite !nth_iota //= ?nth_cat ?size_iota ?size_subst_env lt_in.
rewrite -[X in (_ < X)%N]addn0 ltn_add2l ltn0 add0n.
rewrite !(nth_map O) ?size_iota // ?(addnC, addnK) //.
rewrite [in (n + _ - n)%N]addnC addnK.
rewrite !nth_iota // add0n => /rcf_satP h1 /rcf_satP h2.
move: (@SAfun_func F 1 1 f (const_mx t`_i)
                           (const_mx t`_(n + i))
                           (const_mx t`_(2 * n + i))).
rewrite !inE !ngraph_cat /= enum_ordSl enum_ord0.
rewrite /= !mxE mul2n -addnn.
by move/(_ h1 h2)/matrixP/(_ ord0 ord0); rewrite !mxE.
Qed.

Lemma total_diagf (f : SAfun F 1 1) (n : nat) : diagf n f \in SAtot.
Proof.
apply/rcf_satP/nforallP => t.
rewrite -[X in nquantify X _ _ _](size_tuple t).
apply/nexistsP.
pose x := \row_(i < n) ((f (const_mx (nth 0 t (nat_of_ord i)))) ord0 ord0).
exists (ngraph x); apply/holds_repr_pi => /=.
rewrite /diagf_form !size_iota eqxx.
apply/rcf_satP; rewrite rcf_sat_forall; apply/forallP => /= i.
apply/rcf_satP/holds_subst.
rewrite ?nth_iota // add0n /= !nth_cat size_tuple ltn_ord.
rewrite -ltn_subRL subnn ltn0. (* this line can be used earlier in the code *)
rewrite addnC addnK.
move : (inSAgraph f (const_mx t`_i)); rewrite inE.
move/rcf_satP; apply: eqn_holds => j y.
rewrite !mxE /=.
rewrite (nth_map 0); last by rewrite size_enum_ord ltn_ord.
rewrite (nth_map 0); last by rewrite -enumT size_enum_ord.
rewrite -enumT nth_ord_enum; case: y => m lt_m2.
rewrite mxE; case: splitP => k ->; first by rewrite !ord1 mxE.
rewrite !ord1 addn0 -[in RHS]tnth_nth /=.
have -> : [seq (\row_i1 (f (const_mx t`_i1)) 0 0) 0 i0 | i0 <- enum 'I_n]`_i =
           (\row_i1 (f (const_mx t`_i1)) 0 0) 0 i.
  by rewrite mxE (nth_map i _) ?size_enum_ord // nth_ord_enum mxE.
by rewrite mxE.
Qed.

Fact SAfun_diagf (f : {SAfun F^1 -> F^1}) (n : nat) :
   (diagf n f \in SAfunc) && (diagf n f \in SAtot).
Proof. by rewrite functional_diagf total_diagf. Qed.

Definition SAid (f : {SAfun F^1 -> F^1}) (n : nat) :=
  MkSAfun (SAfun_diagf f n).

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
apply: (sameP (rcf_satP _ _)).
apply: (equivP _ (nexistsP _ _ _)).
apply: (iffP idP); last first.
+  move=> [t] /=.
  move=> [ /holds_subst hf /holds_subst hg].
  move: hf hg.
  rewrite subst_env_cat -catA.
  rewrite subst_env_iota_catl; last by rewrite size_map size_enum_ord.
  rewrite catA subst_env_iota_catr ?size_tuple ?card_ord //.
  rewrite subst_env_cat subst_env_iota_catr ?size_tuple ?card_ord //.
  rewrite -catA subst_env_iota; last 2 first.
  - by rewrite size_map size_enum_ord.
  - by rewrite size_map size_enum_ord.
  rewrite -[t]ngraph_tnth -!ngraph_cat.
  move/holds_ngraph; rewrite -inSAfun; move/eqP ->.
  by move/holds_ngraph; rewrite -inSAfun; move/eqP ->.
+ move/eqP => eq_gfu_v.
  exists (ngraph (f u)).
  split; apply/holds_subst; rewrite subst_env_cat.
  - rewrite -catA subst_env_iota_catl; last by rewrite size_map size_enum_ord.
    rewrite catA subst_env_iota_catr ?size_tuple ?card_ord // -ngraph_cat.
    by apply/holds_ngraph; apply: inSAgraph.
  - rewrite subst_env_iota_catr ?size_tuple ?card_ord //.
    rewrite -catA subst_env_iota; last 2 first.
      by rewrite size_map size_enum_ord.
    by rewrite size_map size_enum_ord.
    rewrite -ngraph_cat; apply/holds_ngraph; rewrite -eq_gfu_v.
    exact: inSAgraph.
Qed.

Fact SAfun_SAcomp (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :
   (SAcomp_graph f g \in SAfunc) && (SAcomp_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAcomp_graphP; move=> /eqP-> /eqP->.
by apply/inSAtot => x; exists (g (f x)); rewrite SAcomp_graphP.
Qed.

Definition SAcomp (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :=
    MkSAfun (SAfun_SAcomp f g).

Lemma SAcompP (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :
    SAcomp f g =1 g \o f.
Proof.
move=> x; apply/eqP; rewrite eq_sym -SAcomp_graphP.
by move: (inSAgraph (SAcomp f g) x).
Qed.

Definition SAfun_const_graph n m (x : 'rV[F]_m) : {SAset F^(n + m)%N} :=
  [set | \big[And/True]_(i : 'I_m) ('X_(@unsplit n m (inr i)) == GRing.Const (x ord0 i))].

Lemma SAfun_SAfun_const n m (x : 'rV[F]_m) :
  (SAfun_const_graph n x \in SAfunc) && (SAfun_const_graph n x \in SAtot).
Proof.
apply/andP; split.
  apply/inSAfunc => x0 y1 y2 /SAin_setP /holdsAnd /= h1 /SAin_setP /holdsAnd /= h2.
  apply/rowP => i.
  move/(_ i): h1; rewrite mem_index_enum => /(_ Logic.eq_refl Logic.eq_refl).
  rewrite ngraph_cat nth_cat size_ngraph ltnNge leq_addr/= subDnCA// subnn addn0 nth_ngraph => ->.
  move/(_ i): h2; rewrite mem_index_enum => /(_ Logic.eq_refl Logic.eq_refl).
  by rewrite ngraph_cat nth_cat size_ngraph ltnNge leq_addr/= subDnCA// subnn addn0 nth_ngraph.
apply/inSAtot => y; exists x.
apply/SAin_setP/holdsAnd => i _ _ /=.
by rewrite ngraph_cat nth_cat size_ngraph ltnNge leq_addr/= subDnCA// subnn addn0 nth_ngraph.
Qed.

Definition SAfun_const n m (x : 'rV[F]_m) := MkSAfun (SAfun_SAfun_const n x).

Definition join_formula (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) : formula F :=
  (repr (val f)) /\
  (subst_formula (iota 0 m ++ iota (m+n) p) (repr (val g))).

Lemma nvar_join_formula (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) :
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

Definition SAjoin_graph (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) :=
  \pi_{SAset F^(m + (n + p))} (MkFormulan (nvar_join_formula f g)).

Lemma SAjoin_graphP (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) (u : 'rV[F]_m) (v : 'rV[F]_(n + p)) :
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

Fact SAfun_SAjoin (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) :
  (SAjoin_graph f g \in SAfunc) && (SAjoin_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/inSAfunc => x y1 y2; rewrite !SAjoin_graphP => /eqP <- /eqP.
by apply/inSAtot => x; exists (row_mx (f x) (g x)); rewrite SAjoin_graphP.
Qed.

Definition SAjoin (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) :=
  MkSAfun (SAfun_SAjoin f g).

Lemma SAjoinP (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) (x : 'rV[F]_m) :
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

Lemma SAadd_graphP p (u : 'rV[F]_(p + p)) (v : 'rV[F]_p) :
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

Definition SAfun_add (n p : nat) (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAjoin f g) (SAadd p).

Definition opp_formula (p : nat) : formula F :=
  (\big[And/True]_(i : 'I_p) ('X_(p + i) == - 'X_i))%oT.

Lemma nvar_opp_formula p : nvar (p + p) (opp_formula p).
Proof.
apply/fsubsetP => x; rewrite formula_fv_bigAnd => /bigfcupP [i _] /fset2P.
case=> ->; rewrite seq_fsetE mem_iota /= add0n; last exact/ltn_addl.
by rewrite ltn_add2l.
Qed.

Definition SAopp_graph p :=
  \pi_{SAset F^(p + p)} (MkFormulan (nvar_opp_formula p)).

Lemma SAopp_graphP p (u v : 'rV[F]_p) :
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

Definition SAfun_sub (n p : nat) (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAjoin f (SAcomp g (SAopp p))) (SAadd p).

Definition SAfun_lt (n : nat) (f g : {SAfun F^n -> F^1}) :=
  SAgraph (SAfun_sub f g) :<=: (SAsetT F n) :*: (SAset_pos F).

Definition partition_of_graphs (n m : nat) (xi : m.-tuple {SAfun F^n -> F^1}) : {fset {SAset F^(n + 1)%N}} :=
  ((\big[@SAsetI F (n + 1)/SAset0 F (n + 1)]_i SAepigraph (tnth xi i))
  |` ((\big[@SAsetI F (n + 1)/SAset0 F (n + 1)]_i SAhypograph (tnth xi i))
    |` ([fset SAgraph f | f in tval xi]
      `|` [fset SAepigraph (nth (@SAfun_const n 1 0) xi (val i)) :&: SAhypograph (nth (@SAfun_const n 1 0) xi (val i).+1) | i in 'I_m.-1])))%fset.

Definition partition_of_graphs_above n (s : {SAset F^n}) (m : nat) (xi : m.-tuple {SAfun F^n -> F^1}) : {fset {SAset F^(n + 1)%N}} :=
  [fset x :&: (s :*: SAsetT F 1) | x in partition_of_graphs xi].

Definition SAset_path_connected n (s : {SAset F^n}) :=
  {in s &, forall x y, exists xi : {SAfun F^1 -> F^n}, {within set_of_SAset (SAepigraph (@SAfun_const 0 1 0) :&: SAhypograph (@SAfun_const 0 1 1)), continuous (xi : 'rV_1 -> 'rV_n)} /\ xi 0 = x /\ xi 1 = y}.

End SAfunOps.

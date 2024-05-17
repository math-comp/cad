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
From mathcomp Require Import zmodp mxpoly mpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order finset classical_sets topology.

From SemiAlgebraic Require Import auxresults formula.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax.
Import numFieldTopology.Exports.

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

Fixpoint mpoly_rterm (R : unitRingType) (n : nat) (t : term R) : {mpoly R[n]} :=
  match t with
  | Var i =>
    match ltnP i n with
    | LtnNotGeq ilt => 'X_(Ordinal ilt)
    | _ => 0
    end
  | Const c => mpolyC n c
  | NatConst i => mpolyC n i%:R
  | Add t u => (mpoly_rterm n t) + (mpoly_rterm n u)
  | Opp t => - (mpoly_rterm n t)
  | NatMul t i => (mpoly_rterm n t) *+ i
  | Mul t u => (mpoly_rterm n t) * (mpoly_rterm n u)
  | Exp t i => (mpoly_rterm n t) ^+ i
  end.

Lemma mevalXn (n k : nat) (R : comRingType) (x : 'I_n -> R) (p : {mpoly R[n]}) :
  (p ^+ k).@[x] = p.@[x] ^+ k.
Proof.
elim: k => [|k IHk]; first by rewrite !expr0 meval1.
by rewrite !exprS mevalM IHk.
Qed.

Lemma meval_mpoly_rterm (R : realDomainType) (n : nat) (x : 'I_n -> R) (t : term R) :
  (mpoly_rterm n t).@[x] = eval [seq x i | i <- enum 'I_n] t.
Proof.
elim: t => /=.
- move=> i; case: (ltnP i n) => [ilt|ige].
    rewrite mevalXU (nth_map (Ordinal ilt)) ?size_enum_ord//.
    by rewrite -[X in nth _ _ X]/(nat_of_ord (Ordinal ilt)) nth_ord_enum.
  by rewrite meval0 nth_default// size_map size_enum_ord.
- exact/mevalC.
- move=> i; exact/mevalC.
- by move=> t IHt u IHu; rewrite mevalD IHt IHu.
- by move=> t IHt; rewrite mevalN IHt.
- by move=> t IHt i; rewrite mevalMn IHt.
- by move=> t IHt u IHu; rewrite mevalM IHt IHu.
- by move=> t IHt i; rewrite mevalXn IHt.
Qed.

Lemma forall_ord1 (p : pred 'I_1) :
  [forall i : 'I_1, p i] = p ord0.
Proof.
apply/forallP/idP => [/(_ ord0) //|p0].
by case; case=> // ilt; move: p0; congr p; apply/val_inj.
Qed.

Lemma eval_rterm (R : unitRingType) (e : seq R) (t : GRing.term R) :
  GRing.rterm t -> GRing.eval e (to_rterm t) = GRing.eval e t.
Proof.
elim: t => //=.
- by move=> t IHt u IHu /andP[] {}/IHt -> {}/IHu ->.
- by move=> t /[apply] ->.
- by move=> t /[swap] n /[apply] ->.
- by move=> t IHt u IHu /andP[] {}/IHt -> {}/IHu ->.
- by move=> t /[swap] n /[apply] ->.
Qed.

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

HB.instance Definition _ := Monoid.isComLaw.Build {SAset F^n} (SAset0 F n) (@SAsetU F n) SAsetUA SAsetUC SAset0U.

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

HB.instance Definition _ := Monoid.isComLaw.Build {SAset F^n} (SAsetT F n) (@SAsetI F n) SAsetIA SAsetIC SAsetTI.

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
apply/eqP/SAsetP => x; rewrite inSAsetC inSAset_bigcap inSAset_bigcup -has_predC.
elim: r => [//|] i r IHr /=.
by rewrite negb_imply IHr inSAsetC.
Qed.

Lemma SAsetCbigcup (I : Type) (r : seq I) (P : pred I) (f : I -> {SAset F^n}) :
  (~: \bigcup_(i <- r | P i) f i) = \bigcap_(i <- r | P i) ~: f i.
Proof.
rewrite -[RHS]SAsetCK SAsetCbigcap; congr (~: _).
by apply/eq_bigr => i _; rewrite SAsetCK.
Qed.

Lemma rcf_sat_subst (e : seq F) (s : seq nat) (f : formula F) :
  rcf_sat e (subst_formula s f) = rcf_sat (subst_env s e) f.
Proof. by apply/rcf_satP/rcf_satP => /holds_subst. Qed.

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

Lemma SAset_disjointC (s1 s2 : {SAset F^n}) :
  SAset_disjoint s1 s2 = SAset_disjoint s2 s1.
Proof. by rewrite /SAset_disjoint SAsetIC. Qed.

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

Definition SApreimset (f : {SAfun F^n -> F^m}) (s : {SAset F^m}) : {SAset F^n} :=
  [set | nquantify n m Exists (f /\ (subst_formula (iota n m) s)) ].

Lemma inSApreimset (x : 'rV[F]_n)
 (s : {SAset F^m}) (f : {SAfun F^n -> F^m}) :
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

Lemma nth_catr [T : Type] (x0 : T) (s1 s2 : seq T) (p n : nat) :
  p = size s1 ->
  nth x0 (s1 ++ s2) (p + n) = nth x0 s2 n.
Proof.
move=> ->.
by rewrite nth_cat -[X in (_ < X)%N]addn0 ltn_add2l ltn0 subDnCA// subnn addn0.
Qed.

Definition SAid_graph (n : nat) : {SAset F^(n + n)} :=
  [set | \big[And/True]_(i : 'I_n) ('X_(n + i) == 'X_i)].

Lemma SAid_graphP n (x y : 'rV[F]_n) :
  (row_mx x y \in SAid_graph n) = (y == x).
Proof.
apply/SAin_setP/eqP => [/holdsAnd xy|->];
  [apply/rowP => i; move: xy => /(_ i (mem_index_enum _) isT) /=
 | apply/holdsAnd => i _ _ /=];
  (rewrite enum_ordD map_cat nth_catr; last by rewrite 2!size_map size_enum_ord);
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

Definition SAcomp (m n p : nat) (f : SAfun F n p) (g : SAfun F m n) :=
    MkSAfun (SAfun_SAcomp g f).

Lemma SAcompE (m n p : nat) (f : SAfun F n p) (g : SAfun F m n) :
    SAcomp f g =1 f \o g.
Proof.
move=> x; apply/eqP; rewrite eq_sym -SAcomp_graphP.
by move: (inSAgraph (SAcomp f g) x).
Qed.

Definition SAfun_const_graph n m (x : 'rV[F]_m) : {SAset F^(n + m)%N} :=
  [set | \big[And/True]_(i : 'I_m) ('X_(@unsplit n m (inr i)) == GRing.Const (x ord0 i))].

Lemma SAfun_constP n m (x : 'rV[F]_m) (y : 'rV[F]_n) (z : 'rV[F]_m) :
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
apply/andP; split; last by apply/inSAtot => y; exists x; rewrite SAfun_constP.
by apply/inSAfunc => x0 y1 y2; rewrite !SAfun_constP => /eqP -> /eqP.
Qed.

Definition SAfun_const n m (x : 'rV[F]_m) := MkSAfun (SAfun_SAfun_const n x).

Lemma SAfun_constE n m (x : 'rV[F]_m) (y : 'rV[F]_n) :
  SAfun_const n x y = x.
Proof. by apply/eqP; rewrite inSAfun /SAfun_const SAfun_constP. Qed.

Definition SAfun_split_graph n m : {SAset F^(n + m + n)} :=
  [set | \big[And/True]_(i : 'I_n) ('X_(n + m + i) == 'X_i)].

Lemma SAfun_splitP n m (x : 'rV[F]_(n + m)) (y : 'rV[F]_n) :
  row_mx x y \in SAfun_split_graph n m = (y == lsubmx x).
Proof.
apply/SAin_setP/eqP => [/holdsAnd/= yE|->];
    [apply/rowP => i; move: yE => /(_ i (mem_index_enum _) isT)
    | apply/holdsAnd => i _ _ /=];
  (rewrite enum_ordD map_cat nth_catr;
    last by rewrite 2!size_map size_enum_ord);
  rewrite -map_comp (nth_map i) ?size_enum_ord//= nth_ord_enum mxE;
  rewrite (unsplitK (inr i)) nth_cat 2!size_map size_enum_ord;
  rewrite (leq_trans (ltn_ord i) (leq_addr m n)) -map_comp enum_ordD;
  rewrite map_cat nth_cat 2!size_map size_enum_ord ltn_ord -map_comp;
  rewrite (nth_map i) ?size_enum_ord//= nth_ord_enum !mxE;
  by rewrite (unsplitK (inl (unsplit (inl i))))/=.
Qed.

Lemma SAfun_SAfun_split n m:
  (SAfun_split_graph n m \in SAfunc) && (SAfun_split_graph n m \in SAtot).
Proof.
apply/andP; split; last by apply/inSAtot => y; exists (lsubmx y); rewrite SAfun_splitP.
by apply/inSAfunc => x0 y1 y2; rewrite !SAfun_splitP => /eqP -> /eqP.
Qed.

Definition SAfun_split n m := MkSAfun (SAfun_SAfun_split n m).

Lemma SAfun_splitE n m (x : 'rV[F]_(n + m)) :
  SAfun_split n m x = lsubmx x.
Proof. by apply/eqP; rewrite inSAfun /SAfun_split SAfun_splitP. Qed.

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

Lemma SAjoinE (m n p : nat) (f : {SAfun F^m -> F^n}) (g : {SAfun F^m -> F^p}) (x : 'rV[F]_m) :
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

Lemma SAaddE p (x y : 'rV[F]_p) : SAadd p (row_mx x y) = (x + y)%R.
Proof. by apply/eqP; rewrite inSAfun SAadd_graphP row_mxKl row_mxKr. Qed.

Definition SAfun_add (n p : nat) (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAadd p) (SAjoin f g).

Lemma SAfun_addE (n p : nat) (f g : {SAfun F^n -> F^p}) (x : 'rV[F]_n) :
  SAfun_add f g x = (f x + g x)%R.
Proof. by rewrite SAcompE/= SAjoinE SAaddE. Qed.

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

Lemma SAoppE p (x : 'rV[F]_p) : SAopp p x = - x.
Proof. by apply/eqP; rewrite inSAfun SAopp_graphP. Qed.

Definition SAfun_opp n p (f : {SAfun F^n -> F^p}) :=
  SAcomp (SAopp p) f.

Lemma SAfun_oppE n p (f : {SAfun F^n -> F^p}) (x : 'rV[F]_n) :
  SAfun_opp f x = - f x.
Proof. by rewrite SAcompE/= SAoppE. Qed.

Definition SAfun_sub (n p : nat) (f g : {SAfun F^n -> F^p}) :=
  SAcomp (SAadd p) (SAjoin f (SAcomp (SAopp p) g)).

Lemma SAfun_subE (n p : nat) (f g : {SAfun F^n -> F^p}) (x : 'rV[F]_n) :
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

Lemma SAfun_addNr n p : left_inverse (SAfun_const n (0 : 'rV[F]_p)) (@SAfun_opp n p) (@SAfun_add n p).
Proof.
move=> f; apply/eqP/SAfunE => x.
by rewrite SAfun_addE SAfun_oppE SAfun_constE addNr.
Qed.

HB.instance Definition _ n p := GRing.isZmodule.Build {SAfun F^n -> F^p}
  (@SAfun_addA n p) (@SAfun_addC n p) (@SAfun_add0r n p) (@SAfun_addNr n p).

Definition SAfun_le (n : nat) (f g : {SAfun F^n -> F^1}) :=
  SAgraph (SAfun_sub g f) :<=: (SAsetT F n) :*: (SAset_itv `[0, +oo[%R).

Lemma SAfun_leP (n : nat) (f g : {SAfun F^n -> F^1}) :
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

Definition SAfun_lt (n : nat) (f g : {SAfun F^n -> F^1}) :=
  SAgraph (SAfun_sub g f) :<=: (SAsetT F n) :*: (SAset_pos F).

Lemma SAfun_ltP (n : nat) (f g : {SAfun F^n -> F^1}) :
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

Definition SAmpoly_graph (n : nat) (p : {mpoly F[n]}) : {SAset F^(n + 1)} :=
  [set | 'X_n == term_mpoly p (fun i => 'X_i)].

Lemma SAmpoly_graphP (n : nat) (p : {mpoly F[n]}) (x : 'rV[F]_n) (y : 'rV[F]_1) :
  (row_mx x y \in SAmpoly_graph p) = (y ord0 ord0 == p.@[x ord0]).
Proof.
by apply/SAin_setP/eqP; rewrite /= eval_term_mpoly enum_ordD/= map_cat;
  rewrite nth_cat/= -map_comp size_map size_enum_ord ltnn subnn enum_ordSl;
  rewrite enum_ord0/= row_mxEr => ->; apply/meval_eq => i /=;
  rewrite nth_cat size_map size_enum_ord (ltn_ord i);
  rewrite (nth_map i) ?size_enum_ord// nth_ord_enum/= row_mxEl.
Qed.

Lemma SAfun_SAmpoly (n : nat) (p : {mpoly F[n]}) :
  (SAmpoly_graph p \in @SAfunc _ n 1) && (SAmpoly_graph p \in @SAtot _ n 1).
Proof.
apply/andP; split.
  apply/inSAfunc => x y1 y2; rewrite !SAmpoly_graphP => /eqP <- /eqP y12.
  apply/rowP; case; case=> //= lt01.
  by move/esym: y12; congr (_ = _); congr (_ _ _); apply/val_inj.
by apply/inSAtot => x; exists (\row__ p.@[x ord0]); rewrite SAmpoly_graphP mxE.
Qed.

Definition SAmpoly (n : nat) (p : {mpoly F[n]}) := MkSAfun (SAfun_SAmpoly p).

Lemma SAmpolyE n (p : {mpoly F[n]}) (x : 'rV[F]_n) :
  SAmpoly p x = \row__ p.@[x ord0].
Proof. by apply/eqP; rewrite inSAfun SAmpoly_graphP !mxE. Qed.

Definition SAset_lt (s t : {SAset F^1}) :=
  (t != SAset0 F 1) && rcf_sat [::] ('forall 'X_0, s ==> 'forall 'X_1, subst_formula [:: 1%N] t ==> ('X_0 <% 'X_1))%oT.

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
apply/forallP => /= -[] /= s; rewrite inT => /(nthP (SAset0 F 1)) [i] iS <-.
apply/forallP => /= -[] /= t; rewrite inT => /(nthP (SAset0 F 1)) [j] jS <-.
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
rewrite -IHxi// inSAset_bigcup => /hasP[] /= s /(nthP (SAset0 F _)) [i].
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
    by rewrite (nth_map 0)// nth_iota//= inSAset_seq mem_seq1 rowPE forall_ord1 mxE.
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
rewrite inS; apply/negP => /(nthP (SAset0 F 1)) [i].
rewrite size_map size_iota; case: (posnP i) => [->|i0] ixi; last first.
  move: xisort => /sorted_partition_of_pts /(lt_sorted_ltn_nth (SAset0 F 1 : SAsetltType)).
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

Definition partition_of_graphs (n : nat) (xi : seq {SAfun F^n -> F^1}) : seq {SAset F^(n + 1)%N} :=
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
by rewrite inSApreimset inSAset0.
Qed.

(* Lemma cardfs_partition_of_pts m (xi : m.-tuple F) :
  path.sorted <%O xi ->
  #|` partition_of_pts xi | = m.*2.+1.
Proof.
case: m xi => [|m] xi /(lt_sorted_ltn_nth 0) xisort; first by rewrite partition_of_pts0 cardfs1.
have {xisort} xilt : forall (i j : 'I_m.+1), (i < j)%O ->
    tnth xi i < tnth xi j.
  move=> i j; rewrite ltEord => ij; move: xisort => /(_ i j).
  by rewrite !inE size_tuple !ltn_ord => /(_ isT isT); rewrite ij !(tnth_nth 0).
have xile : forall (i j : 'I_m.+1), (i <= j)%O -> tnth xi i <= tnth xi j.
  move=> i j; rewrite le_eqVlt => /orP [/eqP ->|/xilt /ltW //].
  exact/lexx.
rewrite cardfsU1; case/boolP: (_ \in _) => [|_] /=.
  have xlt: \row__ (tnth xi 0 - 1)%R \in \big[SAsetI (n:=1)/SAsetT F 1]_(i < m.+1) SAset_itv `]-oo, (tnth xi i)[%R.
    rewrite inSAset_bigcap; apply/allP => i _ /=.
    rewrite inSAset_itv in_itv/= mxE.
    have /xile xi0: (ord0 <= i)%O by rewrite leEord.
    by apply/(lt_le_trans _ xi0); rewrite -subr_gt0 opprB addrCA subrr addr0.
  rewrite in_fset1U in_fsetU => /orP [/eqP|/orP [|] /imfsetP [i] _]
      /eqP/SAsetP/(_ (\row__ (tnth xi 0 - 1)%R)); rewrite xlt => /esym.
  - rewrite -big_enum inSAset_bigcap/= enum_ordSl/=.
    by rewrite inSAset_itv in_itv/= mxE -subr_gt0 addrAC subrr add0r oppr_gt0 ltr10.
  - rewrite inSAset_seq mem_seq1 rowPE forall_ord1 !mxE => /eqP xiE.
    have /xile: (ord0 <= i)%O by rewrite leEord.
    by rewrite -xiE -subr_ge0 addrAC subrr add0r oppr_ge0 ler10.
  - rewrite inSAset_itv in_itv/= mxE => /andP[+] _.
    have /xile: (ord0 <= (widen_ord (leqnSn _) i))%O by rewrite leEord.
    rewrite [X in _ <= X](tnth_nth 0) => x0i /(le_lt_trans x0i).
    by rewrite -subr_gt0 addrAC subrr add0r oppr_gt0 ltr10.
rewrite cardfsU1; case/boolP: (_ \in _) => [|_] /=.
  have xgt: \row__ (tnth xi ord_max + 1)%R \in \big[SAsetI (n:=1)/SAsetT F 1]_(i < m.+1) SAset_itv `]tnth xi i, +oo[%R.
    rewrite inSAset_bigcap; apply/allP => i _ /=.
    rewrite inSAset_itv in_itv/= mxE andbT.
    have /xile xi0: (i <= ord_max)%O by rewrite leEord -ltnS.
    by apply/(le_lt_trans xi0); rewrite -subr_gt0 addrAC subrr add0r.
    rewrite in_fsetU => /orP [|] /imfsetP [i] _ /eqP/SAsetP
        /(_ (\row__ (tnth xi ord_max + 1)%R)); rewrite xgt => /esym.
      rewrite inSAset_seq mem_seq1 rowPE forall_ord1 !mxE => /eqP xmE.
      have /xile: (i <= ord_max)%O by rewrite leEord -ltnS.
      by rewrite -xmE -subr_ge0 opprD addrA subrr add0r oppr_ge0 ler10.
    rewrite inSAset_itv in_itv/= mxE => /andP[_] xmi.
    have /xile: (lift ord0 i <= ord_max)%O by rewrite leEord -ltnS.
    rewrite (tnth_nth 0) => /(lt_le_trans xmi).
    by rewrite -subr_gt0 opprD addrA subrr add0r oppr_gt0 ltr10.
rewrite cardfsU; have -> 
Search disjoint.
Search #|` (_ `&` _) |%fset.
 
      





Lemma SAset_fiber_inj_partition_of_graphs n m (xi : m.-tuple (SAfunltType n))
  (s t : {SAset F^(n + 1)}) (x : 'rV[F]_n) :
  path.sorted <%O xi ->
  s \in partition_of_graphs xi ->
  t \in partition_of_graphs xi ->
  SAset_fiber s x = SAset_fiber t x -> s = t.
   Proof. *)

Lemma SAset_partition_of_graphs (n : nat) (xi : seq (SAfunltType n)) :
  path.sorted <%O xi -> SAset_partition [fset x | x in partition_of_graphs xi].
Proof.
set S := [fset x | x in partition_of_graphs xi].
have inS x : x \in S = (x \in partition_of_graphs xi).
  by apply/imfsetP/idP => [[] y yS -> //|xS]; exists x.
move=> /(lt_sorted_ltn_nth (0 : SAfunltType n)) xisort.
have {}xisort x : path.sorted <%O [seq (f : {SAfun F^n -> F^1}) x 0 0 | f <- xi].
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
  apply/negP; rewrite inS => /(nthP (SAset0 F _)) [i].
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
apply/forallP => -[] /= s; rewrite inS => /(nthP (SAset0 F _)) [i] + <-.
rewrite size_map size_iota => ilt.
apply/forallP => -[] /= t; rewrite inS => /(nthP (SAset0 F _)) [j] + <-.
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
have nk k: (k < (size xi).*2.+1)%N -> nth (SAset0 F _) (partition_of_pts xi') k \in T.
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

Definition partition_of_graphs_above n (s : {SAset F^n}) (xi : seq {SAfun F^n -> F^1}) : {fset {SAset F^(n + 1)%N}} :=
  [fset x :&: (s :*: SAsetT F 1) | x in partition_of_graphs xi].

Lemma SAset_partition_of_graphs_above n (S : {fset {SAset F^n}}) (xi : S -> seq (SAfunltType n)) :
  SAset_partition S ->
  (forall s, path.sorted <%O (xi s)) -> 
  SAset_partition (\big[fsetU/fset0]_(s : S) partition_of_graphs_above (val s) (in_tuple (xi s))).
Proof.
move=> /andP[] /andP[] S0 SI /eqP SU xisort.
have {}xisort (s : S) x : path.sorted <%O [seq (f : {SAfun F^n -> F^1}) x 0 0 | f <- xi s].
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
  have vS: v :&: \val s :*: SAsetT F 1 \in \bigcup_(s | true) partition_of_graphs_above (val s) (xi s).
    apply/bigfcupP; exists s; first by rewrite mem_index_enum.
    by apply/imfsetP; exists v.
  apply/hasP; exists [` vS ] => /=; first exact/mem_index_enum.
  by rewrite inSAsetI xv inSAsetX xs inSAsetT.
apply/andP; split.
  apply/negP => /bigfcupP [] /= s _ /imfsetP [t] /= /(nthP (SAset0 F _)) [i].
  rewrite size_map size_iota => ilt <- i0.
  have [s0|[x xs]] := set0Vmem (val s).
    by move: S0; rewrite -s0 => /negP; apply; apply/(fsvalP s).
  have: SAset_fiber (SAset0 F (n + 1)) x = SAset0 F _.
    by rewrite /SAset_fiber SApreimset0.
  rewrite i0 /SAset_fiber SApreimsetI -/(SAset_fiber _ _).
  have ->: SApreimset (SAjoin (SAfun_const 1 x) (SAid 1)) (fsval s :*: SAsetT F 1) = SAsetT F _.
    apply/eqP/SAsetP => y; rewrite inSApreimset SAjoinE SAfun_constE inSAsetX.
    by rewrite row_mxKl xs !inSAsetT.
  rewrite SAsetIT -[LHS](@nth_map _ _ _ (SAset0 F _) (fun s => SAset_fiber s x));
      last by rewrite size_map size_iota.
  rewrite SAset_fiber_partition_of_graphs => {}i0.
  move: (SAset_partition_of_pts (xisort s x)).
  set T := [fset x | x in _] => /andP[] /andP[] + _ _ => /imfsetP; apply.
  exists (SAset0 F 1) => //=.
  by rewrite -i0 mem_nth// size_map size_iota size_map.
apply/forallP => -[] /= a /bigfcupP [s] _ /imfsetP [sa] /=.
move=>/(nthP (SAset0 F _)) [i] + <- ->.
rewrite size_map size_iota => ilt.
apply/forallP => -[] /= b /bigfcupP [t] _ /imfsetP [tb] /=.
move=>/(nthP (SAset0 F _)) [j] + <- ->.
rewrite size_map size_iota => jlt; apply/implyP.
move: jlt; have [<- jlt ij|st _ _] := eqVneq s t; last first.
  rewrite /SAset_disjoint -subset0; apply/SAset_subP => x.
  rewrite !inSAsetI 2!inSAsetX => /andP[] /andP[_] /andP[xs] _ /andP[_] /andP[xt] _.
  move: SI => /forallP/(_ s) /forallP /(_ t) /implyP.
  rewrite (inj_eq val_inj) => /(_ st); rewrite /SAset_disjoint /subset0 => /eqP st0.
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
have nk k: (k < (size (xi s)).*2.+1)%N -> nth (SAset0 F _) (partition_of_pts xi') k \in T.
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

Definition SAset_path_connected n (s : {SAset F^n}) :=
  {in s &, forall x y, exists xi : {SAfun F^1 -> F^n}, {within set_of_SAset (SAepigraph (@SAfun_const 0 1 0) :&: SAhypograph (@SAfun_const 0 1 1)), continuous xi} /\ xi 0 = x /\ xi 1 = y}.

End SAfunOps.

Section SAconvex.
Variables (F : rcfType).

Definition SAset_segment (n : nat) (x y : 'rV[F]_n) : {SAset F^n} :=
  [set | ('exists 'X_n, 0 <=% 'X_n /\ 'X_n <=% 1 /\
      \big[And/True]_(i < n)
        ('X_i == (1-'X_n) * Const (x ord0 i) + 'X_n * Const (y ord0 i)))%oT].

Lemma inSAset_segment (n : nat) (x y z : 'rV[F]_n) :
  reflect (exists t, 0 <= t <= 1 /\ z = (1-t) *: x + t *: y)%R (z \in SAset_segment x y).
Proof.
apply/(iffP (SAin_setP _ _)) => /= [[t]|[t][] /andP[] t0 t1 ->].
  rewrite nth_set_nth/= eqxx => -[t0][t1] /holdsAnd/=.
  rewrite nth_set_nth/= eqxx => zE.
  exists t; split; first by rewrite t0.
  apply/rowP => i; move/(_ i (mem_index_enum _) isT): zE.
  rewrite nth_set_nth/= (ltn_eqF (ltn_ord i)) (nth_map i) ?size_enum_ord//.
  by rewrite nth_ord_enum !mxE.
exists t; rewrite nth_set_nth/= eqxx; split=> //; split=> //.
apply/holdsAnd => /= i _ _.
rewrite !nth_set_nth/= eqxx (ltn_eqF (ltn_ord i)) (nth_map i) ?size_enum_ord//.
by rewrite nth_ord_enum !mxE.
Qed.

Definition SAset_convex (n : nat) (s : {SAset F^n}) :=
  {in s &, forall x y : 'rV[F]_n, SAset_segment x y :<=: s}.

Lemma SAsetT_convex (n : nat) : SAset_convex (SAsetT F n).
Proof. by move=> x y _ _; exact/subsetT. Qed.

Lemma SAset0_convex (n : nat) : SAset_convex (SAset0 F n).
Proof. by move=> x y; rewrite inSAset0. Qed.

Lemma SAsetI_convex (n : nat) (s t : {SAset F^n}) :
  SAset_convex s -> SAset_convex t -> SAset_convex (s :&: t).
Proof.
move=> sc tc x y; rewrite !inSAsetI SAsubsetI => /andP[xs xt] /andP[ys yt].
by apply/andP; split; [apply/sc|apply/tc].
Qed.

End SAconvex.

Lemma rterm_tsubst (R : unitRingType) (t : GRing.term R) (s : nat * GRing.term R) :
  GRing.rterm t -> GRing.rterm (snd s) -> GRing.rterm (GRing.tsubst t s).
Proof.
move=> + sr; elim: t => //=.
- by move=> n _; case: (n == fst s).
- by move=> t IHt u IHu /andP[] /IHt {}IHt /IHu {}IHu; apply/andP; split.
- by move=> t IHt u IHu /andP[] /IHt {}IHt /IHu {}IHu; apply/andP; split.
Qed.

Lemma rform_fsubst (R : realDomainType) (f : formula R) (s : nat * GRing.term R) :
  rformula f -> GRing.rterm (snd s) -> rformula (fsubst f s).
Proof.
move=> + sr; elim: f => //=.
- by move=> t u /andP[] tr ur; apply/andP; split; apply/rterm_tsubst.
- by move=> t u /andP[] tr ur; apply/andP; split; apply/rterm_tsubst.
- by move=> t u /andP[] tr ur; apply/andP; split; apply/rterm_tsubst.
- by move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg; apply/andP; split.
- by move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg; apply/andP; split.
- by move=> f IHf g IHg /andP[] /IHf {}IHf /IHg {}IHg; apply/andP; split.
- by move=> n f IHf fr; case: (n == fst s); last apply/IHf.
- by move=> n f IHf fr; case: (n == fst s); last apply/IHf.
Qed.

Lemma rform_qf_elim (R : rcfType) (f : formula R) :
  rformula (qf_elim f).
Proof.
rewrite /qf_elim.
elim: (enum_fset _) => /= [|x r IHr]; last exact/rform_fsubst.
exact/rform_elim/to_rform_rformula.
Qed.

Lemma SAset_formula (F : rcfType) (n : nat) (s : {SAset F^n}) :
  {f : formula F | rformula f /\ qf_form f /\ s = [set | f]}.
Proof.
exists (qf_elim s); split; first exact/rform_qf_elim.
split; first exact/qf_elim_qf.
apply/eqP/SAsetP => x; apply/rcf_satP/SAin_setP => [xs|/rcf_satP/qf_elim_holdsP//].
exact/rcf_satP/qf_elim_holdsP.
Qed.

Lemma SAset_nf (F : rcfType) (n : nat) (s : {SAset F^n}) :
  {P : seq ({mpoly F[n]} * seq {mpoly F[n]}) |
      s = \big[@SAsetU F n/SAset0 F n]_(p <- P)
        (SApreimset (SAmpoly (fst p)) (SAset_seq [:: 0])
        :&: \big[@SAsetI F n/SAsetT F n]_(q <- (snd p)) SApreimset (SAmpoly q) (SAset_pos F))}.
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
  rewrite !inSAsetI 2!inSApreimset !SAmpolyE !inSAset1 !rowPE !forall_ord1 !mxE
    pf10 pg10/= !inSAset_bigcap.
  by apply/andP; split; apply/allP => p pP /=; apply/pfg20; rewrite mem_cat pP// orbT.
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
    by rewrite inSAsetI/= big_seq1 2!inSApreimset inSAset1 inSAset_pos !SAmpolyE
      rowPE forall_ord1 !mxE meval0 eqxx mevalN oppr_gt0.
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
  rewrite inSApreimset SAmpolyE inSAset1 rowPE forall_ord1 !mxE mevalB subr_eq0.
  by rewrite !meval_mpoly_rterm !evalE !eval_rterm//; apply/SAin_setP/eqP.
- move=> t u /andP[] rt ru _.
  exists [:: (0, [:: mpoly_rterm n (to_rterm (GRing.Add u (GRing.Opp t)))])].
  rewrite big_seq1/= big_seq1; apply/eqP/SAsetP => x.
  rewrite inSAsetI 2!inSApreimset !SAmpolyE inSAset1 rowPE forall_ord1.
  rewrite inSAset_pos !mxE meval0 eqxx/= mevalB subr_gt0 !meval_mpoly_rterm.
  by rewrite !evalE !eval_rterm//; apply/SAin_setP/idP.
- move=> t u /andP[] rt ru _.
  pose v := GRing.Add u (GRing.Opp t).
  exists [:: (mpoly_rterm n (to_rterm v), [::]);
    (0, [:: mpoly_rterm n (to_rterm v)])].
  rewrite big_cons big_nil big_seq1/= big_seq1 SAsetIT; apply/eqP/SAsetP => x.
  rewrite inSAsetU inSAsetI 3!inSApreimset !SAmpolyE 2!inSAset1 !rowPE.
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

(* WIP 
Lemma SAset_supP (s : {SAset F^1}) :
  s != SAset0 F 1 -> SAsetUB s != SAset0 F 1
  -> {x : 'rV[F]_1 | SAsetUB s = SAset_itv `[(x 0 0), +oo[%R}.
Proof.
pose Goal (t : {SAset F^1}) := t != SAset0 F 1 ->
  SAsetUB t != SAset0 F 1 ->
  {x : 'cV_1 | SAsetUB t = SAset_itv `[(x 0 0), +oo[%R}.
have supU : forall s t : {SAset F^1}, Goal s -> Goal t -> Goal (s :|: t).
  move=> {}s t sP tP; rewrite /Goal.
  Search SAsetU SAset0.
  {1}SAsetUBU inSAsetI.
  move=> /andP[] {}/sP [x +] {}/tP [y].
  wlog: x y s t / x 0 0 <= y 0 0 => xy.
    move: (le_total (x 0 0) (y 0 0)); case/boolP: (x 0 0 <= y 0 0) => /= xy' yx.
      exact/xy.
    by rewrite SAsetUC => /[swap]; apply/xy.
  rewrite !inSAsetI => /andP[] /inSAsetUB xub /inSAsetLB xlb
    /andP[] /inSAsetUB yub /inSAsetLB ylb.
  exists y; rewrite inSAsetI; apply/andP; split; last first.
    by apply/inSAsetLB => z; rewrite SAsetUBU inSAsetI => /andP[] _ /ylb.
  apply/inSAsetUB => z; rewrite inSAsetU => /orP; case => zst; last exact/yub.
  exact/(le_trans _ xy)/xub.
have {}supU (I : Type) (r : seq I) (f : I -> {SAset F^1}) :
  (forall i, Goal (f i)) -> Goal (\big[@SAsetU F 1/SAset0 F 1]_(i <- r) f i).
  move=> iub; elim: r => [|i r IHr].
    rewrite big_nil => /inSAsetUB/(_ 0).


right; case: (SAset_nf s) => P ->.
Check SAset_nf.
 *)
  

End SAorder.

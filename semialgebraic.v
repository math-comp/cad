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
From mathcomp Require Import ssralg poly polydiv ssrnum mxpoly binomial finalg.
From mathcomp Require Import zmodp mxpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order finset.

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

Lemma SAsetP (s1 s2 : {SAset F^n}) : reflect (s1 =i s2) (s1 == s2).
Proof.
move: s1 s2; apply: quotW => f1; apply: quotW => f2.
apply: (iffP idP) => [/eqP <-|] //.
rewrite eqmodE /equivf => h; apply/rcf_satP/nforallP => u.
split; move/holds_repr_pi/holds_tuple; [rewrite h | rewrite -h];
by move/holds_tuple/holds_repr_pi.
Qed.

End SemiAlgebraicSet.

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

Section Next.

Variables (F : rcfType) (n : nat).

Definition SAset0 := \pi_{SAset F^n} (Bool false).

Lemma pi_form (f : {formula_n F}) (x : 'rV[F]_n) :
    (x \in \pi_{SAset F^n} f) = rcf_sat (ngraph x) f.
Proof. by rewrite inE; apply/rcf_satP/rcf_satP => ?; apply/holds_repr_pi. Qed.

Lemma inSAset0 (x : 'rV[F]_n) : (x \in SAset0) = false.
Proof. by rewrite pi_form. Qed.

Definition SAset1_formula (x : 'rV[F]_n) :=
    \big[And/True%oT]_(i < n) ('X_i == (x ord0 i)%:T)%oT.

Lemma SAset1_formulaP (x y : 'rV[F]_n) :
    rcf_sat (ngraph x) (SAset1_formula y) = (x == y).
Proof.
rewrite rcf_sat_forallP; apply/forallP/eqP; last first.
  by move=> -> i; rewrite simp_rcf_sat /= nth_ngraph.
move=> h; apply/rowP => i; move/(_ i) : h.
by rewrite simp_rcf_sat /= nth_ngraph => /eqP.
Qed.

Lemma SAset1_proof (x : 'rV[F]_n) : @nvar F n (SAset1_formula x).
Proof.
rewrite /SAset1_formula; elim/big_ind: _; rewrite /nvar.
- exact: fsub0set.
- by move=> ???? /=; apply/fsubUsetP.
- by move=> i /= _; rewrite fsetU0 fsub1set mnfsetE /=.
Qed.

Definition SAset1 (x : 'rV[F]_n) : {SAset F^n} :=
    \pi_{SAset F^n} (MkFormulan (SAset1_proof x)).

Lemma inSAset1 (x y : 'rV[F]_n) : (x \in SAset1 y) = (x == y).
Proof. by rewrite pi_form SAset1_formulaP. Qed.

End Next.

Section POrder.

Variable F : rcfType.

Variable n : nat.

Definition SAsub (s1 s2 : {SAset F^n}) :=
    rcf_sat [::] (nquantify O n Forall (s1 ==> s2)).

Lemma reflexive_SAsub : reflexive SAsub.
Proof. by move=> s; apply/rcf_satP/nforallP => u; rewrite cat0s. Qed.

Lemma antisymetry_SAsub : antisymmetric SAsub.
Proof.
apply: quotP => f1 _; apply: quotP => f2 _.
move => /andP [/rcf_satP/nforallP sub1 /rcf_satP/nforallP sub2].
apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
split; move/holds_repr_pi=> hf.
+ move/(_ u) : sub1; rewrite cat0s => sub1.
  by apply/holds_repr_pi; apply: sub1.
+ by move/(_ u) : sub2 => sub2; apply/holds_repr_pi; apply: sub2.
Qed.

Lemma transitive_SAsub : transitive SAsub.
Proof.
apply: quotP => f1 _; apply: quotP => f2 _; apply: quotP => f3 _.
move/rcf_satP/nforallP => sub21; move/rcf_satP/nforallP => sub13.
apply/rcf_satP/nforallP => u.
move/holds_repr_pi => holds_uf2.
by apply: sub13; apply: sub21; apply/holds_repr_pi.
Qed.

Fact SAset_disp : unit. Proof. exact tt. Qed.

Fact nvar_False : @formula_fv F False `<=` mnfset 0 n.
Proof. by rewrite fsub0set. Qed.

Definition SAset_bottom := \pi_{SAset F^n} (MkFormulan nvar_False).

Lemma SAset_bottomP (s : {SAset F^n}) : SAsub SAset_bottom s.
Proof. by apply/rcf_satP/nforallP => u; move/holds_repr_pi. Qed.

(* TODO: Why does {SAset F^n} not have a structure of bPOrderType yet? *)

Definition SAset_meet (s1 s2 : {SAset F^n}) : {SAset F^n} :=
    \pi_{SAset F^n} (formulan_and s1 s2).

Definition SAset_join (s1 s2 : {SAset F^n}) : {SAset F^n} :=
    \pi_{SAset F^n} (formulan_or s1 s2).

Fact commutative_meet : commutative SAset_meet.
Proof.
move=> s1 s2; apply/eqP; rewrite eqmodE.
by apply/rcf_satP/nforallP => u; split => [[h1 h2] | [h2 h1]]; split.
Qed.

Fact commutative_join : commutative SAset_join.
Proof.
move=> s1 s2; apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
by split => h; apply/or_comm.
Qed.

Fact associative_meet : associative SAset_meet.
Proof.
move => s1 s2 s3; apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
split=> [[h1 /holds_repr_pi [h2 h3]]|[/holds_repr_pi [h1 h2] h3]];
by split=> //; apply/holds_repr_pi => []; split.
Qed.

Fact associative_join : associative SAset_join.
Proof.
move=> s1 s2 s3; apply/eqP; rewrite eqmodE.
apply/rcf_satP/nforallP => u.
split => [ [ | /holds_repr_pi [|]] | [/holds_repr_pi [|] | ] ].
+ by left; apply/holds_repr_pi; left.
+ by left; apply/holds_repr_pi; right.
+ by right.
+ by left.
+ by right; apply/holds_repr_pi; left.
+ by right; apply/holds_repr_pi; right.
Qed.

Fact meet_join (s1 s2 : {SAset F^n}) : SAset_meet s2 (SAset_join s2 s1) = s2.
Proof.
apply/eqP/SAsetP => x; rewrite !inE.
rewrite !rcf_sat_repr_pi simp_rcf_sat rcf_sat_repr_pi.
by rewrite simp_rcf_sat andbC orbK.
Qed.

Fact join_meet (s1 s2 : {SAset F^n}) : SAset_join s2 (SAset_meet s2 s1) = s2.
Proof.
apply/eqP/SAsetP => x; rewrite !inE !rcf_sat_repr_pi.
by rewrite simp_rcf_sat rcf_sat_repr_pi simp_rcf_sat andbC andKb.
Qed.

Fact le_meet (s1 s2 : {SAset F^n}) : SAsub s1 s2 = (SAset_meet s1 s2 == s1).
Proof.
apply/idP/idP=> [sub12| /SAsetP h].
+ apply/SAsetP => x; move : (ngraph x) => e.
  rewrite !inE rcf_sat_repr_pi simp_rcf_sat.
  apply : andb_idr; apply/implyP.
  move : sub12 => /rcf_satP/nforallP sub12.
  apply/implyP; move/rcf_satP => holds_e_s1.
  apply/rcf_satP; move : holds_e_s1.
  exact: sub12.
+ apply/rcf_satP/nforallP => e.
  by move/holds_tuple; rewrite -h; move/holds_tuple/holds_repr_pi => [].
Qed.

Fact left_distributive_meet_join : left_distributive SAset_meet SAset_join.
Proof.
set vw := holds_repr_pi; move=> s1 s2 s3; apply/eqP; rewrite eqmodE.
apply/rcf_satP/nforallP => t.
split=> [[/vw /= [h1|h2] h3]|[/vw [h1 h3]| /vw [h2 h3]]].
+ by left; apply/vw.
+ by right; apply/vw.
+ by split => //; apply/vw; left.
+ by split => //; apply/vw; right.
Qed.

Fact idempotent_meet : idempotent SAset_meet.
Proof.
move=> x; apply/eqP/SAsetP => i.
by rewrite !inE rcf_sat_repr_pi simp_rcf_sat andbb.
Qed.

#[non_forgetful_inheritance]
HB.instance Definition SAset_latticeType :=
  Order.isMeetJoinDistrLattice.Build SAset_disp {SAset _}
  le_meet (fun _ _ => erefl) commutative_meet commutative_join
    associative_meet associative_join meet_join join_meet left_distributive_meet_join idempotent_meet.

HB.instance Definition _ :=
  Order.hasBottom.Build SAset_disp {SAset F^n} SAset_bottomP.

Definition SAset_top : {SAset F^n} :=
  \pi_{SAset F^n} (Bool true).

Lemma SAset_topP (s : {SAset F^n}) : (s <= SAset_top)%O.
Proof. by apply/rcf_satP/nforallP => t h; apply/holds_repr_pi. Qed.

Canonical SAset_tblatticeType :=
  Order.hasTop.Build _ _ SAset_topP.

Definition SAset_sub (s1 s2 : {SAset F^n}) : {SAset F^n} :=
  \pi_{SAset F^n} (formulan_and s1 (formulan_not s2)).

Fact meet_sub (s1 s2 : {SAset F^n}) :
    SAset_meet s2 (SAset_sub s1 s2) = SAset_bottom.
Proof.
apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => t.
by split => //; move => [? /holds_repr_pi [_ ?]].
Qed.

Fact join_meet_sub (s1 s2 : {SAset F^n}) :
  SAset_join (SAset_meet s1 s2) (SAset_sub s1 s2) = s1.
Proof.
apply/eqP/SAsetP => x; rewrite !inE.
rewrite !rcf_sat_repr_pi !simp_rcf_sat !rcf_sat_repr_pi.
by rewrite !simp_rcf_sat -andb_orr orbN andbT.
Qed.

HB.instance Definition _ := Order.hasRelativeComplement.Build SAset_disp {SAset F^n} meet_sub join_meet_sub.

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

Lemma f_is_ftotalE (f : {formula_(n + m) F}) :
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

Lemma f_is_funcE (f : {formula_(n + m) F}) :
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

Lemma SAtotE (s : {SAset F ^ (n + m)}) :
    reflect
    (forall (x : 'rV[F]_n), exists (y : 'rV[F]_m), (row_mx x y) \in s)
    (s \in SAtot).
Proof.
rewrite inE; apply: (iffP (f_is_ftotalE _)) => s_sat x.
  have [y sat_s_xy] := s_sat (ngraph x).
  exists (\row_(i < m) (nth 0 y i)).
  by rewrite inE ngraph_cat ngraph_nth.
have [y xy_in_s] := s_sat ((\row_(i < n) (nth 0 x i))).
exists (ngraph y).
by move: xy_in_s; rewrite inE ngraph_cat ngraph_nth.
Qed.

Lemma SAfuncE (s : {SAset F ^ (n + m)}) :
    reflect
    (forall (x : 'rV[F]_n), forall (y1 y2 : 'rV[F]_m),
    (row_mx x y1) \in s -> (row_mx x y2) \in s -> y1 = y2)
    (s \in SAfunc).
Proof.
rewrite inE; apply: (iffP (f_is_funcE _)) => fun_s x y1 y2.
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

Fact nvar_SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) :
  formula_fv (nquantify m n Exists ((subst_formula ((iota m n)
          ++ (iota O m)) f) /\ (subst_formula (iota m n) s)))
  `<=` mnfset 0 m.
Proof.
rewrite formula_fv_nexists fsubDset fsubUset.
rewrite !(fsubset_trans (fv_subst_formula mnfset_key _ _));
by rewrite ?fsubsetUl // seq_fset_cat fsubset_refl.
Qed.

Definition SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) :=
    \pi_{SAset F^m} (MkFormulan (nvar_SAimset f s)).

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
Proof. by apply: SAfuncE; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Lemma SAfun_tot (f : {SAfun}) (x : 'rV[F]_n) :
    exists (y : 'rV[F]_m), row_mx x y \in SAgraph f.
Proof. by apply: SAtotE; case: f; move => /= [f h /andP [h1 h2]]. Qed.

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

Section SASetTheory.

Variable F : rcfType.

Lemma in_SAset_bottom (m : nat) (x : 'rV[F]_m) :
    x \in (@SAset_bottom F m) = false.
Proof. by rewrite pi_form. Qed.

Lemma SAset1_neq0 (n : nat) (x : 'rV[F]_n) : (SAset1 x) != (@SAset_bottom F n).
Proof.
apply/negP; move/SAsetP/(_ x) => h.
by move: h; rewrite inSAset1 eqxx pi_form.
Qed.

Lemma SAemptyP (n : nat) (x : 'rV[F]_n) : x \notin (@SAset_bottom F n).
Proof. by rewrite in_SAset_bottom. Qed.

Lemma inSAset1B (n : nat) (x y : 'rV[F]_n) : (x \in SAset1 y) = (x == y).
Proof. by rewrite inSAset1. Qed.

Lemma sub_SAset1 (n : nat) (x : 'rV[F]_n) (s : {SAset F^n}) :
  (SAset1 x <= s)%O = (x \in s).
Proof.
apply: (sameP (rcf_satP _ _)).
apply: (equivP _ (nforallP _ _ _)).
apply: (iffP idP).
  move=> h t; rewrite cat0s /=.
  move/rcf_satP : h => holds_s.
  move/holds_tuple; rewrite inSAset1 => /eqP eq_x.
  by move: holds_s; rewrite -eq_x ngraph_tnth.
move/(_ (ngraph x)).
rewrite cat0s inE => /rcf_satP.
rewrite simp_rcf_sat => /implyP; apply.
apply/rcf_satP/holds_tuple; rewrite inSAset1; apply/eqP/rowP => i.
by rewrite mxE (tnth_nth 0) nth_ngraph.
Qed.

Lemma non_empty : forall (n : nat) (s : {SAset F^n}),
    ((@SAset_bottom F n) < s)%O -> {x : 'rV[F]_n | x \in s}.
Proof.
move=> a s /andP [bot_neq_s _].
move: s bot_neq_s; apply: quotW => /= f; rewrite eqmodE /=.
move=> /rcf_satP/n_nforall_formula/nexistsP P.
apply: sigW; move: P => [x hx] /=; exists (\row_(i < a) x`_i).
rewrite inE ngraph_nth rcf_sat_repr_pi.
by move/rcf_satP: hx; rewrite cat0s !simp_rcf_sat; case: rcf_sat.
Qed.

Lemma le_sub : forall (n : nat) (s1 s2 : {SAset F^n}),
    (forall (x : 'rV[F]_n), x \in s1 -> x \in s2) -> (s1 <= s2)%O.
Proof.
move=> a s1 s2 sub12; apply/rcf_satP/nforallP => t.
rewrite cat0s /= => /rcf_satP s1_sat; apply/rcf_satP.
by move/(_ ((\row_(i < a) t`_i))): sub12; rewrite !inE ngraph_nth => ->.
Qed.

Lemma SAunion : forall (n : nat) (x : 'rV[F]_n) (s1 s2 : {SAset F^n}),
    (x \in SAset_join s1 s2) = (x \in s1) || (x \in s2).
Proof.
move=> n x s1 s2.
rewrite /SAset_join pi_form !inE.
apply/idP/idP.
move/rcf_satP => /=.
by move=> [l|r]; apply/orP; [left|right]; apply/rcf_satP.
by move/orP => [l|r]; apply/rcf_satP; [left|right]; apply/rcf_satP.
Qed.

Lemma in_graph_SAfun (n m : nat) (f : {SAfun F^n -> F^m}) (x : 'rV[F]_n) :
    row_mx x (f x) \in SAgraph f.
Proof.
by rewrite /SAfun_to_fun; case: ((sigW (SAfun_tot f x))) => y h.
Qed.

Lemma in_SAimset (m n : nat) (x : 'rV[F]_n)
 (s : {SAset F^n}) (f : {SAfun F^n -> F^m}) :
  x \in s -> f x \in SAimset f s.
Proof.
rewrite pi_form /= => h.
have hsiz : m = size (ngraph (f x)) by rewrite size_ngraph.
rewrite [X in nquantify X _ _]hsiz.
apply/rcf_satP/nexistsP.
exists (ngraph x).
split; last first.
+ apply/holds_subst.
  move: h; rewrite inE.
  move/rcf_satP.
  rewrite -[ngraph (f x) ++ ngraph x]cats0.
  by rewrite -catA subst_env_iota // size_ngraph.
+ apply/holds_subst.
  move: h; rewrite inE.
  move/rcf_satP => h.
  rewrite subst_env_cat subst_env_iota_catl ?size_ngraph //.
  rewrite -[ngraph (f x) ++ ngraph x]cats0.
  rewrite -catA subst_env_iota ?size_ngraph //.
  move: (in_graph_SAfun f x); rewrite inE.
  by move/rcf_satP; rewrite ngraph_cat.
Qed.

Lemma SAimsetP (n m: nat) (f : {SAfun F^n -> F^m})
  (s : {SAset F^n}) (y : 'rV[F]_m) :
   reflect (exists2 x : 'rV[F]_n, x \in s & y = f x)
            (y \in (SAimset f s)).
Proof.
apply: (iffP idP); last by move=> [x h] ->; apply: in_SAimset.
rewrite /SAimset pi_form.
move/rcf_satP.
rewrite /= -[X in nquantify X _ _ _](size_ngraph y).
move/nexistsP => [t] /=.
rewrite !holds_subst subst_env_cat; move => [h1 h2].
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

(*
Definition SAset_setMixin :=
  SET.Semiset.Mixin SAemptyP inSAset1B sub_SAset1 non_empty
  le_sub SAunion SAimsetP.

Notation SemisetType set m :=
  (@SET.Semiset.pack _ _ set _ _ m _ _ (fun => id) _ id).
Canonical SAset_setType := SemisetType (fun n => {SAset F^n}) SAset_setMixin.
 *)
(* Import SET.Theory. *)
(* Definition SAset_setMixin := *)
(*   SemisetMixin SAemptyP inSAset1B sub_SAset1 non_empty *)
(*   le_sub SAunion SAimsetP. *)

(* Notation SemisetType set m := *)
(*   (@SET.Semiset.pack _ _ set _ _ m _ _ (fun => id) _ id). *)

Lemma in_SAfun (n m : nat) (f : {SAfun F^n -> F^m})
   (x : 'rV[F]_n) (y : 'rV[F]_m):
   (f x == y) = (row_mx x y \in SAgraph f).
Proof.
apply/eqP/idP => [<- | h]; first by rewrite in_graph_SAfun.
exact: (SAfun_func (in_graph_SAfun _ _)).
Qed.

Lemma SAfunE (n m : nat) (f1 f2 : {SAfun F^n -> F^m}) :
  reflect (f1 =1 f2) (f1 == f2).
Proof.
apply: (iffP idP); first by move/eqP ->.
move=> h; apply/SAsetP => x.
by rewrite -(cat_ffun_id x) -!in_SAfun h.
Qed.

Definition max_abs (k : nat) (x : 'rV[F]_k) :=
    \big[maxr/0]_(i < k) `|(x ord0 i)|.

Definition distance (k : nat) (x y : 'rV[F]_k) := max_abs (x - y).

Lemma max_vectP (k : nat) (x : 'rV[F]_k) (i :'I_k) : x ord0 i <= max_abs x.
Proof.
rewrite /max_abs; move: x i.
elim: k => [x [i lt_i0]| k ihk x i] //.
rewrite big_ord_recl le_max.
have [->|] := eqVneq i ord0; first by rewrite ler_norm.
rewrite eq_sym => neq_i0; apply/orP; right.
move: (unlift_some neq_i0) => /= [j lift_0j _].
move: (ihk (\row_(i < k) x ord0 (lift ord0 i)) j); rewrite mxE /=.
rewrite (eq_big predT (fun i => `|x ord0 (lift ord0 i)|)) //.
  by rewrite -lift_0j.
by move=> l _; rewrite mxE.
Qed.

Definition max_vec (v : seq nat) (n : nat) : formula F :=
    ((\big[Or/False]_(i < size v) ('X_n == 'X_(nth O v i))) /\
    (\big[And/True]_(i < size v) ('X_(nth O v i) <=% 'X_n)))%oT.

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
move : (in_graph_SAfun f (const_mx t`_i)); rewrite inE.
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
  move/holds_ngraph; rewrite -in_SAfun; move/eqP ->.
  by move/holds_ngraph; rewrite -in_SAfun; move/eqP ->.
+ move/eqP => eq_gfu_v.
  exists (ngraph (f u)).
  split; apply/holds_subst; rewrite subst_env_cat.
  - rewrite -catA subst_env_iota_catl; last by rewrite size_map size_enum_ord.
    rewrite catA subst_env_iota_catr ?size_tuple ?card_ord // -ngraph_cat.
    by apply/holds_ngraph; apply: in_graph_SAfun.
  - rewrite subst_env_iota_catr ?size_tuple ?card_ord //.
    rewrite -catA subst_env_iota; last 2 first.
      by rewrite size_map size_enum_ord.
    by rewrite size_map size_enum_ord.
    rewrite -ngraph_cat; apply/holds_ngraph; rewrite -eq_gfu_v.
    exact: in_graph_SAfun.
Qed.

Fact SAfun_SAcomp (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :
   (SAcomp_graph f g \in SAfunc) && (SAcomp_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/SAfuncE => x y1 y2; rewrite !SAcomp_graphP; move=> /eqP-> /eqP->.
by apply/SAtotE => x; exists (g (f x)); rewrite SAcomp_graphP.
Qed.

Definition SAcomp (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :=
    MkSAfun (SAfun_SAcomp f g).

Lemma SAcompP (m n p : nat) (f : SAfun F m n) (g : SAfun F n p) :
    SAcomp f g =1 g \o f.
Proof.
move=> x; apply/eqP; rewrite eq_sym -SAcomp_graphP.
by move: (in_graph_SAfun (SAcomp f g) x).
Qed.

End SASetTheory.

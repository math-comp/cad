Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div fintype tuple.
From mathcomp
Require Import finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
From mathcomp
Require Import poly polydiv mxpoly.
From mathcomp
Require ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Monoid.Theory.
Import Pdiv.Idomain.

(* Four extra result sections for: nat, perm, polydiv, matrix and mxpoly. *)

(* perm_rev and perm_circle *)
(* take and drop of polynomials *)
(* lcm and its properties       *)

(*****************************************************************************)

Section extra_nat.

Lemma leq_gtF m n : m <= n -> n < m = false.
Proof. by rewrite leqNgt; case: ltngtP. Qed.

End extra_nat.

Section extra_perm.

From mathcomp Require Import fintype finfun finset perm zmodp div binomial.

(* Remark: generalize (D : {set aT}) to (D : pred_class_of aT) in finset.v *)
(* Meanwhile, we reprove it in this more general case *)
Notation pred_class_of T := (pred_sort (predPredType T)).
Lemma pred_class_eq_imset (aT rT : finType) (f g : aT -> rT)
  (D : pred_class_of aT) :
  f =1 g -> [set f x | x in D] = [set g x | x in D].
Proof.
move=> eqfg; apply/setP=> y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Definition perm_rev {n} : 'S_n := perm rev_ord_inj.

Lemma perm_rev0 : @perm_rev 0 = 1%g.
Proof. by apply/permP => [[]]. Qed.

Lemma perm_rev1 : @perm_rev 1 = 1%g.
Proof. by apply/permP => x /=; rewrite !ord1. Qed.

Lemma perm_circle_proof n :
  injective ((fun k : 'I_n => insubd k (if k.+1 < n then k.+1 else 0%N))).
Proof.
move=> x y /= eq_xy; apply: val_inj => /=; have {eq_xy} := congr1 val eq_xy.
rewrite !val_insubd /=.
have [x_lt|] := ltnP x.+1 _; have [y_lt|] := ltnP y.+1 _;
rewrite ?x_lt ?y_lt ?(ltn_trans _ y_lt) ?(ltn_trans _ x_lt) //; first by case.
case: ifP=> // _; rewrite ![n <= _]leq_eqVlt ![_ < _.+1]ltnNge !ltn_ord !orbF.
by move=> /eqP {1}-> /eqP [].
Qed.

Definition perm_circle n : 'S_n := perm (@perm_circle_proof n).

Lemma pcycle_perm_circle n x : pcycle (perm_circle n) x = setT.
Proof.
apply/setP => y /=; rewrite in_setT.
wlog le_xy : x y / x <= y => /= [hwlog|].
  by have /orP[/hwlog//|/hwlog] := leq_total x y; rewrite pcycle_sym.
suff -> : y = ((perm_circle n) ^+ (y - x))%g x by rewrite mem_pcycle.
rewrite permX; apply: val_inj => /=.
move: (ltn_ord y); set d := (y - x)%N; rewrite -(subnK le_xy) -/d.
elim: d => //= d ihd; rewrite addSn => hd.
by rewrite permE -ihd ?val_insubd ?(hd, ltnW hd).
Qed.

Definition imset_const (aT rT : finType) (A : pred_class_of aT)
  (a : aT) (x : rT) : (a \in A) -> [set x | _ in A] = [set x].
Proof.
move=> Ha; apply/setP=> y; rewrite in_set1.
by apply/imsetP/eqP => [[//]|->]; last exists a.
Qed.
Arguments imset_const {_ _ _} a [x] _.

Lemma pcycles_perm_circle n : pcycles (perm_circle n.+1) = [set setT].
Proof.
rewrite /pcycles /= (pred_class_eq_imset _ (@pcycle_perm_circle n.+1)) /=.
by apply/setP => /= x; rewrite (imset_const ord0).
Qed.

Lemma perm_circle0 : perm_circle 0%N = 1%g.
Proof. by apply/permP => [[]]. Qed.

Lemma odd_perm_circle n : perm_circle n.+1 = odd n :> bool.
Proof.
by rewrite /odd_perm pcycles_perm_circle card_ord cards1 addbT negbK.
Qed.

Lemma odd_perm_rev n : @perm_rev n = odd 'C(n, 2) :> bool.
Proof.
elim: n => [|/= n ihn]; first by rewrite perm_rev0 odd_perm1.
suff -> : perm_rev = (perm_circle n.+1 * lift0_perm perm_rev)%g.
  rewrite odd_permM odd_lift_perm /= ihn => {ihn}.
  by rewrite odd_perm_circle /= binS bin1 odd_add addbC.
apply/permP => i /=; apply/val_inj; do !rewrite !permE /=.
rewrite /lift_perm_fun /= subSS ltnS.
case: unliftP => /= [j|] /(congr1 val) /=; last first.
  by rewrite val_insubd ltnS; have [-> //|/eqP-> //] := ltnP.
rewrite !val_insubd permE /bump !leq0n !add1n /= !ltnS.
have [i_lt <-|//] := ltnP; first by rewrite i_lt subnSK.
Qed.

Lemma perm_rev2 n : (perm_rev * perm_rev)%g = 1%g :> 'S_n.
Proof.
apply/permP => i; apply: val_inj.
by rewrite permM !permE /= subnSK // subKn // ltnW.
Qed.

Lemma perm_revV n : perm_rev^-1%g = perm_rev :> 'S_n.
Proof. by apply/eqP; rewrite eq_invg_mul perm_rev2. Qed.

End extra_perm.

Section bin2.
Import ssrint.IntDist.

Lemma bin2D m n : 'C(m + n, 2) = 'C(m, 2) + 'C(n, 2) + m * n.
Proof.
case: m => [|m] //=; rewrite bin2 !addSn /= mulnDr -{1}addSn -addnS !mulnDl.
rewrite [n * m]mulnC [X in X + _]addnC addnACA addnn.
rewrite halfD !odd_double /= doubleK halfD !odd_mul !andNb !add0n addnC.
by rewrite -!bin2 ['C(n.+1, 2)]binS bin1 mulSn !addnA.
Qed.

Lemma odd_bin2M2 n : odd 'C(n.*2, 2) = odd n.
Proof.
rewrite bin2 -{1}mul2n -mulnA mul2n doubleK odd_mul.
by case: n => //= n; rewrite odd_double andbT.
Qed.

Lemma odd_bin2D2n k n : odd 'C(k.*2 + n, 2) = (odd k (+) odd 'C(n, 2)).
Proof. by rewrite bin2D !odd_add odd_bin2M2 -doubleMl odd_double addbF. Qed.

Lemma bin2DB m n : odd 'C(m + n, 2) = odd (minn m n) (+) odd 'C(`|m - n|, 2).
Proof.
wlog le_nm : n m / n <= m => [hwlog|].
  by have /orP [/hwlog//|/hwlog] := leq_total n m; rewrite addnC distnC minnC.
rewrite -{1}(subnK le_nm) -addnA addnn addnC odd_bin2D2n.
by rewrite distnEl ?(minn_idPr _) ?leq_addl.
Qed.

Lemma odd_bin2_dist (m n : nat) :
  odd 'C(`|m - n|, 2) = odd (minn m n) (+) odd 'C(m + n, 2).
Proof. by rewrite bin2DB addbA addbb. Qed.

Lemma odd_bin2B m n : n <= m -> odd 'C(m - n, 2) = odd n (+) odd 'C(m + n, 2).
Proof. by move=> le_nm; rewrite -distnEl // odd_bin2_dist (minn_idPr _). Qed.

Lemma bin2B_trans n p m : p <= n <= m ->
   'C(m - p, 2) = 'C(m - n, 2) + 'C(n - p, 2) + (m - n) * (n - p).
Proof.
move=> /andP [pn nm]; rewrite -[m - p](@subnK (n - p)%N) ?leq_sub //.
by rewrite  bin2D subnBA ?subnK ?(leq_trans pn).
Qed.

End bin2.

Local Open Scope ring_scope.

Section extra_polydiv.
Import Pdiv.IdomainUnit Pdiv.Idomain.
Variable R : idomainType.

Lemma Poly_take_drop n (p : {poly R}) :
   (Poly (take n p) = p %% 'X^n) * (Poly (drop n p) = p %/ 'X^n).
Proof.
suff: Poly (drop n p) * 'X^n + Poly (take n p) = p.
  have: size (Poly (take n p)) < size ('X^n : {poly R}).
    rewrite (leq_ltn_trans (size_Poly _)) //.
    by rewrite size_take size_polyXn ltnS; case: ltnP.
  move: (drop _ _) (take _ _) => d t st <-.
  by rewrite modp_addl_mul_small ?divp_addl_mul_small // lead_coefXn unitr1.
have [spn|spn] := leqP (size p) n.
  by rewrite drop_oversize // mul0r add0r take_oversize // polyseqK.
apply/polyP => i /=; rewrite coef_add_poly polyseqMXn; last first.
  rewrite -(inj_eq val_inj) /=.
  have p_neq0 : p != 0 by rewrite -size_poly_gt0 (leq_trans _ spn).
  suff: (Poly (drop n p))`_((size p).-1 - n) != 0.
    by apply: contraNneq => ->; rewrite coef0.
  rewrite coef_Poly nth_drop subnKC ?lead_coef_eq0 //.
  by rewrite -ltnS (leq_trans spn) // leqSpred.
rewrite nth_ncons !coef_Poly nth_drop.
have [leni|ltin] := leqP; last  by rewrite nth_take // add0r.
by rewrite subnKC // addrC nth_default ?add0r // size_take spn.
Qed.

Lemma Poly_take (p : {poly R}) n : Poly (take n p) = p %% 'X^n.
Proof. by rewrite Poly_take_drop. Qed.

Lemma Poly_drop (p : {poly R}) n : Poly (drop n p) = p %/ 'X^n.
Proof. by rewrite Poly_take_drop. Qed.

Definition lcmp (p q : {poly R}) := (p * q) %/ gcdp p q.

Lemma mulp_gcd_lcm (p q : {poly R}) :
  gcdp p q * lcmp p q =
  lead_coef (gcdp p q) ^+ scalp (p * q) (gcdp p q) *: (p * q).
Proof. by rewrite divpKC ?dvdp_mull ?dvdp_gcdr. Qed.

Lemma lcm0p (p : {poly R}) : lcmp 0 p = 0.
Proof. by rewrite /lcmp mul0r div0p. Qed.

Lemma lcmp0 (p : {poly R}) : lcmp p 0 = 0.
Proof. by rewrite /lcmp mulr0 div0p. Qed.

Lemma lcmp_eq0 (p q : {poly R}) : (lcmp p q == 0) = (p == 0) || (q == 0).
Proof.
rewrite /lcmp divp_eq0 gcdp_eq0 orb_idr ?mulf_eq0 //.
move=> /orP [/andP [-> //]|]; do 2!have [//|?] := altP eqP.
by rewrite ltnNge dvdp_leq ?mulf_neq0 // dvdp_mull ?dvdp_gcdr.
Qed.

Lemma dvdp_lcml (p q : {poly R}) : p %| lcmp p q.
Proof.
have [->|p0] := eqVneq p 0; first by rewrite lcm0p.
rewrite -(@dvdp_mul2l _ (gcdp p q)) ?gcdp_eq0 ?(negPf p0) // mulp_gcd_lcm.
by rewrite dvdp_scaler ?lc_expn_scalp_neq0 // mulrC dvdp_mul ?dvdp_gcdr.
Qed.

Lemma dvdp_lcmr (p q : {poly R}) : q %| lcmp p q.
Proof.
have [->|p0] := eqVneq p 0; first by rewrite lcm0p dvdp0.
rewrite -(@dvdp_mul2l _ (gcdp p q)) ?gcdp_eq0 ?(negPf p0) // mulp_gcd_lcm.
by rewrite dvdp_scaler ?lc_expn_scalp_neq0 ?dvdp_mul ?dvdp_gcdl.
Qed.

Lemma dvdp_lcm (p q r : {poly R}) : (lcmp p q %| r) = (p %| r) && (q %| r).
Proof.
have [->|p0] := eqVneq p 0; first by rewrite lcm0p dvd0p andb_idr => // /eqP->.
have [->|q0] := eqVneq q 0; first by rewrite lcmp0 dvd0p andb_idl => // /eqP->.
rewrite -(@dvdp_mul2l _ (gcdp p q)) ?gcdp_eq0 ?(negPf p0) // mulp_gcd_lcm.
rewrite dvdp_scalel ?lc_expn_scalp_neq0 // -(eqp_dvdr _ (gcdp_mul2r _ _ _)).
by rewrite dvdp_gcd dvdp_mul2l // mulrC dvdp_mul2l // andbC.
Qed.

Lemma size_lcm (p q : {poly R}) : p != 0 -> q != 0 ->
  size (lcmp p q) = ((size (p * q)%R).+1 - size (gcdp p q))%N.
Proof.
move=> p0 q0; rewrite -(size_scale _ (lc_expn_scalp_neq0 (p * q) (gcdp p q))).
rewrite -mulp_gcd_lcm size_mul ?gcdp_eq0 ?lcmp_eq0 ?(negPf p0) //.
rewrite prednK addnC ?addnK //.
by rewrite ltn_addl ?size_poly_gt0 ?gcdp_eq0 ?(negPf p0).
Qed.

Lemma size_gcd (p q : {poly R}) : p != 0 -> q != 0 ->
  size (gcdp p q) = ((size (p * q)%R).+1 - size (lcmp p q))%N.
Proof.
move=> p_neq0 q_neq0; rewrite size_lcm // subnBA 1?addnC ?addnK //.
by rewrite leqW // dvdp_leq ?mulf_neq0 ?dvdp_mull ?dvdp_gcdr.
Qed.

End extra_polydiv.

Notation perm_rev_mx := (perm_mx perm_rev).
Section extra_matrix.

Lemma mulmxP (K : ringType) (m n : nat) (A B : 'M[K]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply: (iffP eqP) => [-> //|eqAB]; apply/matrixP => i j.
by have := eqAB (delta_mx 0 i) => /rowP - /(_ j); rewrite -!rowE !mxE.
Qed.

Lemma lsubmx_col (R : Type) (m n p k: nat)
  (A : 'M[R]_(m, p + k)) (B : 'M[R]_(n, p + k)) :
  lsubmx (col_mx A B) = col_mx (lsubmx A) (lsubmx B).
Proof. by apply/matrixP=> i j; rewrite !mxE; case: split => l; rewrite mxE. Qed.

Lemma rsubmx_col (R : Type) (m n p k: nat)
  (A : 'M[R]_(m, p + k)) (B : 'M[R]_(n, p + k)) :
  rsubmx (col_mx A B) = col_mx (rsubmx A) (rsubmx B).
Proof. by apply/matrixP=> i j; rewrite !mxE; case: split => l; rewrite mxE. Qed.

Lemma usubmx_row (R : Type) (m n p k: nat)
  (A : 'M[R]_(m + n, p)) (B : 'M[R]_(m + n, k)) :
  usubmx (row_mx A B) = row_mx (usubmx A) (usubmx B).
Proof. by apply/matrixP=> i j; rewrite !mxE; case: split => l; rewrite mxE. Qed.

Lemma dsubmx_row (R : Type) (m n p k: nat)
  (A : 'M[R]_(m + n, p)) (B : 'M[R]_(m + n, k)) :
  dsubmx (row_mx A B) = row_mx (dsubmx A) (dsubmx B).
Proof. by apply/matrixP=> i j; rewrite !mxE; case: split => l; rewrite mxE. Qed.

Lemma mulmx_lsub (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m lsubmx B = (lsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_rsub (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m rsubmx B = (rsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_usub (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m + n, p)) (B : 'M[R]_(p, k)) :
  usubmx A *m B = (usubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_dsub (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m + n, p)) (B : 'M[R]_(p, k)) :
  dsubmx A *m B = (dsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_perm_rev_col (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m, p + k)) (B : 'M[R]_(n, p + k)) :
  perm_rev_mx *m col_mx A B =
  castmx (addnC _ _,erefl) (col_mx (perm_rev_mx *m B) (perm_rev_mx *m A)).
Proof.
apply/matrixP => i j; rewrite !(castmxE, mxE) big_split_ord /=.
case: splitP => [] l /= Hl; rewrite mxE.
  rewrite big1 ?add0r; last first.
    move=> x _; rewrite !mxE -!val_eqE permE /= Hl.
    by rewrite gtn_eqF ?mul0r // -addnBA ?ltn_addr.
  apply: eq_bigr => x _; rewrite !mxE.
  rewrite -!val_eqE /= !permE /= Hl -addnBA // eqn_add2l.
  case: splitP=> [y Hy|y /addnI Hy]; last by congr (_ * B _ _); apply: val_inj.
  by move: (ltn_ord y); rewrite -Hy -ltn_subRL subnn ltn0.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> x _; rewrite !mxE -!val_eqE permE /= Hl.
  rewrite addnC -addnS subnDl ltn_eqF ?mul0r //.
  by rewrite -subn_gt0 subnBA // -addnA addnC addnK addnS.
apply: eq_bigr => x _; rewrite !mxE.
rewrite -!val_eqE /= !permE /= Hl addnC -addnS subnDl.
case: splitP => [y Hy|y /= Hy]; first by congr (_ * A _ _); apply: val_inj.
by move: (ltn_ord x); rewrite Hy -ltn_subRL subnn ltn0.
Qed.

Lemma mulmx_row_perm_rev (R : ringType) (m n p k: nat)
  (A : 'M[R]_(m + n, p)) (B : 'M[R]_(m + n, k)) :
  row_mx A B *m perm_rev_mx =
  castmx (erefl,addnC _ _) (row_mx (B *m perm_rev_mx) (A *m perm_rev_mx)).
Proof.
apply: trmx_inj; rewrite trmx_cast /= !(tr_row_mx, trmx_mul_rev).
by rewrite !tr_perm_mx !perm_revV mulmx_perm_rev_col.
Qed.

End extra_matrix.

Section extra_mxpoly.

Lemma rsubmx_poly_rV (R : idomainType) (m n: nat) (p : {poly R}):
  rsubmx (poly_rV p : 'rV_(m + n)) = poly_rV (p %/ 'X^m).
Proof. by apply/rowP => i; rewrite !mxE -Poly_drop coef_Poly nth_drop. Qed.

Lemma lsubmx_poly_rV (R : idomainType) (m n: nat) (p : {poly R}):
  lsubmx (poly_rV p : 'rV_(m + n)) = poly_rV (p %% 'X^m).
Proof. by apply/rowP => i; rewrite !mxE -Poly_take coef_Poly nth_take. Qed.

Lemma poly_rV_eq0 (R : ringType) n (p : {poly R}) :
  size p <= n -> (poly_rV p == 0 :> 'rV[R]_n) = (p == 0).
Proof.
move=> spn; apply/eqP/eqP; last by move->; rewrite linear0.
by move=> /(congr1 rVpoly); rewrite linear0 poly_rV_K.
Qed.

End extra_mxpoly.

Section extra_int.

Import ssrint ssrnum.
Import Num.Theory.

Lemma sgz_gt0Blt0 (R : realDomainType) (x : R) :
   sgz x = (0 < x)%R%:Z - (x < 0)%R%:Z.
Proof. by case: sgzP. Qed.

Lemma sgr_gt0Blt0 (R : realDomainType) (x : R) :
   Num.sg x = (0 < x)%R%:R - (x < 0)%R%:R.
Proof. by case: sgrP; rewrite ?subr0 ?sub0r ?mulr1n. Qed.

End extra_int.

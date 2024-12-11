From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq order.
From mathcomp Require Import div fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import ssralg zmodp matrix mxalgebra interval binomial.
From mathcomp Require Import ssrint poly polydiv mxpoly ssrnum.
From mathcomp Require Import polyorder polyrcf qe_rcf_th.

Require Import extra_ssr auxresults.

(***************************************************************************)
(* The statements and proofs in this file are largely inpired by BPR       *)
(* (http://perso.univ-rennes1.fr/marie-francoise.roy/bpr-ed2-posted2.html) *)
(*                                                                         *)
(*  SylvesterHabitch_mx p q j == a variant of the Sylvester-Habitch matrix *)
(*                               (cf comment below)                        *)
(*         subresultant p q j == a variant of the subresultant             *)
(***************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Monoid.Theory Pdiv.Idomain Order.POrderTheory.
Local Open Scope ring_scope.

(**************************************************************************)
(* About Permanence Minus Variations                                      *)
(*                                                                        *)
(* Remark, what is called /variations/ in BPR, we call it /changes/.      *)
(* Instead, what we call variation witnesses a strict sign change and was *)
(* defined in qe_rcf_th.                                                  *)
(**************************************************************************)

Module Import PMV.
Section PMV.
(* part of it should be backported to polyrcf/qe_rcf_th *)
(* and generalized to numDomainType *)

Import Num.Theory. (* This stays in the module PMV *)

Lemma variationrr (R : rcfType) (x : R) : variation x x = 0.
Proof.
rewrite /variation real_ltNge// ?sqr_ge0 ?mulr0//.
by apply/rpredM; apply/num_real.
Qed.

Lemma variationE (R : rcfType) (y x : R) :
  variation x y != 0 -> variation x y = sgz y.
Proof. by rewrite /variation -sgz_lt0 sgzM; do 2!case: sgzP. Qed.

Lemma variation_eq0 (R : rcfType) (x y : R) :
  (variation x y == 0) = (x * y == 0) || (sgz x == sgz y).
Proof.
by rewrite /variation -sgz_lt0 !sgzM !mulf_eq0 eqz_nat eqb0; do 2!case: sgzP.
Qed.

Lemma variation_neq0 (R : rcfType) (x y : R) :
  (variation x y != 0) = (x != 0) && (y != 0) && (sgz x == - sgz y).
Proof. by rewrite variation_eq0 mulf_eq0; do 2!case: sgzP. Qed.

Lemma novariation_sgz (R : rcfType) (y x : R) :
  x != 0 -> y != 0 -> variation x y = 0 -> sgz x = sgz y.
Proof.
move=> x0 y0 /eqP; rewrite variation_eq0.
by rewrite mulf_eq0 (negPf x0) (negPf y0) => /= /eqP.
Qed.

Lemma variationNr (R : rcfType) (x y : R) :
  variation (- x) y = sgz y * (x != 0) * (variation x y == 0).
Proof.
rewrite variation_eq0 mulf_eq0 /variation mulNr oppr_lt0 -sgz_gt0 sgzM.
by do 2!case: sgzP.
Qed.

Lemma variationrN (R : rcfType) (x y : R) :
  variation x (- y) = - sgz x * (y != 0) * (variation x y == 0).
Proof. by rewrite variationC variationNr !mulNr variationC oppr_eq0. Qed.

Lemma variation_sgzLR (R : rcfType) (y x : R) :
  variation x y != 0 -> sgz x = - sgz y.
Proof. by rewrite variation_neq0 => /andP[_ /eqP->]. Qed.

Lemma variation_neq0l (R : rcfType) (y x : R) :
  variation x y != 0 -> x != 0.
Proof. by rewrite variation_neq0=> /andP[/andP[]]. Qed.

Lemma variation_neq0r (R : rcfType) (x y : R) :
  variation x y != 0 -> y != 0.
Proof. by rewrite variation_neq0=> /andP[/andP[]]. Qed.

Lemma variationNrr (R : rcfType) (x : R) : variation (- x) x = sgz x.
Proof. by rewrite variationNr variationrr; case: sgzP. Qed.

Lemma variationrNr (R : rcfType) (x : R) : variation x (- x) = - sgz x.
Proof. by rewrite variationrN variationrr; case: sgzP. Qed.

Lemma crossRE (R : rcfType) (p : {poly R}) :
  crossR p = sgz (lead_coef p) *+ (odd (size p).-1).
Proof.
rewrite /crossR /sgp_minfty /sgp_pinfty -signr_odd.
case: odd; rewrite /= (mulN1r, mul1r) ?sgrN.
  by rewrite variationNrr sgz_sgr mulr1n.
by rewrite variationrr mulr0n.
Qed.

(* Notation 4.30. from BPR *)
Fixpoint pmv_aux (R : numDomainType) (a : R) (n : nat) (s : seq R) :=
  if s is b :: s then
    if b == 0 then pmv_aux a n.+1 s
    else pmv_aux b 0%N s + (-1) ^+ 'C(n, 2) * sgz (a * b) *+ ~~ (odd n)
  else 0.
Definition pmv (R : numDomainType) (s : seq R) : int :=
  if s is a :: s then pmv_aux a 0%N s else 0.
Arguments pmv : simpl never.

Notation nonzero := (forall x, x != 0).

Lemma pmv_cat0s (R : numDomainType) (a b : R) (s0 s : seq R) :
  b != 0 -> {in s0, forall x, x == 0} ->
  pmv (a :: s0 ++ b :: s) =
    pmv (b :: s) + (-1) ^+ 'C(size s0, 2) * sgz (a * b) *+ ~~ odd (size s0).
Proof.
move=> /negPf b0 s00; rewrite /pmv -[size s0]/(0 + size s0)%N.
move: {1 3 5}0%N => n; elim: s0 n s00 => [|x s0 IHs0] n s00.
  by rewrite /= b0 addn0.
rewrite /= s00 ?mem_head// addnS -addSn IHs0// => y ys0.
by apply/s00; rewrite in_cons ys0 orbT.
Qed.

Lemma pmv_cat00 (R : numDomainType) (a : R) (s0 : seq R) :
  {in s0, forall x, x == 0} -> pmv (a :: s0) = 0.
Proof.
rewrite /pmv /=; move: 0%N.
elim: s0 => //= b s0 IHs0 n bs0.
rewrite bs0 ?mem_head// IHs0// => i is0.
by apply/bs0; rewrite in_cons is0 orbT.
Qed.

Lemma pmv_0s (R : numDomainType) (s : seq R) :
  pmv (0 :: s) = pmv s.
Proof.
rewrite /pmv/=; move: {1}0%N.
elim: s => // x s IHs n /=.
have [->|_] := eqVneq x 0; first by rewrite !IHs.
by rewrite mul0r sgz0 mulr0 mul0rn addr0.
Qed.

Lemma pmv_s0 (R : numDomainType) (s : seq R) :
  pmv (rcons s 0) = pmv s.
Proof.
rewrite /pmv; case: s => // x s /=.
elim: s x 0%N => [|y s IHs] /= x n; first by rewrite eqxx.
case: (y == 0); first exact: IHs.
by congr (_ + _); apply: IHs.
Qed.

Lemma pmv_sgz (R : realDomainType) (s : seq R) :
  pmv [seq sgz x | x <- s] = pmv s.
Proof.
rewrite /pmv; case: s => // a s /=.
elim: s a 0%N => // a s IHs b k/=.
by rewrite sgz_eq0 !IHs !sgzM !sgz_id.
Qed.

Lemma eq_pmv (R : realDomainType) (s t : seq R) :
  all2 (fun x y => sgz x == sgz y) s t -> pmv s = pmv t.
Proof.
move=> st; rewrite -pmv_sgz -(pmv_sgz t); congr pmv; apply/eqP.
rewrite eqseq_all; elim: s t st => [|x s IHs]; case=> //= y t /andP[xy] st.
by apply/andP; split=> //; apply/IHs.
Qed.

Lemma pmv_opp (R : numDomainType) (s : seq R) :
  pmv [seq - x | x <- s] = pmv s.
Proof.
rewrite /pmv; case: s => // a s /=.
elim: s a 0%N => // a s IHs b k/=.
by rewrite oppr_eq0 !IHs mulrNN.
Qed.

Lemma pmvZ (R : realDomainType) (a : R) (s : seq R) :
  a != 0 -> pmv [seq a * x | x <- s] = pmv s.
Proof.
rewrite /pmv; case: s => // x s /= /negPf a0.
elim: s x 0%N => // x s IHs y k/=.
rewrite mulf_eq0 a0/= !IHs mulrACA sgzM -expr2 sgzX.
suff ->: sgz a ^+ 2 = 1 by rewrite mul1r.
rewrite /sgz a0/=; case: (a < 0); last exact/expr1n.
by rewrite -signr_odd/= expr0.
Qed.

Fixpoint permanences (R : numDomainType) (s : seq R) : nat :=
  (if s is a :: q then (a * (head 0 q) > 0)%R + permanences q else 0)%N.

(* First remark about Notation 4.30 in BPR *)
Lemma nonzero_pmvE (R : rcfType) (s : seq R) :
  {in s, nonzero} -> pmv s = (permanences s)%:Z - (changes s)%:Z.
Proof.
rewrite /pmv; case: s => // a s /=.
elim: s a => [|b s ihs] a s_neq0; first by rewrite /= mulr0 subrr.
rewrite /= (negPf (s_neq0 _ _)); last by rewrite in_cons mem_head orbT.
rewrite mul1r ihs; last by move=> x Hx; rewrite /= s_neq0 // in_cons Hx orbT.
by rewrite !PoszD !opprD [in RHS]addrACA -sgz_gt0Blt0 addrC.
Qed.

Lemma changes_minftyE (R : rcfType) (sp : seq {poly R}) :
  (forall i, (size sp`_i.+1) = (size sp`_i).-1) ->
  changes_minfty sp = permanences (map lead_coef sp).
Proof.
rewrite /changes_minfty; elim: sp => //= p sp ihsp size_sp.
rewrite ihsp => {ihsp}; last by move=> i; have := size_sp i.+1.
congr (_ + _)%N; case: sp => [|q sq] /= in size_sp *; first by rewrite !mulr0.
rewrite mulr_signM (size_sp 0%N) /=.
have [->|p_neq0]:= eqVneq p 0; first by rewrite lead_coef0 mul0r mulr0.
by rewrite polySpred //= negbK addbN addbb mulN1r oppr_lt0.
Qed.

(* Second remark about Notation 4.30 in BPR *)
Lemma pmv_changes_poly (R : rcfType) (sp : seq {poly R}) :
  {in sp, nonzero} -> (forall i, (size sp`_i.+1) = (size sp`_i).-1) ->
  pmv (map lead_coef sp) = changes_poly sp.
Proof.
move=> sp_neq0 size_sp; rewrite nonzero_pmvE; last first.
  by move=> c /mapP [p /sp_neq0 p_neq0 ->]; rewrite lead_coef_eq0.
by rewrite /changes_poly changes_minftyE.
Qed.

End PMV.
End PMV.

(*************************************************)
(* Here begins the development on subresultants. *)
(*************************************************)
Local Notation band r := (lin1_mx (poly_rV \o r \o* rVpoly)).
Section SubResultant.

Variables (R : ringType) (np nq k : nat) (p q : {poly R}).

Lemma band0 n m :
  band 0  = 0 :> 'M[R]_(n, m).
Proof. by apply/matrixP => i j; rewrite !mxE/= mulr0 polyseq0 nth_nil. Qed.

(**************************************************************************)
(* We define the SylvesterHabitch_mx in this way, in order to be able to  *)
(* reuse the poly_rV and rVpoly mappings rather than redefining custom    *)
(* ones in big endian encoding and reversing some rows of the matrix when *)
(* reasonning about the nullity of its determinant.  Instead, we apply    *)
(* the row reversal of the lower part of the matrix in the definition of  *)
(* the subresultant, and we also correct the sign.                        *)
(*                                                                        *)
(* Note also that the matrix is generalized to arbitrary sizes. Although  *)
(* it makes sense only with the instanciations given in the definition of *)
(* the subresultant, this helps stating various lemmas without any casts  *)
(* (cf SylvesterHabicht_mod and SylvesterHabicht_scaler) or only one      *)
(* (cf SylvesterHabicht_reduce)                                           *)
(**************************************************************************)

Definition SylvesterHabicht_mx : 'M[R]_(np + nq, k) :=
  col_mx (band p) (band q).

Lemma SylvesterHabicht_mxE (m : 'I_(np + nq)) (n : 'I_k):
  let S_ r k := r`_(n - k) *+ (k <= n) in
  SylvesterHabicht_mx m n =
  match split m with inl k => S_ p k | inr k => S_ q k end.
Proof.
move=> S_; rewrite mxE; case: {m}(split m) => m; rewrite !mxE /=;
by rewrite rVpoly_delta coefXnM ltnNge if_neg -?mulrb.
Qed.

End SubResultant.

Lemma det_rsub_band (R : comRingType) m n (p : {poly R}) :
  (size p).-1 = n ->
  \det (rsubmx (band p : 'M_(m, n + m))) = lead_coef p ^+ m.
Proof.
move <-; elim: m => [|m ihm] //; first by rewrite det_mx00 expr0.
rewrite exprS -add1n -[X in \det X]submxK.
rewrite [X in block_mx X _ _ _]mx11_scalar.
rewrite !mxE /= rVpoly_delta /= expr0 mul1r addn0 -lead_coefE.
set ur := ursubmx _; have -> : ur = 0.
  apply/matrixP=> i j; rewrite !mxE/= !rVpoly_delta/= !add1n ord1 expr0 mul1r.
  by rewrite nth_default // addnS -addn1 addnC -leq_subLR subn1 leq_addr.
rewrite det_lblock det_scalar expr1 -ihm; congr (_ * \det _).
apply/matrixP => i j; rewrite !mxE /= !rVpoly_delta /= !add1n addnS.
by rewrite !coefXnM ltnS subSS.
Qed.

(* Note: it is unclear yet whether the appropriate formulation is *)
(* ((size q).-1 - j) or (size q - j.+1)                  -- Cyril *)
Definition subresultant (R : ringType) j (p q : {poly R}) :=
  if (j <= (size p).-1)%N && (j <= (size q).-1)%N then
    let nq := ((size p).-1 - j)%N in let np := ((size q).-1 - j)%N in
    (- 1) ^+ 'C(np + nq, 2) *
    \det (rsubmx ((block_mx perm_rev_mx 0 0 1%:M) *m
                SylvesterHabicht_mx np nq (j + (np + nq)) p q))
  else if j == (size p).-1 then lead_coef p
  else if j == (size q).-1 then lead_coef q
  else 0.

Lemma subresultantE (R : comRingType) j (p q : {poly R}) :
  (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  let np := ((size p).-1 - j)%N in let nq := ((size q).-1 - j)%N in
  subresultant j p q =
  (-1) ^+ ('C(nq + np, 2) + 'C(nq, 2)) *
  \det (rsubmx (SylvesterHabicht_mx nq np (j + (nq + np)) p q)).
Proof.
rewrite /subresultant /SylvesterHabicht_mx => -> -> /=.
rewrite -mulmx_rsub det_mulmx det_ublock det1 mulr1.
by rewrite det_perm odd_perm_rev signr_odd exprD mulrA.
Qed.

Remark subresultant0 (R : comRingType) (p q : {poly R}) :
  subresultant 0 p q =
  (-1) ^+ ('C((size q).-1 + (size p).-1, 2) + 'C((size q).-1, 2)) *
  resultant p q.
Proof.
rewrite /resultant /Sylvester_mx subresultantE// /SylvesterHabicht_mx !subn0.
move: (col_mx _ _) => x; congr (_ * \det _).
by apply/matrixP => i j /=; rewrite !mxE; congr (x _ _); apply: val_inj.
Qed.

Lemma subresultant_eq0 (R : comRingType) j (p q : {poly R}) :
  (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  let np := ((size p).-1 - j)%N in let nq := ((size q).-1 - j)%N in
  (subresultant j p q  == 0) =
  (\det (rsubmx (SylvesterHabicht_mx nq np (j + (nq + np)) p q)) == 0).
Proof.
move=> jp jq; rewrite subresultantE// -signr_odd mulr_sign; case: ifP => //.
by rewrite oppr_eq0.
Qed.

(* Remark 4.23. from BPR *)
Lemma SylvesterHabicht_mxP (R : ringType) (np nq k : nat)
  (p q u v : {poly R}) : (size u <= np)%N -> (size v <= nq)%N ->
  row_mx (poly_rV u) (poly_rV v) *m SylvesterHabicht_mx np nq k p q
                                    = poly_rV (u * p + v * q).
Proof.
by move=> su sv; rewrite mul_row_col !mul_rV_lin1 /= !poly_rV_K // -linearD.
Qed.

Lemma lsubmx_SylvesterHabicht (R : ringType)
      (np nq k1 k2 : nat) (p q : {poly R}) :
  lsubmx (SylvesterHabicht_mx nq np (k1 + k2) p q) =
  SylvesterHabicht_mx nq np k1 p q.
Proof.
by apply/matrixP=> i j; rewrite !(mxE, SylvesterHabicht_mxE); case: split.
Qed.

(* Lemma 4.24. from BPR, not so trivial because            *)
(* row_mx u v != 0 is not equivalent to u != 0 and v != 0) *)
Lemma subresultantP (R : idomainType) j (p q : {poly R}) :
  p != 0 -> q != 0 -> (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  reflect (exists2 u : {poly R} * {poly R},
                      (0 < size u.1 <= (size q).-1 - j)%N
                   && (0 < size u.2 <= (size p).-1 - j)%N
                    & size (u.1 * p + u.2 * q)%R <= j)%N
          (subresultant j p q == 0).
Proof.
have Xj_neq0 : 'X^j != 0 :> {poly R} by rewrite monic_neq0 ?monicXn.
move=> p0 q0 le_jp le_jq; rewrite subresultant_eq0//.
apply: (iffP det0P) => [[r]|[[u v] /= /andP [su sv] s_upvq]]; last first.
  move: su sv; rewrite !size_poly_gt0 => /andP [u_neq0 su] /andP [v_neq0 sv].
  exists (row_mx (poly_rV u) (poly_rV v)).
    rewrite -[0]hsubmxK; apply: contraTneq (sv) => /eq_row_mx.
    by rewrite !linear0 => [[_ /eqP]]; rewrite poly_rV_eq0 ?(negPf v_neq0).
  rewrite mulmx_rsub SylvesterHabicht_mxP // rsubmx_poly_rV.
  set r := (X in poly_rV X); suff -> : r = 0 by rewrite linear0.
  by apply/eqP; rewrite -?size_poly_eq0 size_divp // size_polyXn /= subn_eq0.
rewrite -[r]hsubmxK -[X in row_mx X]rVpolyK -[X in row_mx _ X]rVpolyK.
set u := (rVpoly _); set v := (rVpoly _) => ruv_neq0.
have {ruv_neq0} uVv_neq0 : (u != 0) || (v != 0).
  rewrite -negb_and; apply: contra ruv_neq0 => /andP [/eqP-> /eqP->].
  by rewrite !linear0 row_mx0.
have su : (size u <= (size q).-1 - j)%N by rewrite size_poly.
have sv : (size v <= (size p).-1 - j)%N by rewrite size_poly.
move: u v => u v {r} in uVv_neq0 su sv *.
rewrite mulmx_rsub /= SylvesterHabicht_mxP ?size_poly //.
rewrite rsubmx_poly_rV /= => /eqP; rewrite poly_rV_eq0; last first.
  rewrite size_divp // size_polyXn /= leq_subLR.
  rewrite !addnA subnKC // (leq_trans (size_add _ _)) // geq_max.
  rewrite !(leq_trans (size_mul_leq _ _)) // -subn1 leq_subLR add1n addnC.
    by rewrite -addSn leq_add // ?size_poly // leqSpred.
  rewrite addnBA // [in X in (_ <= X)%N]addnC -addnBA //.
  by rewrite -addSn leq_add // ?size_poly // leqSpred.
rewrite divp_eq0 (negPf Xj_neq0) size_polyXn ltnS /=.
rewrite orb_idl; last by move/eqP->; rewrite size_poly0.
wlog u_neq0 : p q u v p0 le_jp le_jq q0 uVv_neq0 su sv / u != 0 => [hwlog|].
  case/orP: (uVv_neq0) => [u0 /hwlog|v0]; first exact.
  rewrite addrC orbC in uVv_neq0 * => /hwlog [] //.
  by move=> [v' u' /=]; rewrite andbC addrC; exists (u', v').
have [->|v_neq0] := eqVneq v 0; last first.
  by exists (u, v) => //=; rewrite !size_poly_gt0; do ![apply/andP;split].
rewrite mul0r addr0 size_mul // => /leq_trans - /(_ _ le_jp).
rewrite -ltnS !prednK ?ltn_addr ?size_poly_gt0 //.
by rewrite -subn_eq0 addnK size_poly_eq0 (negPf u_neq0).
Qed.

Fact gt_size_gcd  (R : idomainType) (p q u v : {poly R}) j :
  p != 0 -> q != 0 -> u != 0 ->
  (j < size (gcdp p q))%N ->
  (size u <= (size q).-1 - j)%N -> (size (u * p + v * q)%R <= j)%N ->
  (j < (size (gcdp p q)).-1)%N.
Proof.
move=> p0 q0 u0 gt_sg_j ge_sqmj_u.
set l := _ * _ + _ * _ => sl; have /eqP : l = 0.
  apply: contraTeq (leq_ltn_trans sl gt_sg_j) => l_neq0.
  by rewrite -leqNgt dvdp_leq // dvdp_add ?dvdp_mull ?(dvdp_gcdl, dvdp_gcdr).
rewrite addr_eq0 => /eqP eq_up_Nvq {sl}.
rewrite size_gcd // subSKn ltn_subRL addnC -ltn_subRL.
have /dvdp_leq : lcmp p q %| u * p.
  by rewrite dvdp_lcm dvdp_mull //= eq_up_Nvq dvdpNr dvdp_mull.
rewrite mulf_neq0 // => /(_ isT); rewrite -ltnS => /leq_trans -> //.
rewrite !size_mul // prednK ?ltn_addr ?size_poly_gt0 //.
rewrite addnC -subn1 -!addnBA ?size_poly_gt0 ?subn1 // ?leq_add2l//.
by rewrite -(succnK j); apply/leq_predn/(leq_trans gt_sg_j)/leq_gcdpr.
Qed.

(* Proposition 4.25. from BPR *)
Lemma geq_gcdp_subresultant (R : idomainType) j (p q : {poly R}) :
  (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  ((size (gcdp p q)).-1 >= j)%N = [forall i : 'I_j, subresultant i p q == 0].
Proof.
have [->|p_neq0] := eqVneq p 0.
  rewrite size_poly0 leqn0 => /eqP -> _; rewrite leq0n.
  by symmetry; apply/forallP => [[]].
have [->|q_neq0] := eqVneq q 0.
  rewrite size_poly0 leqn0 => _ /eqP ->; rewrite leq0n.
  by symmetry; apply/forallP => [[]].
move=> s_jp s_jq; apply/idP/idP => [sg|/forallP /= rpq].
  apply/forallP => i.
  apply/subresultantP => //; [by rewrite (@leq_trans j) // ltnW..|].
  pose cp := lead_coef (gcdp p q) ^+ scalp p (gcdp p q).
  pose cq := lead_coef (gcdp p q) ^+ scalp q (gcdp p q).
  exists (cp *: (q %/ gcdp p q), - (cq *: (p %/ gcdp p q))) => /=.
    rewrite size_opp !size_scale ?lc_expn_scalp_neq0 //.
    rewrite ?size_poly_gt0 ?dvdp_div_eq0 ?(dvdp_gcdr, dvdp_gcdl) //.
    rewrite p_neq0 q_neq0 /= !size_divp ?gcdp_eq0 ?(negPf p_neq0) //.
    by rewrite -!subn1 -!subnDA add1n subn1 !leq_sub2l // (leq_trans _ sg).
  rewrite mulNr !scalerCA -!divpK ?(dvdp_gcdr, dvdp_gcdl) //.
  by rewrite mulrCA subrr size_poly0.
have {}rpq : forall i, (i < j)%N -> subresultant i p q = 0.
  by move=> i Hi; apply/eqP; rewrite -[i]/(val (Ordinal Hi)); apply: rpq.
elim: j => // j ihj in s_jp s_jq rpq *.
have [s_jp' s_jq'] := (ltnW s_jp, ltnW s_jq).
have gt_sg_j : (j < size (gcdp p q))%N.
  rewrite polySpred ?gcdp_eq0 ?(negPf p_neq0) // ltnS ihj //.
  by move=> i Hi; apply: rpq; apply: ltnW.
have /eqP /subresultantP [] // := rpq _ (leqnn _).
move=> [u v] /= /andP[/andP [su0 su] /andP[sv0 sv]].
have u_neq0 : u != 0 by rewrite -size_poly_gt0.
exact: gt_size_gcd.
Qed.

(* Proposition 4.26. from BPR *)
Lemma gcdp_subresultant (R : idomainType) j (p q : {poly R}) :
  p != 0 -> q != 0 ->
  (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  (size (gcdp p q)).-1 == j =
  [forall i : 'I_j, subresultant i p q == 0] && (subresultant j p q != 0).
Proof.
move=> p_neq0 q_neq0 sjp sjq; rewrite eqn_leq -geq_gcdp_subresultant // andbC.
have [ge_sg_j|] //= := leqP; rewrite leqNgt; congr negb.
have [] // := altP (subresultantP _ _ _ _).
  move=> [[u v] /= /andP[/andP[su0 su] hv]]; rewrite size_poly_gt0 in su0.
  move=> ge_upvq_j; apply: gt_size_gcd ge_upvq_j => //.
  by rewrite polySpred ?gcdp_eq0 ?(negPf p_neq0).
apply: contraNF.
move: sjp; rewrite leq_eqVlt => /orP [/eqP ->|sjp].
  rewrite ltnNge -ltnS !prednK ?size_poly_gt0 ?gcdp_eq0 ?(negPf p_neq0) //.
  by rewrite dvdp_leq ?dvdp_gcdl.
move: sjq; rewrite leq_eqVlt => /orP [/eqP ->|sjq].
  rewrite ltnNge -ltnS !prednK ?size_poly_gt0 ?gcdp_eq0 ?(negPf p_neq0) //.
  by rewrite dvdp_leq ?dvdp_gcdr.
rewrite geq_gcdp_subresultant // => /forallP rpq.
by rewrite -[j]/(val (Ordinal (leqnn _))) rpq.
Qed.

Lemma subresultantC  (R : idomainType) j (p q : {poly R}) :
  subresultant j p q =
  (-1) ^+ ('C((size p).-1 - j + ((size q).-1 - j), 2)) * subresultant j q p.
Proof.
rewrite -signr_odd /subresultant andbC; set M := (_ *m _ in RHS).
case /boolP: (_ && _) => [_|jpq].
  rewrite mulrCA; congr (_ * _); first by rewrite addnC.
  transitivity (\det (rsubmx (perm_rev_mx *m M))); rewrite /M.
    rewrite !mul_block_col !mul1mx !mul0mx !add0r !addr0.
    rewrite mulmx_perm_rev_col //= mulmxA -perm_mxM perm_rev2 perm_mx1 mul1mx.
    by case: _ / addnC => //=.
  by rewrite -mulmx_rsub det_mulmx det_perm odd_perm_rev.
case: eqP jpq => [->|_].
  rewrite leqnn andbT -ltnNge subnn => qp.
  by rewrite eq_sym (negPf (ltn_neq qp)) (geq_subn (ltnW qp)) expr0 mul1r.
case: eqP => [->|_]; last by rewrite mulr0.
rewrite leqnn/= -ltnNge subnn => /ltnW pq.
by rewrite (geq_subn pq) expr0 mul1r.
Qed.

Lemma SylvesterHabicht_mod (R : idomainType) np nq k (p q : {poly R}) :
  (size (p %/ q)%R + np <= nq.+1)%N ->
  (SylvesterHabicht_mx np nq k (p %% q) q) =
  ((block_mx 1%:M (band (- (p %/ q))) 0 1%:M) *m
  (SylvesterHabicht_mx np nq k (lead_coef q ^+ scalp p q *: p) q)).
Proof.
move=> leq_sr_n.
rewrite mul_block_col !mul1mx mul0mx add0r; congr col_mx.
apply/eqP/mulmxP => u; rewrite mulmxDr mulmxA !mul_rV_lin1 /= -!linearD /=.
rewrite poly_rV_K.
  by rewrite -!mulrA -mulrDr divp_eq mulNr addrAC subrr add0r.
rewrite (leq_trans (size_mul_leq _ _)) //.
rewrite -subn1 leq_subLR add1n addnC (leq_trans _ leq_sr_n) //.
by rewrite size_opp leq_add2l size_poly.
Qed.

Lemma SylvesterHabicht_reduce (R : idomainType)
  (m' k' n m k : nat) (p q : {poly R})
  (pP : (n + m' + (k - k') = n + m)%N) (qP : ((k' + (k - k') = k)%N)) :
  (n <= k')%N -> (m' <= k')%N ->
  ((size p).-1 <= k' - n)%N -> ((size q).-1 <= k' - m')%N ->
  SylvesterHabicht_mx n m k p q =
  castmx (pP, qP) (col_mx (row_mx (SylvesterHabicht_mx n m' k' p q) 0)
                          (band ('X^m' * q))).
Proof.
move: (k - k')%N => z in pP qP *; move=> le_nk le_m'k' Hp Hq.
apply: (canRL (castmxKV _ _)); rewrite -[LHS]vsubmxK.
have Hm : (m' + z = m)%N by move: pP; rewrite -addnA => /addnI.
rewrite /SylvesterHabicht_mx -Hm in pP *; case: _ / qP => /=.
have -> : band q = col_mx (band q) (band ('X^m' * q)) :> 'M_(m' + _, _).
  move=> a b; rewrite -[LHS]vsubmxK; congr col_mx.
    by apply/matrixP => i j; rewrite !mxE /= !rVpoly_delta.
  by apply/matrixP => i j; rewrite !mxE /= !rVpoly_delta /= exprD mulrCA mulrA.
rewrite col_mxA castmx_comp castmx_id col_mxKd; congr col_mx.
rewrite col_mxKu -!/(SylvesterHabicht_mx _ _ _ _ _).
rewrite -[LHS]hsubmxK lsubmx_SylvesterHabicht; congr row_mx.
apply/matrixP => i j; rewrite  ?(mxE, SylvesterHabicht_mxE).
case: splitP => a /= _; rewrite nth_default ?mul0rn //.
  have [->|p_neq0] := eqVneq p 0; first by rewrite size_poly0.
  rewrite polySpred // (leq_ltn_trans Hp) // (@leq_trans (k' - a)) //.
    by rewrite ltn_sub2l // (leq_trans (ltn_ord _)) //.
  by rewrite leq_sub2r // leq_addr.
have [->|q_neq0] := eqVneq q 0; first by rewrite size_poly0.
rewrite polySpred // (leq_ltn_trans Hq) // (@leq_trans (k' - a)) //.
  by rewrite ltn_sub2l // (leq_trans (ltn_ord _)) //.
by rewrite leq_sub2r // leq_addr.
Qed.

Lemma SylvesterHabicht_scaler (R : idomainType) np nq k
  (p q : {poly R}) (c : R) : c != 0 ->
  SylvesterHabicht_mx np nq k (c *: p) q =
  block_mx c%:M 0 0 1%:M *m SylvesterHabicht_mx np nq k p q.
Proof.
move=> c_neq0; apply/eqP/mulmxP => u.
rewrite -[u]hsubmxK mulmxA mul_row_block !mulmx0 add0r addr0 mulmx1.
rewrite mul_mx_scalar !mul_row_col; congr (_ + _).
rewrite !mul_rV_lin1 /= -scalerCA; congr (poly_rV (_ * _)).
apply/polyP => i; rewrite coefZ !coef_rVpoly.
by case: insubP => [i' _ _|]; rewrite ?(mulr0, mxE).
Qed.

Lemma subresultant_scaler (R : idomainType) j (p q : {poly R}) (c : R) :
  c != 0 -> (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  subresultant j (c *: p) q = c ^+ ((size q).-1 - j) * subresultant j p q.
Proof.
move=> c_neq0 jp jq; rewrite !subresultantE// size_scale // mulrCA.
congr (_ * _); rewrite SylvesterHabicht_scaler // -mulmx_rsub.
by rewrite det_mulmx det_ublock det1 det_scalar mulr1.
Qed.

Lemma subresultant_scalel (R : idomainType) j (p q : {poly R}) (c : R) :
  c != 0 -> (j <= (size p).-1)%N -> (j <= (size q).-1)%N ->
  subresultant j p (c *: q) = c ^+ ((size p).-1 - j) * subresultant j p q.
Proof.
move=> c_neq0 jp jq; rewrite subresultantC subresultant_scaler ?size_scale //.
by rewrite mulrA subresultantC addnC -signr_odd mulr_signM addbb mul1r.
Qed.

(* Something like Proposition 4.36 from BPR *)
(* Should we parametrize by a remainder of p rather than correcting p? *)
Lemma subresultant_mod (R : idomainType) j (p q : {poly R})
      (c := (-1) ^+ 'C((size p).-1 - (size q).-1, 2) *
             lead_coef q ^+ ((size p).-1 - (size (p %% q)).-1)) :
  p != 0 -> q != 0 -> ((size q).-1 <= (size p).-1)%N ->
  (j <= (size (p %% q)%R).-1)%N ->
  subresultant j (lead_coef q ^+ (scalp p q) *: p) q =
  c * subresultant j q (- (p %% q)).
Proof.
move=> p_neq0 q_neq0 le_pq le_jr; have le_jq : (j <= (size q).-1)%N.
  by rewrite (leq_trans le_jr) -?subn1 ?leq_sub2r // ltnW ?ltn_modp.
rewrite -[- _ as X in subresultant _ _ X]scaleN1r.
rewrite subresultant_scalel ?oppr_eq0 ?oner_eq0 //.
rewrite [in RHS]subresultantC ?size_opp //.
rewrite !subresultantE// !size_scale ?lc_expn_scalp_neq0 //; last first.
  exact/(leq_trans le_jq).
rewrite ![in X in c * X]mulrA [c * _]mulrA -!exprD.
set np := ((size p).-1 - j)%N; set nq := ((size q).-1 - j)%N.
set nr := ((size (p %% q)%R).-1 - j)%N.
set c1 := (X in X * \det _); set c2 := (X in c * X * _).
set SHpq := SylvesterHabicht_mx _ _ _ _ _.
have -> : \det (rsubmx SHpq) =
          \det (rsubmx ((block_mx 1%:M (band (- (p %/ q))) 0 1%:M) *m SHpq)).
  by rewrite -mulmx_rsub det_mulmx det_ublock !det1 !mul1r.
rewrite /SHpq {SHpq} -SylvesterHabicht_mod; last first.
  rewrite size_divp // /np /nq -subn_eq0 subnS subnBA ?(leq_trans _ le_pq) //.
  rewrite -addnA subnK // -subn1 subnAC addnC -addnBA //; last first.
    by rewrite subn_gt0 (leq_ltn_trans le_pq) // polySpred.
  by rewrite subnAC subn1 subnKC // subnn.
rewrite (@SylvesterHabicht_reduce _ nr (j + (nq + nr))); first 3 last.
  by rewrite addnCA leq_addr.
  by rewrite addnCA addnA leq_addl.
  by rewrite addnA addnAC addnK /nr subnKC.
  by rewrite addnA addnK /nq subnKC.
  by rewrite subnDl subnKC // leq_add2l /nr /np -!subn1 !leq_sub // leq_modp.
  by apply: subnKC; rewrite !leq_add2l /nr /np -!subn1 !leq_sub // leq_modp.
move=> pP qP; move: (SylvesterHabicht_mx _ _ _ _ _) => M; move: pP qP M.
move z_def : (_ - _)%N => z; case: _ / => qP M; set (B := band _).
rewrite  cast_col_mx -{1}[M]hsubmxK -[B]hsubmxK -[lsubmx B]hsubmxK.
have {qP} -> : qP = esym (addnA _ _ _) by exact: nat_irrelevance.
rewrite -!row_mxA -block_mxEv block_mxEh row_mxKr -block_mxEv det_lblock.
rewrite mulrA mulrAC; congr (_ * _); rewrite det_rsub_band; last first.
  rewrite size_monicM ?monicXn // size_polyXn addSn /=.
  by rewrite /np addnA subnKC // -!subn1 -addnBA ?size_poly_gt0 // addnC.
rewrite subnDl subnDl /nq /nr -subnDA subnKC // in z_def.
rewrite lead_coef_monicM ?monicXn // mulrAC z_def; congr (_ * _).
have le_rq : ((size (p %% q)%R).-1 <= (size q).-1)%N.
  by rewrite -!subn1 leq_sub2r // ltnW // ltn_modp.
rewrite -exprD -[LHS]signr_odd -[RHS]signr_odd; congr (_ ^+ _ _).
rewrite !oddD -/np -/nq -/nr !addbA addbK; congr (_ (+) _).
have -> : ((size p).-1 - (size q).-1 = np - nq)%N.
  by rewrite subnBA // subnK // (leq_trans le_jq).
by rewrite addbC odd_bin2B ?leq_sub // addKb addnC.
Qed.

Lemma subresultant_gt_mod (R : idomainType) j (p q : {poly R}) :
  p != 0 -> q != 0 -> ((size q).-1 <= (size p).-1)%N ->
  (size (p %% q)%R <= j < (size q)%R.-1)%N ->
  subresultant j p q = 0.
Proof.
move=> p_neq0 q_neq0 le_pq /andP[le_rj] le_jq.
apply/eqP/subresultantP => //.
- by apply/(leq_trans _ le_pq)/ltnW.
- exact/ltnW.
exists ((lead_coef q ^+ scalp p q)%:P, - (p %/ q)) => /=; last first.
  by rewrite mul_polyC divp_eq addrAC mulNr subrr add0r.
rewrite size_polyC expf_neq0 ?lead_coef_eq0//= subn_gt0 le_jq/= size_opp.
rewrite size_poly_gt0 divpN0// -(leq_sub2rE (p:=1)) ?size_poly_gt0//.
by rewrite !subn1 le_pq/= size_divp// -predn_sub -subnS leq_sub2l.
Qed.

Lemma subresultantp0 (R : idomainType) j (p : {poly R}) :
  (j < (size p).-1)%N -> subresultant j p 0 = 0.
Proof.
case: (posnP j) => [->|].
  rewrite ltnNge -subn_eq0 => /negPf sp; apply/eqP.
  rewrite subresultant_eq0// size_poly0/= sub0n /SylvesterHabicht_mx band0.
  case: ((size p).-1 - 0)%N sp => //= n _.
  apply/det0P; exists (row_mx 0 (\row_i (i == ord_max)%:R)).
    apply/eqP => /rowP /(_ (unsplit (inr ord_max))).
    rewrite mxE unsplitK !mxE eqxx => /eqP; apply/negP/oner_neq0.
  apply/rowP => i; rewrite !mxE big1_idem//= ?addr0// => k _.
  by rewrite !mxE; case: (split k) => a; rewrite !mxE (mul0r, mulr0).
move=> j0 jp.
rewrite /subresultant size_poly0/= (leqNgt j 0) j0 andbF (negPf (ltn_neq jp)).
by rewrite eq_sym (negPf (ltn_neq j0)).
Qed.

Lemma subresultant0p (R : idomainType) j (q : {poly R}) :
  (j < (size q).-1)%N -> subresultant j 0 q = 0.
Proof.
move=> jq; apply/eqP; rewrite subresultantC mulf_eq0; apply/orP; right.
exact/eqP/subresultantp0.
Qed.

Lemma subresultant_map_poly (A B : ringType) i
    (p q : {poly A}) (f : {rmorphism A -> B}) :
  f (lead_coef p) != 0 -> f (lead_coef q) != 0 ->
  subresultant i (map_poly f p) (map_poly f q) = f (subresultant i p q).
Proof.
move=> fp0 fq0; rewrite /subresultant !size_map_poly_id0//.
case: ifP => [_|ipq].
  rewrite rmorphM rmorphXn rmorphN1 -det_map_mx.
  rewrite map_rsubmx map_mxM map_block_mx map_perm_mx !map_mx0 map_mx1.
  rewrite /SylvesterHabicht_mx map_col_mx.
  congr (_ * \det (rsubmx (_ *m _)))%R; apply/esym.
  by congr col_mx; apply/map_lin1_mx => x /=;
    rewrite mxpoly.map_poly_rV rmorphM/= mxpoly.map_rVpoly.
case: eqP => _; first exact/lead_coef_map_eq.
case: eqP => _; first exact/lead_coef_map_eq.
exact/esym/raddf0.
Qed.

Lemma subresultant_last (A : idomainType) (p q : {poly A}) :
  subresultant (size p).-1 p q
  = lead_coef p ^+ ((size q).-1 - (size p).-1 + ((size q).-1 < (size p).-1))%N.
Proof.
case: (ltnP (size q).-1 (size p).-1) => [qp|pq].
  rewrite /subresultant [X in _ && X]leqNgt qp andbF eqxx.
  by rewrite (geq_subn (ltnW qp)) expr1.
rewrite subresultantE// subnn det_trig; last first.
  apply/forallP => /= i; apply/forallP => /= k; apply/implyP => ik; apply/eqP.
  rewrite mxE SylvesterHabicht_mxE.
  case: (fintype.split i) (splitK i) ik => [i' <- /= ik|[]//]/=.
  rewrite nth_default ?mul0rn// -addnBA; last exact/ltnW.
  case: {1 2}(size p) => [//|n] /=.
  by rewrite -[X in (X < _)%N]addn0 ltn_add2l subn_gt0.
rewrite {1}addn0 addnn -signr_odd odd_double expr0 mul1r.
under eq_bigr => i _.
  suff ->: rsubmx
            (SylvesterHabicht_mx ((size q).-1 - (size p).-1) 0
        ((size p).-1 + ((size q).-1 - (size p).-1 + 0)) p q) i i
           = lead_coef p.
    over.
  rewrite mxE SylvesterHabicht_mxE.
  case: (fintype.split i) (splitK i) => [i' <- /=|[]//]/=.
  by rewrite leq_addl mulr1n -addnBA// subnn addn0 lead_coefE.
by rewrite prodr_const cardT size_enum_ord addn0.
Qed.

Import Num.Theory Order.POrderTheory Pdiv.Field.

(* Lemma 4.34 from BPR is cindexR_rec from qe_rcf_th, except it uses rmodp *)

Theorem pmv_subresultant (R : rcfType) (p q : {poly R}) :
  (size q < size p)%N ->
  pmv [seq subresultant i p q | i <- rev (iota 0 (size p))] = cindexR q p.
Proof.
move sq: (size q) => n; move: p q sq.
apply/(@Wf_nat.lt_wf_ind n
  (fun n => forall p q : {poly R}, size q = n -> (n < size p)%N -> _)).
move=> {}n IHn p q sq sp.
case/boolP: (q == 0) sq sp => [/eqP ->|q0 sq sp].
  rewrite size_poly0 => <- {n IHn} /= p0.
  rewrite -(prednK p0) iotanS rev_rcons/= cindexR0p.
  apply/pmv_cat00 => _ /mapP[i] + ->.
  rewrite mem_rev mem_iota/= => ip.
  exact/eqP/subresultantp0.
have p0: p != 0 by apply/eqP => p0; move: sp; rewrite p0 size_poly0.
have n0: (0 < n)%N by rewrite -sq size_poly_gt0.
rewrite -(subnKC (ltnW sp)) iotaD rev_cat map_cat.
move mE: (size p - n)%N => m.
case: m mE => [/eqP|m mE]; first by rewrite subn_eq0 leqNgt sp.
rewrite iotanS rev_rcons/= -(succnK (n + m)%N) -addnS -mE subnKC ?(ltnW sp)//.
rewrite {1}/subresultant sq [X in _ && X]leqNgt ltn_predRL prednK//.
rewrite sp andbF eqxx.
under eq_map_seq => i.
rewrite mem_rev mem_iota => /andP[] ni.
  rewrite -(succnK (n + m)%N) -addnS -mE subnKC ?(ltnW sp)// => ip.
  rewrite /subresultant sq [X in _ && X]leq_npred; last exact/(leq_trans n0).
  rewrite ltnNge ni andbF (negPf (ltn_neq ip)) eq_sym.
  move: ni; rewrite -{1}(prednK n0) => /ltn_neq/negPf ->.
  over.
move srE : (size (p %% q)) => sr.
have srn : (sr < n)%N by rewrite -srE -sq; apply/ltn_modpN0.
rewrite -{2}(subnKC (ltnW srn)) iotaD rev_cat.
move kE: (n - sr)%N => k.
case: k kE => [/eqP|k kE]; first by rewrite subn_eq0 leqNgt srn.
rewrite iotanS rev_rcons/= map_cat.
have ->: (sr + k = (size q).-1)%N.
  apply/succn_inj; rewrite -addnS -kE subnKC ?(ltnW srn)// sq prednK//.
rewrite subresultantC subresultant_last subnn addn0 sq subn_prednn//.
under [X in _ :: X ++ _]eq_map_seq => i.
  rewrite mem_rev mem_iota => /andP[] sri.
  rewrite -ltnS -addnS -kE subnKC ?(ltnW srn)// => ilt.
  rewrite subresultant_gt_mod//; first by over.
    by apply/leq_predn/ltnW; rewrite sq.
  by rewrite srE sri sq ltn_predRL.
(* Whaaaat??? Why do I need to alias `p` for `over` to work? *)
set a := p.
under [X in _ :: _ ++ X]eq_map_seq => i.
  rewrite mem_rev mem_iota/= => isr.
  have ->: a = (lead_coef q ^+ scalp p q) *: a.
    by rewrite scalpE expr0 scale1r.
  rewrite subresultant_mod//; first by over.
    by apply/leq_predn/ltnW; rewrite sq.
  rewrite -ltnS srE; apply/(leq_trans isr)/leqSpred.
rewrite {}/a [LHS]pmv_cat0s; first last.
- by move=> x /mapP[] i _ /eqP.
- by rewrite mulf_eq0 signr_eq0 expf_eq0 lead_coef_eq0 (negPf q0) andbF.
rewrite size_map size_rev size_iota addrC cindexR_rec; congr (_ + _).
  rewrite crossRE lead_coefM size_mul// sq.
  have odd2: forall i, (1 < i)%N -> (odd i.-2 = odd i).
    by case=> [//|]; case=> [//|i _] /=; rewrite negbK.
  rewrite odd2; last first.
    by apply/(@leq_add 1) => //; apply/(leq_ltn_trans _ sp).
  rewrite oddD -oddB ?(ltnW sp)// mE/=.
  case/boolP: (odd m) => modd; first by rewrite !mulr0n.
  rewrite !mulr1n !sgzM !sgzX sgzN1 mulrCA; congr (_ * _).
  rewrite sgz_odd ?lead_coef_eq0//= ltn_predRL prednK; last first.
    exact/(ltn_trans n0).
  rewrite ltnNge (ltnW sp) [(m + _)%Nrec]addn0 modd expr1 mulrA -exprD !bin2.
  rewrite succnK.
  case: m {mE} => [|m] in modd *; first by rewrite expr0 mul1r.
  rewrite succnK mulnC !mulSn addnA addnn halfD odd_double doubleK add0n.
  rewrite addnCA addnn halfK oddM andbN subn0 -signr_odd oddD oddM.
  by rewrite (negPf modd) andbF/= expr0 mul1r.
have ->: cindexR (next_mod p q) q = cindexR (- (p %% q)) q.
  by rewrite /next_mod modpE -scaleNr !cindexR_mulCp !sgzN sgz_invr.
rewrite -(IHn sr); first last.
- by rewrite sq.
- by rewrite size_opp.
- exact/ltP.
case: sr => [/=|sr] in srE srn kE *.
  rewrite !cats0 [LHS]pmv_cat00; last by move=> x /mapP[] i _ /eqP.
  rewrite subn0 in kE.
  rewrite sq kE iotanS rev_rcons/= [RHS]pmv_cat00// => _ /mapP[] i + ->.
  rewrite mem_rev mem_iota/= => ik.
  move/eqP: srE; rewrite -leqn0 => /size_poly_leq0P ->.
  rewrite oppr0; apply/eqP/subresultantp0.
  by rewrite sq kE succnK.
rewrite sq -[in RHS](subnKC (ltnW srn)) iotaD rev_cat map_cat kE !iotanS.
rewrite !rev_rcons/= -(succnK (sr.+1 + k)%N) -addnS -kE (subnKC (ltnW srn)).
rewrite -[sr]succnK -srE -[size (p %% q)]size_opp.
rewrite subresultantC subresultant_last size_opp srE succnK subnn addn0 sq.
rewrite subn_prednn; last by rewrite -sq size_poly_gt0.
rewrite mE -[(n.-1 - _)%N]predn_sub -subnS kE -{1}[in RHS]sq.
rewrite subresultant_last [RHS]pmv_cat0s; first last.
- move=> _ /mapP[] i + ->.
  rewrite mem_rev mem_iota => /andP[] sri.
  rewrite -(succnK (sr.+1 + k)%N) -addnS -kE (subnKC (ltnW srn)) => iq.
  rewrite /subresultant size_opp srE succnK [X in _ && X]leqNgt sri andbF sq.
  by rewrite (negPf (ltn_neq iq)) [i == _]eq_sym (negPf (ltn_neq sri)).
- rewrite mulf_eq0 signr_eq0/= expf_eq0 lead_coef_eq0 oppr_eq0 -size_poly_eq0.
  by rewrite srE andbF.
rewrite [LHS]pmv_cat0s; first last.
- by move=> x /mapP[] i _ /eqP.
- rewrite !mulf_eq0 !expf_eq0 !lead_coef_eq0 (negPf q0) !oppr_eq0 oner_eq0.
  by rewrite !andbF/= -size_poly_gt0 srE.
congr (_ + _).
  rewrite map_comp; apply/esym/(esym (pmvZ _ _)).
  by rewrite mulf_eq0 signr_eq0 expf_eq0 lead_coef_eq0 (negPf q0) andbF.
rewrite !size_map !size_rev !size_iota.
case/boolP: (odd k) => kodd; first by rewrite !mulr0n.
rewrite !mulr1n; congr (_ * _).
rewrite !sgzM !mulrA; congr (_ * _ * _).
rewrite !sgzX !sgzN1.
rewrite ltn_predRL prednK; last exact/(ltn_trans n0).
rewrite ltnNge (ltnW sp) addn0 sq size_opp srE succnK ltn_predRL srn.
rewrite [(sr - _)%N]geq_subn; last first.
  by rewrite -(succnK sr); apply/leq_predn/ltnW.
rewrite expr1.
rewrite mulrAC -[X in X * _]mulrA -exprD mulrAC -exprD addnn -signr_odd.
rewrite odd_double expr0 mul1r sgz_odd ?lead_coef_eq0// -mE.
rewrite -(@subnKC n.-1 (size p).-1); last by apply/leq_predn/ltnW.
rewrite subDnCA; last first.
  by apply/ltnW; rewrite ltnNge -subn_eq0 -predn_sub -subnS kE.
rewrite subn_prednn; last by rewrite -sq size_poly_gt0.
by rewrite addnA addnn oddD odd_double/= -predn_sub -subnS kE/= kodd expr1.
Qed.

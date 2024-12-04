From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq ssrnat.
From mathcomp Require Import bigop fintype tuple order ssralg ssrnum poly.
From mathcomp Require Import polydiv complex polyorder matrix topology.
From mathcomp Require Import normedtype signed classical_sets.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory Num.Def.
Import complex numFieldTopology.Exports.

Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope complex_scope.
Local Open Scope classical_set_scope.

Section ContinuityRoots.
Variable (R : rcfType).

Definition alignp eps (p q : {poly R[i]}) :=
  {in root p, forall u,
        (\sum_(v <- dec_roots q | (`|v - u| < eps)%R) \mu_v q >= \mu_u p)%N}.

Definition deformp eps (p q : {poly R[i]}) :=
  (size q <= size p)%N /\ forall i : 'I_(size p), `|p`_i - q`_i| < eps.

Lemma close_root_deformp (eps : R[i]) (p : {poly R[i]}) : 0 < eps ->
  exists delta : R[i], 0 < delta /\
    forall q, deformp delta p q ->
      forall x, root p x -> exists y, root q y /\ `|x - y| < eps.
Proof.
wlog : eps / eps <= 1 => [H|eps1 eps0].
  case: eps => eR eI.
  rewrite ltcE/= => /andP[/eqP ->] e0.
  case: (H (minr (eR)%:C 1)) => [||delta [d0]dP] {H}.
  - rewrite lecE /minr -(fun_if (fun x => x%:C))/= ltcE/= eqxx/=.
    by rewrite ge_min lexx orbT.
  - rewrite ltcE /minr -(fun_if (fun x => x%:C))/= ltcE/= eqxx/= .
    by rewrite lt_min e0 ltr01.
  exists delta; split=> [//|] q /dP {}dP x /dP [y] [qy] xy.
  exists y; split=> //; apply/(lt_le_trans xy).
  by rewrite lecE /minr -(fun_if (fun x => x%:C))/= ltcE/= eqxx/= ge_min lexx.
case sp: (size p) => [|n].
  exists 1; split=> [//|] q [sq] _ x _; exists x; split; last first.
    by rewrite subrr normr0.
  by move: sq; rewrite sp size_poly_leq0 => /eqP ->; apply/root0.
pose M := (\big[maxr/1]_(x <- dec_roots p) Re `|x|)%:C.
have M1 : 1 <= M.
  rewrite /M lecE/= eqxx/=.
  exact/Order.TotalTheory.bigmax_ge_id.
exists ((`|p`_(ord_max : 'I_n.+1)|) * ((eps / M) ^+ n / (n.+1%:R *+ 4))).
split=> [|q [sq]].
  apply/mulr_gt0; last first.
    by rewrite divr_gt0// exprn_gt0// divr_gt0// (lt_le_trans (ltr01)).
  rewrite normr_gt0; apply/eqP => p0.
  suff: (size p <= n)%N by rewrite sp ltnn.
  apply/leq_sizeP => i; rewrite leq_eqVlt => /orP; case=> [/eqP <- //|ni].
  have/leq_sizeP: (size p <= n.+1)%N by rewrite sp.
  exact.
rewrite sp => qcoef; move: (qcoef ord_max) => /(le_lt_trans (lerB_dist _ _)).
rewrite ltrBlDl -ltrBlDr -[X in X - _]mulr1 -mulrBr.
have: 1 / 2 <= (1 - (eps / M) ^+ n / (n.+1%:R *+ 4)).
  rewrite ler_pdivrMr ?ltr0n// mulrBl lerBrDr -lerBrDl [1 * 2]mulr_natr.
  rewrite -{2}[2]natr1 -addrA subrr addr0 -[2]divr1 mulf_div mulr1.
  rewrite -[4%N]/(2 * 2)%N mulrnA -[X in _ / X]mulr_natr -mulf_div.
  rewrite divff ?pnatr_eq0// mulr1 -mulr_natr -natrM.
  rewrite ler_pdivrMr ?ltr0n ?muln_gt0// mul1r.
  have le1: (eps / M) ^+ n <= 1.
    apply/exprn_ile1.
      apply/divr_ge0; first exact/ltW.
      exact/(le_trans ler01).
    rewrite ler_pdivrMr ?mul1r; last exact/(lt_le_trans ltr01).
    exact/(le_trans eps1).
  by apply/(le_trans le1); rewrite ler1n muln_gt0.
move=> /(ler_pM _ _ (lexx (normr p`_ord_max))) => /(_ n (normr_ge0 _)).
rewrite div1r invr_ge0 => /(_ (ler0n _ _)).
move=> le2 /(le_lt_trans le2) {le2} /= pqn x px.
have n0: (0 < n)%N.
  rewrite lt0n; apply/eqP => n0; move: sp; rewrite n0 => ps.
  have /size1_polyC pE : (size p <= 1)%N by rewrite ps.
  by move: px ps; rewrite pE rootC => /eqP ->; rewrite size_polyC eqxx.
have qn0: q`_n != 0.
  apply/eqP => qn.
  move: pqn; rewrite qn normr0 ltr_pdivrMr ?ltr0n// mul0r.
  by move=> /(le_lt_trans (normr_ge0 _)); rewrite ltxx.
have {}sq : size q = n.+1.
  apply/eqP; rewrite eqn_leq; apply/andP; split; first by rewrite -sp.
  exact/gt_size.
case: (closed_field_poly_normal q) => /= r; rewrite lead_coefE sq -pred_Sn => qE.
move: (sq); rewrite qE size_scale// size_prod_seq; last first.
  by move=> i _; rewrite polyXsubC_eq0.
under eq_bigr do rewrite size_XsubC.
rewrite big_const_seq count_predT iter_addn_0 subSn ?leq_pmull// mul2n -addnn.
rewrite subDnCA// subnn addn0 => /eqP.
rewrite eqSS => /eqP sr.
pose m := (\big[Order.min/Re `|x - head 0 r|]_(z <- r) Re `|x - z|)%:C.
have m0: 0 <= m.
  rewrite /m lecE/= eqxx/=.
  rewrite le_bigmin -lecR (normr_ge0 (x - _)); apply/allP => y _ /=.
  by rewrite -lecR (normr_ge0 (x - y)).
have: `|p`_n| / 2 * m ^+ n <= `|q.[x]|.
  rewrite qE hornerE horner_prod normrM normr_prod; apply/ler_pM.
  - apply/divr_ge0; [apply/normr_ge0|apply/ler0n].
  - exact/exprn_ge0.
  - exact/ltW.
    rewrite -sr -prodr_const_seq big_seq [X in _ <= X]big_seq.
    apply/ler_prod => y yr; apply/andP; split=> //.
    rewrite !hornerE -[`|x - y|]RRe_real ?normr_real// /m lecR.
    rewrite bigmin_le; apply/orP; right; apply/hasP; exists y => //=.
rewrite -[q.[x]]subr0 -{2}(rootP px) distrC -hornerN -hornerD.
rewrite -[p - q]coefK horner_poly => mle.
move: (le_trans mle (ler_norm_sum _ _ _)).
under eq_bigr do rewrite normrM normrX coefD coefN; move=> {}mle.
have: normr (p`_n) / 2 * m ^+ n <=
    \sum_(i < size (p - q))
      normr p`_n * ((eps / M) ^+ n / (n.+1%:R *+ 4)) * M ^+ n.
  apply/(le_trans mle)/ler_sum; case=> i/= ipq _.
  have ilt : (i < n.+1)%N.
    rewrite -[n.+1]maxnn -{1}sp -sq -[size q]size_opp.
    exact/(leq_trans ipq)/size_add.
  apply/ler_pM.
  - exact/normr_ge0.
  - exact/exprn_ge0/normr_ge0.
  - exact/ltW/(qcoef (Ordinal ilt)).
  rewrite ltnS in ilt; rewrite -(subnKC ilt) exprD -[X in X <= _]mulr1.
  apply/ler_pM.
  - exact/exprn_ge0/normr_ge0.
  - exact/ler01.
  - rewrite -[M ^+ i]mul1r -ler_pdivrMr; last first.
      exact/exprn_gt0/(lt_le_trans ltr01).
    rewrite -expr_div_n; apply/exprn_ile1.
      by apply/divr_ge0; [apply/normr_ge0|apply/(le_trans ler01)].
    rewrite ler_pdivrMr ?mul1r /M; last exact/(lt_le_trans ltr01).
    rewrite -[X in X <= _]RRe_real ?normr_real// lecR.
    rewrite le_bigmax; apply/orP; right; apply/hasP; exists x => //=.
    by rewrite mem_dec_roots -size_poly_leq0 sp.
  - exact/exprn_ege1.
rewrite sumr_const card_ord -[(_ * _) *+ _]mulr_natr -!mulrA -subr_ge0 -mulrBr.
rewrite pmulr_rge0; last first.
  rewrite normr_gt0; apply/eqP => pn.
  suff: (size p <= n)%N by rewrite sp ltnn.
  apply/leq_sizeP => i; rewrite leq_eqVlt => /orP[/eqP <- //|].
  by rewrite -sp => /leq_sizeP/(_ i (leqnn i)).
rewrite subr_ge0 mulrC expr_div_n -[_ *+ 4]mulr_natr [_^-1 * _]mulrC.
rewrite [_ * 4]mulrC -mulf_div [X in _ <= X]mulrA mulf_div [_ * 4]mulrC.
rewrite -mulf_div divff; last exact/expf_neq0/lt0r_neq0/(lt_le_trans ltr01).
rewrite mulr1 => {}mle.
have /(le_trans mle) {}mle:
    eps ^+ n / 4 * ((size (p - q))%:R / n.+1%:R) <= eps ^+ n / 4.
  rewrite -[X in _ <= X]mulr1; apply/ler_pM.
  - apply/mulr_ge0; first exact/exprn_ge0/ltW.
    by rewrite invr_ge0.
  - exact/divr_ge0.
  - exact/lexx.
  rewrite mulrC ler_pdivrMl ?ltr0n// mulr1 ler_nat -(maxnn n.+1) -{1}sp -sq.
  by rewrite -(size_opp q) size_add.
have /(le_lt_trans mle) : eps ^+ n / 4 < eps ^+ n / 2.
  rewrite mulrC ltr_pdivrMl ?ltr0n// -[4%N]/((2 * 2)%N) natrM mulrACA.
  rewrite divff ?pnatr_eq0// mulr1 mulrC mulr_natr mulr2n -subr_gt0 -addrA.
  by rewrite subrr addr0 exprn_gt0.
rewrite -subr_gt0 -(@pmulr_rgt0 _ 2%:R)// mulrBr subr_gt0 mulrCA.
rewrite divff ?pnatr_eq0// mulr1 mulrCA divff ?pnatr_eq0//.
rewrite -ltr_pdivrMl ?exprn_gt0// mulrC -expr_div_n expr_lt1//; last first.
  by apply/mulr_ge0 => //; rewrite invr_ge0 ltW.
rewrite mulrC ltr_pdivrMl// mulr1 /m -[eps]RRe_real ?gtr0_real// ltcR.
rewrite bigmin_lt; case: r {qE m m0 mle} sr n0 => [<- //|] y r sr n0/=.
rewrite orbA orbb -/(has _ (y :: r)) => /hasP [z] zr zx.
exists z; split; last by rewrite -[`|x - z|]RRe_real ?normr_real// ltcR.
rewrite rootZ// root_bigmul; apply/hasP; exists z => //=.
by rewrite root_XsubC.
Qed.

Lemma rm_root_poly (p : {poly R[i]}) (x : R[i]) :
  x != 0 ->
  root p x ->
  p %/ ('X - x%:P)
  = \poly_(i < (size p).-1) (- x ^- (i.+1) * \sum_(j < i.+1) p`_j * x ^+ j).
Proof.
move=> x0 /factor_theorem [q] ->.
have X0 : ('X - x%:P != 0) by rewrite polyXsubC_eq0.
rewrite mulpK//.
have [->|q0] := eqVneq q 0.
  by rewrite mul0r size_poly0 poly_def big_ord0.
rewrite size_mul// size_XsubC addn2 -!pred_Sn.
apply/polyP => i; rewrite coef_poly.
case: (ltnP i (size q)) => [|/leq_sizeP/(_ i (leqnn i))//] iq.
rewrite mulNr -mulrN -sumrN.
under eq_bigr do rewrite mulrBr coefD coefN mulrBl coefMC -mulrA -exprS opprB.
under eq_bigr do rewrite coefMX {1}[X in q`_X]pred_Sn.
pose f i := (if i == 0%N then 0 else q`_i.-1) * x ^+ i.
rewrite -(big_mkord xpredT (fun i => f (i.+1) - f i)) telescope_sumr// /f/=.
rewrite mul0r subr0 mulrCA [X in _ * X]mulrC divff ?mulr1//.
exact/expf_neq0.
Qed.

Lemma close_rm_root (eps : R[i]) (p : {poly R[i]}) (xp : R[i]) :
  0 < eps -> xp != 0 -> root p xp ->
  exists delta, 0 < delta /\
    forall (q : {poly R[i]}) (xq : R[i]),
      root q xq -> deformp delta p q -> `|xp - xq| < delta ->
      deformp eps (p %/ ('X - xp%:P)) (q %/ ('X - xq%:P)).
Proof.
move=> e0 xp0 pxp /=.
have [->|] := poly0Vpos p.
  exists 1; split=> [//|] q xq qxq []; rewrite size_poly0 => /size_poly_leq0P.
  by move=> -> _ _; rewrite !div0p; split=> //; case; rewrite size_poly0.
move sp: (size p) => n; case: n sp => // n sp _.
pose f := fun i (x : 'rV[R[i]^o]_n.+1 * (R[i]^o)) =>
  - (x.2 ^- i.+1) * \sum_(j < n.+1 | (j <= i)%N) x.1 ord0 j * x.2 ^+ j.
have cont : forall i, {for (\row_(i < n.+1) p`_i, xp), continuous (f i)}.
  move=> i /=.
  apply/(@continuousM R[i] ('rV[R[i]^o]_n.+1 * (R[i]^o))%type).
    apply/(@continuousN R[i] R[i]^o ('rV[R[i]^o]_n.+1 * (R[i]^o))%type).
    apply/continuousV; first by rewrite expf_eq0.
    apply/continuousX.
    apply/cvg_snd.
  apply/(@continuous_sum R[i] R[i]^o ('rV[R[i]^o]_n.+1 * (R[i]^o))%type).
  move=> j ji.
  apply/(@continuousM R[i] ('rV[R[i]^o]_n.+1 * (R[i]^o))%type); last first.
    exact/continuousX/cvg_snd.
  apply/(@eq_continuous_at ('rV[R[i]^o]_n.+1 * (R[i]^o))%type _
    ((fun x : 'rV[R[i]^o]_n.+1 => x ord0 j) \o fst)) => //.
  apply/continuous_comp; first exact/cvg_fst.
  exact/coord_continuous.
have /fin_all_exists /=: forall i : 'I_n.+1,
  exists delta, 0 < delta /\
    forall (q : {poly R[i]}) (xq : R[i]),
      deformp delta p q -> normr (xp - xq) < delta ->
      `|f i (\row_(i < n.+1) p`_i, xp) - f i (\row_(i < n.+1) q`_i, xq)| < eps.
  move=> i.
  move/(_ i): cont => /= /cvgr_dist_lt /(_ eps e0) [][]/= Vp Vx []/=.
  move=> /nbhs_ballP [dp/= +] dVp /nbhs_ballP [dx/= +] dVx Vpx.
  rewrite !ltcE/= => /andP[/eqP dpi dp0] /andP[/eqP dxi dx0].
  exists (minr (Re dp) (Re dx))%:C.
  split=> [|q xq [] _ dpq xpq]; first by rewrite ltcR lt_min dp0.
  apply/Vpx; split=> /=; last first.
    apply/dVx/(lt_le_trans xpq).
    by rewrite lecE/= dxi eqxx/= ge_min lexx orbT.
  apply/dVp; case; case=> // ltn01 j.
  move: dpq; rewrite sp !mxE => /(_ j) dpq.
  apply/(lt_le_trans dpq).
  by rewrite lecE/= dpi eqxx/= ge_min lexx.
move=> [delta] deltaP.
exists (\big[minr/minr (Re `|xp|) (Re `|p`_n|)]_(i < n.+1) Re (delta i))%:C.
split=> [|q xq qxq [] spq].
  rewrite ltcR lt_bigmin lt_min -!ltcR RRe_real ?normr_real// normr_gt0 xp0/=.
  apply/andP; split; last first.
    by apply/allP => /= i _; case/(_ i): deltaP; rewrite ltcE/= => /andP[_ +] _.
  rewrite (normr_gt0 (p`_n)); apply/eqP => pn0.
  suff: (size p <= n)%N by rewrite sp ltnn.
  apply/leq_sizeP => j; rewrite leq_eqVlt => /orP[/eqP <- //|nj].
  by have/leq_sizeP/(_ j nj): (size p <= n.+1)%N by rewrite sp.
rewrite sp => dpq.
rewrite -(RRe_real (normr_real _)) ltcR lt_bigmin lt_min -!ltcR.
rewrite !(RRe_real (normr_real _)) => /andP[] /andP[xpq] xqpn /allP xdelta.
rewrite /deformp !size_divp ?polyXsubC_eq0// !size_XsubC/= !subn1.
split.
  move: spq; rewrite sp succnK -[(_ <= n)%N]ltnS.
  by case: (size q).
rewrite sp succnK => i.
rewrite rm_root_poly// coef_poly sp ltn_ord rm_root_poly//; last first.
  by apply/eqP => xq0; move: xpq; rewrite xq0 subr0 ltxx.
rewrite coef_poly.
have sq: size q = size p.
  apply/anti_leq; rewrite spq/= sp; apply/gt_size/eqP => qn0.
  move/(_ ord_max): dpq; rewrite -(RRe_real (normr_real _)) ltcR lt_bigmin.
  by rewrite lt_min qn0 subr0 ltxx andbF.
rewrite sq sp ltn_ord.
move/(_ (lift ord_max i)): deltaP => [d0] /(_ q xq) /=.
have /[swap]/[apply]: deformp (delta (lift ord_max i)) p q.
  split; first by rewrite sq.
  rewrite sp => j; apply/(lt_le_trans (dpq j)).
  rewrite -(RRe_real (gtr0_real d0)) lecR bigmin_le; apply/orP; right.
  apply/hasP; exists (lift ord_max i); first exact/mem_index_enum.
  exact/lexx.
have /[swap]/[apply]: normr (xp - xq) < delta (lift ord_max i).
  rewrite -(RRe_real (gtr0_real d0)) ltcR.
  exact/xdelta/mem_index_enum.
rewrite /lift /= /bump leqNgt ltn_ord add0n /f/=.
congr (`|_ * _ - _ * _| < _);
  under eq_bigr do rewrite mxE.
  rewrite (big_ord_iota _ n.+1 (fun i0 => (i0 <= i)%N)
    (fun i => p`_i * xp ^+ i)).
  rewrite -big_filter -{1}[i : nat]add0n filter_iota_leq.
    by rewrite -big_ord_iota.
  by rewrite ltnS; apply/ltnW.
rewrite (big_ord_iota _ n.+1 (fun i0 => (i0 <= i)%N) (fun i => q`_i * xq ^+ i)).
rewrite -big_filter -{1}[i : nat]add0n filter_iota_leq.
  by rewrite -big_ord_iota.
by rewrite ltnS; apply/ltnW.
Qed.

Lemma deformpW (e e' : R[i]) (p q : {poly R[i]}) :
  e <= e' -> deformp e p q -> deformp e' p q.
Proof. by move=> ee [spq pqe]; split=> // i; apply/(lt_le_trans (pqe i)). Qed.

Lemma aligned_deformed (eps : R[i]) (p : {poly R[i]}) :
  0 < eps ->
  exists delta, 0 < delta /\ forall q, deformp delta p q -> alignp eps p q.
Proof.
wlog : eps / eps < 1 => [H|e1 e0].
  case: eps => eR eI.
  rewrite ltcE/= => /andP[/eqP ->] e0.
  case: (H (minr eR (1 / 2))%:C) => /= [||delta [d0 dP]] {H}.
  - by rewrite ltcR gt_min ltr_pdivrMr// mul1r -[1]/(1%:R) ltr_nat leqnn orbT.
  - rewrite ltcR lt_min e0/=; apply/mulr_gt0; first exact: ltr01.
    by rewrite invr_gt0 ltr0n.
  exists delta; split=> // q /dP pq i /pq ple.
  apply/(leq_trans ple).
  rewrite complexr0 big_mkcond [X in (_ <= X)%N]big_mkcond/=.
  apply/leq_sum => x _; rewrite -(RRe_real (normr_real _)) !ltcR lt_min andbC.
  by case: (Re `|x - i| < 1 / 2)%R.
have [->|sp] := poly0Vpos p.
  by exists 1; split=> [//|q _] x _; rewrite mu0.
move: sp; move sp: (size p) => n; case: n sp => // n.
elim: n p => /= [|n IHn] p sp _.
  have p0: p != 0 by apply/eqP => p0; move: sp; rewrite p0 size_poly0.
  by exists 1; split=> [//|q _ x /root_size_gt1] => /(_ p0); rewrite sp.
have p0: p != 0 by apply/eqP => p0; move: sp; rewrite p0 size_poly0.
case/boolP: (all (fun x => x == 0) (dec_roots p)) => [root0|/allPn[x]].
  have r0: dec_roots p = [:: 0].
    case: (dec_roots p) (uniq_dec_roots p) (mem_dec_roots p) root0
        => [|x r] ru memr /allP r0.
      have /closed_rootP [x]: size p != 1 by rewrite sp.
      by move: memr; rewrite p0/= => <-.
    move: (r0 x); rewrite in_cons eqxx/= => /(_ isT) /eqP x0; rewrite x0.
    case: r ru {memr} r0 => // y r /= /andP[+ _] /(_ y).
    rewrite !in_cons negb_or eqxx orbT/= x0 eq_sym.
    by move=> /andP[/negP y0 _] /(_ isT).
  move: (dec_roots_closedP p).
  rewrite r0 big_seq1 subr0 => pE.
  have pn: p`_(size p).-1 != 0 by rewrite -lead_coefE lead_coef_eq0.
  rewrite pE; have -> : \mu_0 p = n.+1.
    move: pE => /(congr1 (fun p : {poly R[i]} => size p)).
    by rewrite size_scale// size_polyXn sp => /eqP; rewrite eqSS => /eqP.
  move: {p p0 sp root0 r0 pE} (p`_(size p).-1) pn => a a0.
  pose d := eps ^+ n.+1 * `|a| / n.+1.*2%:R.
  exists d; split=> [|q []].
    apply/mulr_gt0; last by rewrite invr_gt0 ltr0n double_gt0. 
    apply/mulr_gt0; first exact/exprn_gt0.
    by rewrite normr_gt0.
  rewrite size_scale// size_polyXn => sq qnth.
  move: (qnth ord_max); rewrite coefZ coefXn eqxx mulr1/= => qn.
  have {}qnth (i : 'I_n.+1): `|q`_i| < d.
    move/(_ (lift ord_max i)): qnth.
    rewrite coefZ coefXn /lift/= /bump ltnNge -ltnS ltn_ord add0n.
    move: (ltn_ord i); rewrite ltn_neqAle => /andP[] /negPf -> _.
    by rewrite mulr0 add0r normrN.
  move=> x; rewrite rootE -rootE rootZ// rootE !hornerE expf_eq0/= => /eqP ->.
  rewrite mu_mulC// mu_exp -['X]subr0 mu_XsubC eqxx mul1n big_mkcond big_seq.
  rewrite big_mkcond/=.
  have da2 : d < `|a| / 2.
    rewrite /d -muln2 natrM -mulf_div -[X in _ < X]mul1r -subr_gt0 -mulrBl.
    apply/mulr_gt0; last by apply/mulr_gt0 => //; rewrite normr_gt0.
    rewrite subr_gt0 ltr_pdivrMr ?ltr0n// mul1r.
    apply/(lt_le_trans (y:=1)); last by rewrite ler1n.
    by rewrite exprn_ilt1// ltW.
  have da : d < `|a|.
    apply/(lt_le_trans da2); rewrite ler_pdivrMr// ler_peMr// -[1]/(1%:R).
    by rewrite ler_nat.
  have aqn : `|a| / 2 < `|q`_n.+1|.
    move: da2 => /(lt_trans qn)/(le_lt_trans (lerB_dist _ _)).
    rewrite -[_ - _ < _]subr_gt0 opprD opprK addrA -{2}[`|a|]mulr1.
    rewrite -{2}(divff (x:=2))// mulrCA mulr_natl [_ / _ *+ _]mulr2n opprD.
    by rewrite addrA subrr add0r addrC subr_gt0.
  have {sq} : size q = n.+2.
    apply/anti_leq/andP; split=> //; rewrite ltnNge; apply/negP.
    move=> /leq_sizeP /( _ n.+1 (leqnn _)) q0.
    by move: qn; rewrite q0 subr0 => /(lt_trans da); rewrite ltxx.
  have [->|q0 sq] := eqVneq q 0; first by rewrite size_poly0.
  have qn0 : q`_(size q).-1 != 0 by rewrite -lead_coefE lead_coef_eq0.
  move: (dec_roots_closedP q) => /(congr1 (fun p : {poly R[i]} => size p)).
  rewrite size_scale// size_prod_seq => [|i _]; last first.
    by apply/expf_neq0; rewrite polyXsubC_eq0.
  under eq_bigr do rewrite size_exp_XsubC -addn1.
  rewrite big_split/= sum1_size -addSn -subnBA// subnn subn0 sq => /eq_add_S ->.
  move: qn0; rewrite sq -pred_Sn => qn0.
  rewrite big_seq big_mkcond/=.
  apply/leq_sum => y _; rewrite subr0.
  case/boolP: (y \in dec_roots q) => // yq.
  suff ->: (`|y| < eps)%O by [].
  have [->|y0] := eqVneq y 0; first by rewrite normr0.
  move: yq; rewrite mem_dec_roots q0/= => /rootP.
  rewrite -{1}[q]coefK horner_poly sq big_ord_recr/= addrC => /addr0_eq => yq.
  have y1: `|y| < 1.
    rewrite -(RRe_real (normr_real _)) ltcR ltNge; apply/negP.
    rewrite -lecR RRe_real ?normr_real// => y1.
    have: `|a| / 2 * `|y| ^+ n.+1 < d * n.+1%:R * `|y| ^+ n.
      apply/(lt_le_trans (y:=`|- q`_n.+1 * y ^+ n.+1|)).
        rewrite normrM normrN normrX -subr_gt0 -mulrBl pmulr_rgt0.
          by apply/exprn_gt0; rewrite normr_gt0.
        by rewrite subr_gt0.
      rewrite mulNr yq; apply/(le_trans (ler_norm_sum _ _ _)).
      rewrite -[X in _ * X%:R * _]sum1_ord natr_sum mulr_sumr mulr_suml.
      apply/ler_sum => i _.
      rewrite normrM mulr1; apply/ler_pM.
      - exact/normr_ge0.
      - exact/normr_ge0.
      - exact/ltW.
      by rewrite normrX ler_p1X// -ltnS.
    rewrite exprS mulrA -subr_gt0 -mulrBl pmulr_lgt0; last first.
      exact/(lt_le_trans ltr01)/exprn_ege1.
    rewrite subr_gt0 /d -mul2n natrM invrM ?unitfE// [_ / 2]mulrC -!mulrA.
    rewrite mulVf// mulr1 mulrA mulrC -subr_gt0 -mulrBl.
    rewrite pmulr_lgt0 ?subr_gt0; last by rewrite divr_gt0// normr_gt0.
    move=> /(le_lt_trans y1); rewrite expr_gt1// ?ltW// => /(lt_trans e1).
    by rewrite ltxx.
  have: 1 < n.+1.*2%:R * d / `|a| / `|y| ^+ n.+1.
    rewrite -muln2 natrM -[X in X%:R * _]sum1_ord natr_sum !mulr_suml.
    move/(congr1 (fun x => `|x / (q`_n.+1 * y ^+ n.+1)|)): yq.
    rewrite mulNr normrN divff; last first.
      by rewrite mulf_eq0 negb_or expf_eq0 qn0.
    rewrite normr1 mulr_suml => {1}->.
    apply/(le_lt_trans (ler_norm_sum _ _ _)).
    rewrite -subr_gt0 -sumrB; apply/psumr_gt0 => [i _|]; last first.
      by apply/hasP; exists ord0.
    rewrite subr_gt0 mul1r !normrM normrV; last first.
      by rewrite unitfE mulf_eq0 negb_or expf_eq0 qn0.
    rewrite normrM !normrX [2 * _]mulrC -mulf_div mulrA -subr_gt0 -mulrBl.
    rewrite pmulr_lgt0; last by rewrite invr_gt0 exprn_gt0// normr_gt0.
    rewrite subr_gt0 -2!mulrA ltr_pM//.
    move: aqn; rewrite ltr_pdivrMr// -ltr_pdivrMl ?normr_gt0//.
    rewrite -ltr_pdivlMr ?normr_gt0// => aqn.
    have [->|i0] := (posnP i); first by rewrite expr0 mulr1.
    by rewrite -[X in _ < X]mulr1 ltr_pM// expr_lt1.
  rewrite /d mulrCA divff// mulr1 mulrC -!mulrA divff ?normr_eq0// mulr1 mulrC.
  rewrite -expr_div_n expr_gt1//.
    by rewrite ltr_pdivlMr ?normr_gt0// mul1r.
  exact/divr_ge0/normr_ge0/ltW.
rewrite mem_dec_roots => /andP[_] px x0.
have /IHn {IHn} /(_ isT) [d [d0] dP]: size (p %/ ('X - x%:P)) = n.+1.
  by rewrite size_divp ?polyXsubC_eq0// sp size_XsubC/= subn1 -pred_Sn.
move: (close_rm_root d0 x0 px) => /= [d'][d'0] d'P.
have de0 : 0 < (minr (Re eps) (Re d'))%:C.
  by rewrite ltcR lt_min -!ltcR !(RRe_real (gtr0_real _))// e0.
move: (close_root_deformp p de0) => [d''][d''0]d''P.
exists (minr (Re d') (minr (Re `|lead_coef p|) (Re d'')))%:C; split=> [|q].
  rewrite ltcR !lt_min -!ltcR (RRe_real (gtr0_real d'0)) d'0.
  rewrite (RRe_real (gtr0_real d''0)) (RRe_real (normr_real _)) normr_gt0.
  by rewrite lead_coef_eq0 p0.
have [-> [_]|q0 pq] := eqVneq q 0.
  rewrite sp => /(_ ord_max); rewrite coef0 subr0 -(RRe_real (normr_real _)).
  by rewrite ltcR !lt_min lead_coefE sp -pred_Sn ltxx andbF.
have /d''P/(_ _ px) [y [qy]] : deformp d'' p q.
  apply/(deformpW _ pq).
  by rewrite -{2}(RRe_real (gtr0_real d''0)) lecR !ge_min lexx !orbT.
rewrite -(RRe_real (normr_real _)) ltcR lt_min -!ltcR (RRe_real (normr_real _)).
rewrite !(RRe_real (gtr0_real _))// => /andP[] xye xyd.
have /(d'P _ _ qy)/(_ xyd)/dP pqe : deformp d' p q.
  apply/(deformpW _ pq).
  by rewrite -{2}(RRe_real (gtr0_real d'0)) lecR ge_min lexx.
move=> u pu.
have /divpK pxE: 'X - x%:P %| p by rewrite -root_factor_theorem.
case/boolP: (u \in root (p %/ ('X - x%:P))).
  move=>/pqe.
  rewrite -{2}pxE mu_mul; last by rewrite pxE.
  move=> le.
  have /divpK qyE: 'X - y%:P %| q by rewrite -root_factor_theorem.
  move: (q0); rewrite -{1 3}qyE => q0'.
  under eq_bigr do rewrite mu_mul//.
  rewrite big_split/=; apply/leq_add.
    apply/(leq_trans le)/(uniq_sub_le_big leqnn).
    - move=> a b /=; exact/leq_addr.
    - exact/uniq_dec_roots.
    - exact/uniq_dec_roots.
    - by move=> a; rewrite 2!mem_dec_roots q0 -{3}qyE rootM => /andP[_] ->.
    rewrite mu_XsubC; have [->|//] := eqVneq u x.
    rewrite big_mkcond/= (bigD1_seq y)/=.
    - by rewrite -normrN opprB xye mu_XsubC eqxx add1n.
    - by rewrite mem_dec_roots q0.
    - exact/uniq_dec_roots.
move: pu; rewrite -{1}pxE mem_root => /rootP /rootP.
rewrite rootM root_XsubC => /orP[pu|/eqP ->].
  by rewrite mem_root => /rootP /rootP /negP.
rewrite mem_root => /rootP /rootP px0.
have ->: \mu_x p = 1.
  by rewrite -pxE mu_mul ?pxE// muNroot// mu_XsubC eqxx.
rewrite big_mkcond/= (bigD1_seq y)/=.
- rewrite -normrN opprB xye -[X in (X <= _)%N]/(1 + 0)%N; apply/leq_add => //.
  by rewrite mu_gt0.
- by rewrite mem_dec_roots q0.
- exact/uniq_dec_roots.
Qed.

End ContinuityRoots.

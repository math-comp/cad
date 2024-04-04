From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq ssrnat bigop fintype finfun order ssralg ssrnum poly polydiv complex polyorder.
From mathcomp Require Import matrix topology normedtype classical_sets interval.
Require Import auxresults semialgebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import numFieldTopology.Exports Order.TotalTheory Order.POrderTheory GRing Order Num.Theory.

Local Open Scope type_scope.
Local Open Scope ring_scope.
Local Open Scope sa_scope.
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Ltac mp := 
  match goal with
  | |- (?x -> _) -> _ => have /[swap]/[apply]: x
  end.

Section SAconnected.
Variable (R : rcfType) (n : nat).

Lemma set_of_SAsetC (A : {SAset R^n}) :
  [set` ~: A] = ~` [set` A].
Proof.
rewrite classical_sets.eqEsubset; split; apply/subsetP => /= x; rewrite in_setC/= !inE/= inSAsetC => /negP xAN; apply/negP => xA; apply/xAN.
  by rewrite inE in xA.
by rewrite inE.
Qed.

Definition SAconnected (s : {SAset R ^ n}) :=
  forall (u v : {SAset R^n}),
    @open (subspace [set` s]) [set` u] ->
    @open (subspace [set` s]) [set` v] ->
    s :&: u != SAset0 R n ->
    s :&: v != SAset0 R n ->
    s :<=: (u :|: v) ->
    s :&: u :&: v != SAset0 R n.

Lemma SAconnected_clopen s :
  SAconnected s <->
  forall (u v : {SAset R^n}),
    @open (subspace [set` s]) [set` u] ->
    @closed (subspace [set` s]) [set` v] ->
    s :&: u = s :&: v -> 
    (s :<=: u) || (s :&: u == SAset0 R n).
Proof.
split=> scon u v uo.
  move=> vc uvs; apply/negP => /negP; rewrite negb_or => /andP[su]su0.
  move/(_ u (~: v) uo): scon.
  rewrite set_of_SAsetC openC => /(_ vc su0).
  move: su; rewrite SAsubsetED -SAsetDIr uvs SAsetDIr => /[swap]/[apply].
  rewrite SAsubsetEI SAsetIUr uvs -SAsetIUr SAsetUCr SAsetIT => /(_ (eqxx _)).
  by rewrite -SAsetIA SAsetICr SAsetI0 eqxx.
move=> vo us vs suv; apply/eqP => uv0.
move/(_ u (~: v) uo): scon.
rewrite set_of_SAsetC closedC => /(_ vo).
mp.
  apply/eqP; rewrite eqEsubset; apply/andP; split; apply/SAset_subP => x; rewrite !inSAsetI => /andP[] /[dup] xs -> /=; rewrite inSAsetC => xu.
    apply/negP => xv.
    suff: x \in s :&: u :&: v by rewrite uv0 inSAset0.
    by rewrite !inSAsetI xs xu.
  by move/SAset_subP: suv => /(_ _ xs); rewrite inSAsetU (negPf xu) orbF.
rewrite (negPf us) orbF => /SAset_subP su.
move: vs; have [->|[x]] := (set0Vmem (s :&: v)); first by rewrite eqxx.
rewrite inSAsetI => /andP[] xs xv.
have: x \in s :&: u :&: v by rewrite !inSAsetI xs (su _ xs).
by rewrite uv0 inSAset0.
Qed.

Lemma SAconnected_closed s :
  SAconnected s <-> 
  forall (u v : {SAset R^n}),
    @closed (subspace [set` s]) [set` u] ->
    @closed (subspace [set` s]) [set` v] ->
    s :&: u != SAset0 R n ->
    s :&: v != SAset0 R n ->
    s :<=: (u :|: v) ->
    s :&: u :&: v != SAset0 R n.
Proof.
by split=> scon u v ut vt su0 sv0 suv; apply/eqP => suv0;
move: (scon (~: u) (~: v));
rewrite !set_of_SAsetC ?openC ?closedC => /(_ ut vt);
(mp; [rewrite -SAsubsetED; apply/negP => /SAset_subP su;
  move/negP: sv0; apply; rewrite -subset0; apply/SAset_subP => x;
  rewrite -suv0 !inSAsetI => /andP[xs xv];
  rewrite xs (su _ xs)//|]);
(mp; [rewrite -SAsubsetED; apply/negP => /SAset_subP sv;
  move/negP: su0; apply; rewrite -subset0; apply/SAset_subP => x;
  rewrite -suv0 !inSAsetI => /andP[xs xu];
  rewrite xs xu (sv _ xs)//|]);
rewrite SAsubsetED /SAsetD SAsetCU !SAsetCK SAsetIA suv0 eqxx => /(_ isT);
rewrite -SAsetIA -SAsetCU -SAsubsetED suv.
Qed.

Definition locally_constant_on (T : topologicalType) (U : Type) (f : T -> U)
    (S : set T) (v : U) :=
  {in S, forall x, f x = v -> exists O,
    @open (subspace S) O /\
    x \in O /\
    {in (S `&` O)%classic, forall y, f y = v}}.

Definition locally_constant (T : topologicalType) (U : Type) (f : T -> U) (S : set T) :=
  {in S, forall x, exists O,
    @open (subspace S) O /\
    x \in O /\
    {in (S `&` O)%classic, forall y, f x = f y}}.

Lemma open_subspace_ballP (F : numDomainType) (T : pseudoMetricType F) (S : set T) (A : set T) :
  @open (subspace S) A <->
  forall x, (x \in A `&` S)%classic ->
    exists eps, 0 < eps /\ (ball x eps `&` S `<=` A)%classic.
Proof.
rewrite openE/=; split=> [/subsetP Aopen x|Aopen].
  rewrite in_setI => /andP[] /[dup] xA /Aopen + xS.
  rewrite /interior inE => /nbhs_ballP [] e /= e0.
  rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball xS setIC.
  by exists e.
apply/subsetP => x xA.
rewrite /interior inE; apply/nbhs_ballP.
have [xS|xnS] := boolP (x \in S); last first.
  exists 1 => //=.
  apply/subsetP => y.
  rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball.
  by rewrite (negPf xnS) inE => /= ->.
move: (Aopen x); rewrite in_setI xA => /(_ xS) []e []e0 xSA.
exists e => //=.
by rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball xS setIC.
Qed.

Lemma SAconnected_locally_constant_on_constant m (f : {SAfun R^n -> R^m})
    (S : {SAset R^n}) (x : 'rV_n) :
  x \in S ->
  SAconnected S ->
  locally_constant_on f [set` S] (f x) ->
  {within [set` S], continuous f} ->
  {in S, forall y, f y = f x}.
Proof.
case: m f => [|m] f.
  move=> _ _ _ _ u _.
  by apply/rowP; case.
move=> xS S_con f_const /continuousP/= fcon y yS.
apply/eqP/negP => /negP yx.
move: (S_con (SApreimset f (SAset_seq [:: f x])) (SApreimset f (~: (SAset_seq [:: f x])))).
have /[swap]/[apply]: @open (subspace [set` S]) [set` SApreimset f [set f x]].
  apply/open_subspace_ballP => /= z.
  rewrite in_setI mem_setE inSApreimset inSAset_seq mem_seq1 => /andP[] /eqP zy zS.
  case: (f_const z) => //= O [] + [].
  rewrite openE/= => /subsetP /[apply].
  rewrite /interior inE => /nbhs_ballP [] e /= e0 /subsetP zeO fz.
  exists e; split=> //.
  apply/subsetP => u; rewrite in_setI => /andP[] uz uS.
  rewrite mem_setE inSApreimset inSAset_seq mem_seq1; apply/eqP/fz.
  rewrite in_setI uS; apply/zeO.
  rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball zS.
  by rewrite in_setI uS.
have /[swap]/[apply]: @open (subspace [set` S]) [set` SApreimset f (~: [set f x])].
  have ->: [set` SApreimset f (~: [set f x])] = f @^-1` ~` (set1 (f x)).
    by apply/seteqP; split; apply/subsetP => z; rewrite !inE/= inSApreimset inSAsetC inSAset1 => /eqP.
    apply/fcon; rewrite -open_subspace_setT.
    apply/open_subspace_ballP => /= z.
    rewrite setIT in_setC => zx.
    exists `|z - f x|; split.
      rewrite normr_gt0 subr_eq0; apply/eqP => xz.
      move: zx; rewrite unfold_in/==> /negP; apply.
      by rewrite inE/=.
    rewrite setIT; apply/subsetP => t.
    rewrite -ball_normE inE/= in_setC => tx.
    apply/negP; rewrite inE => /= tE.
    by rewrite tE ltxx in tx.
have /[swap]/[apply]: S :&: SApreimset f [set f x] != SAset0 R n.
  rewrite -subset0; apply/negP => /SAset_subP/(_ x).
  by rewrite inSAset0 inSAsetI xS inSApreimset inSAset_seq => /(_ (mem_head _ _)).
have /[swap]/[apply]: S :&: SApreimset f (~: [ set f x]) != SAset0 R n.
  rewrite -subset0; apply/negP => /SAset_subP/(_ y).
  rewrite inSAset0 inSAsetI yS inSApreimset inSAsetC inSAset_seq mem_seq1.
  by move=> /(_ yx).
rewrite -SApreimsetU SAsetUCr SApreimsetT => /(_ (subsetT _)).
by rewrite -SAsetIA -SApreimsetI SAsetICr SApreimset0 SAsetI0 eqxx.
Qed.

Lemma SAconnected_locally_constant_constant m (f : {SAfun R^n -> R^m}) (S : {SAset R^n}):
  SAconnected S ->
  locally_constant f [set` S] ->
  {in S &, forall x y, f x = f y}.
Proof.
case: m f => [|m] f.
  move=> _ _ u v _ _.
  by apply/rowP; case.
move=> S_con f_const x y xS yS.
apply/eqP/negP => /negP xy.
move: (S_con (SApreimset f (SAset_seq [:: f x])) (SApreimset f (~: (SAset_seq [:: f x])))).
have /[swap]/[apply]: @open (subspace [set` S]) [set` SApreimset f [ set f x]].
  apply/open_subspace_ballP => /= z.
  rewrite in_setI mem_setE inSApreimset inSAset_seq mem_seq1 => /andP[] /eqP zx zS.
  case: (f_const z) => //= O [] + [].
  rewrite openE/= => /subsetP /[apply].
  rewrite /interior inE => /nbhs_ballP [] e /= e0 /subsetP zeO fz.
  exists e; split=> //.
  apply/subsetP => u; rewrite in_setI => /andP[] uz uS.
  rewrite mem_setE inSApreimset inSAset_seq mem_seq1 -zx; apply/eqP/esym/fz.
  rewrite in_setI uS; apply/zeO.
  rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball zS.
  by rewrite in_setI uS.
have /[swap]/[apply]: @open (subspace [set` S]) [set` SApreimset f (~: [ set f x])].
  apply/open_subspace_ballP => /= z.
  rewrite in_setI mem_setE inSApreimset inSAsetC inSAset_seq mem_seq1 => /andP[] zx zS.
  case: (f_const z) => //= O [] + [].
  rewrite openE/= => /subsetP /[apply].
  rewrite /interior inE => /nbhs_ballP [] e /= e0 /subsetP zeO => fz.
  exists e; split=> //.
  apply/subsetP => u; rewrite in_setI => /andP[] uz uS.
  rewrite mem_setE inSApreimset inSAsetC inSAset_seq mem_seq1 -(fz u)//.
  rewrite in_setI uS; apply/zeO.
  rewrite -[ball _ _]/(subspace_ball _ _) /subspace_ball zS.
  by rewrite in_setI uS.
have /[swap]/[apply]: S :&: SApreimset f [ set f x] != SAset0 R n.
  rewrite -subset0; apply/negP => /SAset_subP/(_ x).
  by rewrite inSAset0 inSAsetI xS inSApreimset inSAset_seq => /(_ (mem_head _ _)).
have /[swap]/[apply]: S :&: SApreimset f (~: [ set f x]) != SAset0 R n.
  rewrite -subset0; apply/negP => /SAset_subP/(_ y).
  rewrite inSAset0 inSAsetI yS inSApreimset inSAsetC inSAset_seq mem_seq1.
  by rewrite eq_sym => /(_ xy).
rewrite -SApreimsetU SAsetUCr SApreimsetT => /(_ (subsetT _)).
by rewrite -SAsetIA -SApreimsetI SAsetICr SApreimset0 SAsetI0 eqxx.
Qed.

Lemma subseq_sorted_continuous_SAfun (f g : seq (SAfunltType R n)) (s : {SAset R^n}) :
  {in s, forall x, uniq [seq (f : {SAfun R^n -> R^1}) x | f <- f]}
  -> {in s, forall x, uniq [seq (f : {SAfun R^n -> R^1}) x | f <- g]}
  -> (forall i : 'I_(size f), {within [set` s], continuous f`_i})
  -> (forall i : 'I_(size g), {within [set` s], continuous g`_i})
  -> SAconnected s
  -> {in s, forall x, subseq [seq (f : {SAfun R^n -> R^1}) x | f <- f] [seq (f : {SAfun R^n -> R^1}) x | f <- g]}
  -> (exists t : seq nat,
       subseq t (iota 0 (size g)) /\
       {in s, forall x, [seq (f : {SAfun R^n -> R^1}) x | f <- f] = [seq g`_i x | i <- t]})
.
Proof.
move=> funiq guniq fcont gcont scon fg.
case: (set0Vmem s) => [->|[] x xs].
  exists nil; split; first exact/sub0seq.
  by move=> y; rewrite inSAset0.
move: (fg x xs) => /(subseq_nth_iota 0)[] /= r.
rewrite size_map => -[] rg fE.
move: (fE) => /(congr1 size); rewrite !size_map => fr.
exists r; split=> // y ys.
apply/(@eq_from_nth _ 0); rewrite !size_map// => i ilt.
rewrite (nth_map 0)// (nth_map 0); last by rewrite -fr.
have rig: (r`_i < size g)%N.
  move/mem_subseq: rg => /(_ r`_i); mp.
    by apply/mem_nth; rewrite -fr.
  by rewrite mem_iota.
have fgx: SAfun_sub f`_i g`_(r`_i) x = 0.
  move: fE => /(congr1 (fun f => f`_i)).
  rewrite (nth_map 0)// (nth_map 0); last by rewrite -fr.
  rewrite SAfun_subE (nth_map 0)// => ->.
  exact/subrr.
suff: (SAfun_sub f`_i g`_(r`_i) y = SAfun_sub f`_i g`_(r`_i) x).
  by move=> /eqP; rewrite fgx SAfun_subE subr_eq0 => /eqP.
apply/(SAconnected_locally_constant_on_constant xs scon) => // {ys}y; last first.
  apply/(@eq_continuous (subspace [set` s]) _ (fun y => f`_i y - g`_(r`_i) y)).
    by move=> z; rewrite SAfun_subE.
  move=> z.
  apply/continuousB.
    exact/(fcont (Ordinal ilt)).
  exact/(gcont (Ordinal rig)).
rewrite inE/= fgx SAfun_subE => ys /eqP.
rewrite subr_eq0 => /eqP fgy.
set e := (min (\big[min/1%R]_(i < size f) \big[min/1%R]_(j < size f | i != j) `|f`_j y - f`_i y|)
    (\big[min/1%R]_(i < size g) \big[min/1%R]_(j < size g | i != j) `|g`_j y - g`_i y|)) / 2.
have e0: 0 < e.
  apply/divr_gt0 => //.
  rewrite lt_min; apply/andP; split; apply/lt_bigmin => //= j _; apply/lt_bigmin => // k jk; rewrite normr_gt0 subr_eq0; apply/eqP => jE;
      move: (ltn_ord j) (ltn_ord k); rewrite -{2 4}(size_map (fun f : {SAfun R^n -> R^1} => f y)) => jlt klt.
    move: (funiq y ys) => /(nth_uniq 0 jlt klt).
    rewrite size_map in jlt klt.
    by rewrite [RHS](inj_eq (@ord_inj _)) (negPf jk) (nth_map 0)// (nth_map 0)// jE eqxx.
  move: (guniq y ys) => /(nth_uniq 0 jlt klt).
  rewrite size_map in jlt klt.
  by rewrite [RHS](inj_eq (@ord_inj _)) (negPf jk) (nth_map 0)// (nth_map 0)// jE eqxx.
exists ((\big[setI/setT]_(i < size f) f`_i @^-1` (ball (f`_i y) e)) `&`
    \big[setI/setT]_(i < size g) g`_i @^-1` (ball (g`_i y) e)).
split.
  apply/openI; apply/open_bigcap => /= j _.
    by move: (fcont j) => /continuousP; apply; apply/ball_open.
  by move: (gcont j) => /continuousP; apply; apply/ball_open.
split.
  by rewrite in_setI -!bigcap_seq !unfold_in/=; apply/andP; split; rewrite inE/= => z _ /=; apply/ballxx.
move=> z; rewrite !in_setI -!bigcap_seq mem_setE/= => /andP[zs].
rewrite !unfold_in => /andP[]; rewrite !inE/= => zf zg.
apply/eqP; rewrite SAfun_subE subr_eq0; apply/eqP.
move: (fg z zs) => /mem_subseq/(_ (f`_i z)); mp.
  by apply/map_f/mem_nth.
move=> /mapP[/=] _ /(nthP 0)[] j jg <- fzE.
rewrite fzE; congr (nth _ g _ z).
apply/eqP/negP => /negP ji.
move: (zf (Ordinal ilt) (mem_index_enum _)) => /=.
move: (zg (Ordinal jg) (mem_index_enum _)) => /=.
rewrite -ball_normE/= fzE fgy => gyz ryz.
have: (`|g`_(r`_i) y - g`_j y| < e * 2)%R.
  rewrite -(subrBB (g`_j z)) mulr_natr mulr2n.
  exact/(le_lt_trans (ler_normB _ _))/ltrD.
rewrite /e mulrAC -mulrA divff ?pnatr_eq0// mulr1 lt_min => /andP[_].
move=> /bigmin_gtP[_] /(_ (Ordinal jg) isT) /bigmin_gtP[_] /(_ (Ordinal rig)).
by rewrite -(inj_eq val_inj)/= ltxx => /(_ ji).
Qed.

End SAconnected.

Lemma SAset_itv_connected (R : rcfType) (I : interval R) :
  SAconnected (SAset_itv I).
Proof.
move=> u v uopen vopen.
case: (set0Vmem (SAset_itv I :&: u)) => [->|[] x]; first by rewrite eqxx => + _.
rewrite inSAsetI => /andP[] xI xu _.
case: (set0Vmem (SAset_itv I :&: v)) => [->|[] y]; first by rewrite eqxx.
rewrite inSAsetI => /andP[] yI yv _.
wlog: x y u v xI xu yI yv uopen vopen / x ord0 ord0 <= y ord0 ord0 => xy.
  move: (le_total (x ord0 ord0) (y ord0 ord0)) => /orP[|yx]; first exact/xy.
  rewrite SAsetUC -SAsetIA [u :&: v]SAsetIC SAsetIA.
  by move: yx; apply/xy.
have uy: y \in SAsetUB (SAset_itv `[(x ord0 ord0), (y ord0 ord0)]%R :&: u).
  apply/inSAsetUB => z; rewrite inSAsetI inSAset_itv in_itv/=.
  by move=> /andP[]/andP[_].
move: (@SAset_supP _ (SAset_itv `[x ord0 ord0, y ord0 ord0] :&: u)).
mp.
  apply/negP => /SAsetP/(_ x).
  by rewrite inSAsetI inSAset_itv in_itv/= lexx xy xu inSAset0.
mp=> [|[] z ubu].
  by apply/negP => /SAsetP/(_ y); rewrite uy inSAset0.
move: uy; rewrite ubu inSAset_itv in_itv/= andbT => zy.
have: \row__ z \in SAset_itv `[z, +oo[%R.
  by rewrite inSAset_itv in_itv/= mxE lexx.
rewrite -ubu => /inSAsetUB; rewrite mxE => zub.
move: (zub x); rewrite inSAsetI inSAset_itv in_itv/= lexx xy xu => /(_ isT) xz.
move=> /SAset_subP Iuv.
have /SAset_subP xyI: SAset_itv `[x ord0 ord0, y ord0 ord0] :<=: SAset_itv I.
  apply/SAset_subP => a.
  case: I xI yI {Iuv uopen vopen} => l r.
  rewrite !inSAset_itv !itv_boundlr => /andP[] lx _ /andP[] _ yr /andP[] xa ay.
  apply/andP; split; first exact/(le_trans lx).
  exact/(le_trans ay).
have zI: \row__ z \in SAset_itv I.
  by apply/xyI; rewrite inSAset_itv in_itv/= mxE xz.
move: (Iuv _ zI); rewrite inSAsetU => /orP[zu|zv].
  move: zy; rewrite le_eqVlt => /orP[/eqP|] zy.
    apply/negP => /SAsetP/(_ y).
    rewrite 2!inSAsetI inSAset0 yv andbT => /negP; apply.
    apply/andP; split.
      by apply/xyI; rewrite inSAset_itv in_itv/= xy lexx.
    move: zu; congr (_ \in u); apply/eqP; rewrite rowPE forall_ord1 mxE.
    exact/eqP.
  move: uopen => /open_subspace_ballP/(_ (\row__ z)); mp.
    rewrite in_setI mem_setE/= zu mem_setE inSAset_itv mxE/=.
    by move: zI; rewrite inSAset_itv mxE.
  move=> [] /= e [] e0 /subsetP eu.
  move: (zub (\row__ (Order.min (z + e / 2) (y ord0 ord0))))%R; mp; last first.
    rewrite mxE leNgt lt_min zy andbT -[X in (X < _)%R]addr0 => /negP; elim.
    apply/ler_ltD; first exact/lexx.
    exact/divr_gt0.
  rewrite inSAsetI inSAset_itv in_itv/= mxE.
  rewrite le_min xy -[x _ _]addr0 ge_min lexx orbT !andbT; apply/andP; split.
    by apply/lerD => //; apply/divr_ge0 => //; apply/ltW.
  suff: \row__ Num.min (z + e / 2)%R (y ord0 ord0) \in [set` u].
    by rewrite mem_setE.
  apply/eu; rewrite in_setI -ball_normE/=.
  (* N.B. This is a very weird way to do it. *)
  rewrite mem_setE/= unfold_in/= [X in isPOrder.lt _ X]mx_normrE/=.
  apply/andP; split; last first.
    rewrite mem_setE; apply/xyI; rewrite inSAset_itv in_itv/= mxE.
    rewrite ge_min lexx orbT le_min xy 2!andbT -[x _ _]addr0.
    by apply/lerD => //; apply/divr_ge0 => //; apply/ltW.
  apply/bigmax_lt => //; case; case; case=> //= ltr01; case; case=> // ltr01' _.
  rewrite !mxE; apply/ltr_normlP; split; rewrite -subr_gt0.
    rewrite opprK addrA subr_gt0 gt_min addrC; apply/orP; left.
    apply/ltr_leD; last exact/lexx.
    rewrite ltr_pdivrMr// mulr_natr mulr2n -[X in (X < _)%R]addr0.
    by apply/ler_ltD => //; apply/lexx.
  rewrite opprB addrCA -opprB subr_gt0 lt_min; apply/andP; split; last first.
    by rewrite -[X in (_ < X)%R]addr0; apply/ltrD => //; rewrite oppr_lt0.
  apply/ler_ltD; first exact/lexx.
  rewrite ltr_pdivlMr// -subr_gt0 mulNr opprK -[X in (X + _)%R]mulr1.
  by rewrite -mulrDr; apply/mulr_gt0 => //; apply/addr_gt0.
move: xz; rewrite le_eqVlt => /orP[/eqP|] xz.
  apply/negP => /SAsetP/(_ x).
  rewrite 2!inSAsetI inSAset0 xu andbT => /negP; apply.
  apply/andP; split.
    by apply/xyI; rewrite inSAset_itv in_itv/= xy lexx.
  move: zv; congr (_ \in v); apply/eqP; rewrite rowPE forall_ord1 mxE.
  exact/eqP.
move: vopen => /open_subspace_ballP/(_ (\row__ z)); mp.
  rewrite in_setI mem_setE/= zv mem_setE inSAset_itv mxE/=.
  by move: zI; rewrite inSAset_itv mxE.
move=> [] /= e [] e0 /subsetP ev.
have: (\row__ (Order.max (z - e / 2) (x ord0 ord0))) \in ~: SAset_itv `[z, +oo[%R.
  rewrite inSAsetC inSAset_itv in_itv/= mxE andbT -ltNge gt_max xz andbT.
  rewrite -[X in (_ < X)%R]addr0; apply/ler_ltD; first exact/lexx.
  by rewrite oppr_lt0; apply/divr_gt0.
rewrite -ubu => /inSAsetUBC[] t.
rewrite inSAsetI inSAset_itv in_itv/= mxE gt_max => -[] /andP[]/andP[_] ty tu.
move=> /andP[] zt xt.
apply/negP => /SAsetP/(_ t); rewrite 2!inSAsetI inSAset0 tu andbT => /negP.
apply; apply/andP; split.
  by apply/xyI; rewrite inSAset_itv in_itv/= (ltW xt).
suff: t \in [set` v] by rewrite mem_setE.
apply/ev; rewrite in_setI -ball_normE/=.
(* N.B. This is a very weird way to do it. *)
rewrite mem_setE/= unfold_in/= [X in isPOrder.lt _ X]mx_normrE/=.
apply/andP; split; last first.
  by rewrite mem_setE; apply/xyI; rewrite inSAset_itv in_itv/= (ltW xt).
apply/bigmax_lt => //; case; case; case=> //= ltr01; case; case=> // ltr01' _.
rewrite !mxE; apply/ltr_normlP; split; rewrite -subr_gt0.
  rewrite opprK addrA subr_gt0 -[X in (X < _)%R]add0r; apply/ltr_leD => //.
  move: (zub t); mp; last by congr (t _ _ <= z)%R; apply/val_inj.
  by rewrite inSAsetI inSAset_itv in_itv/= (ltW xt) ty.
rewrite opprB addrCA -opprB subr_gt0.
have ze: z - e < z - e / 2.
  apply/ler_ltD; first exact/lexx.
  rewrite -subr_gt0 -opprD opprB subr_gt0.
  rewrite ltr_pdivrMr// -subr_gt0 -[X in (_ - X)%R]mulr1 -mulrBr.
  by rewrite mulr2n -addrA subrr addr0 mulr1.
by apply/(lt_trans ze); move: zt; congr (_ < t _ _)%R; apply/val_inj.
Qed.

Lemma SAimset_connected (R : rcfType) n m (s : {SAset R^n}) (f : {SAfun R^n -> R^m}) :
  SAconnected s -> {within [set` s], continuous f} -> SAconnected (SAimset f s).
Proof.
move=> scon /continuousP fcon u v.
move=> /open_subspaceP[] U [] /fcon /open_subspaceP[] Us [] Uso UsE UE.
move=> /open_subspaceP[] V [] /fcon /open_subspaceP[] Vs [] Vso VsE VE.
move=> fsu fsv fsuv.
move: (scon (SApreimset f u) (SApreimset f v)).
mp.
  apply/open_subspaceP; exists Us; split=> //.
  rewrite UsE; apply/seteqP; split; apply/subsetP => x;
      rewrite !in_setI !mem_setE inSApreimset => /andP[] fxu xs;
      apply/andP; split=> //.
    suff: f x \in (U `&` [set` SAimset f s])%classic.
      by rewrite UE in_setI mem_setE => /andP[].
    rewrite in_setI mem_setE; apply/andP; split=> //.
    exact/inSAimset.
  suff: f x \in (U `&` [set` SAimset f s])%classic.
    by rewrite in_setI => /andP[].
  rewrite UE in_setI !mem_setE; apply/andP; split=> //.
  exact/inSAimset.
mp.
  apply/open_subspaceP; exists Vs; split=> //.
  rewrite VsE; apply/seteqP; split; apply/subsetP => x;
      rewrite !in_setI !mem_setE inSApreimset => /andP[] fxv xs;
      apply/andP; split=> //.
    suff: f x \in (V `&` [set` SAimset f s])%classic.
      by rewrite VE in_setI mem_setE => /andP[].
    rewrite in_setI mem_setE; apply/andP; split=> //.
    exact/inSAimset.
  suff: f x \in (V `&` [set` SAimset f s])%classic.
    by rewrite in_setI => /andP[].
  rewrite VE in_setI !mem_setE; apply/andP; split=> //.
  exact/inSAimset.
mp.
  move: fsu; apply/contraNN => /eqP fsu.
  apply/SAsetP => x; rewrite inSAsetI inSAset0.
  apply/negP => /andP[] /SAimsetP[] y ys -> fyu.
  suff: y \in SAset0 R n by rewrite inSAset0.
  by rewrite -fsu inSAsetI ys inSApreimset.
mp.
  move: fsv; apply/contraNN => /eqP fsv.
  apply/SAsetP => x; rewrite inSAsetI inSAset0.
  apply/negP => /andP[] /SAimsetP[] y ys -> fyv.
  suff: y \in SAset0 R n by rewrite inSAset0.
  by rewrite -fsv inSAsetI ys inSApreimset.
mp.
  apply/SAset_subP => x xs; rewrite inSAsetU 2!inSApreimset.
  move: fsuv => /SAset_subP/(_ (f x) (inSAimset _ xs)).
  by rewrite inSAsetU.
apply/contraNN => /eqP fsuv0.
apply/SAsetP => x; rewrite 2!inSAsetI 2!inSApreimset inSAset0.
apply/negP => /andP[]/andP[] xs fxu fxv.
suff: f x \in SAset0 R m by rewrite inSAset0.
rewrite -fsuv0 2!inSAsetI fxu fxv !andbT.
exact/inSAimset.
Qed.

Lemma SAselect_continuous R n m s : continuous (SAselect R n m s).
Proof.
case: m => [|m].
  apply/continuousP => /= a _.
  have [->|/set0P[] x ax] := eqVneq a set0.
    rewrite preimage_set0; exact/open0.
  suff ->: a = setT by rewrite preimage_setT; exact/openT.
  rewrite -classical_sets.subTset; apply/subsetP => y _.
  suff ->: y = x by rewrite inE.
  by apply/rowP; case.
case: n => [|n].
  apply/(eq_continuous (f:=fun=> 0)); last exact/cst_continuous.
  move=> x; rewrite SAselectE; apply/rowP => i.
  by rewrite !mxE nth_default// size_ngraph.
apply/continuousP => /= a; rewrite -open_subspace_setT => /open_subspace_ballP/= aopen.
rewrite -open_subspace_setT; apply/open_subspace_ballP => /= x.
rewrite setIT => xa.
move: aopen => /(_ (SAselect _ _ _ s x)) => /=.
rewrite setIT => /(_ xa)[] e [] e0 /subsetP ea.
exists e; split=> //; apply/subsetP => y.
rewrite -ball_normE inE/= [X in (X < _)%R]mx_normrE => -[] + _.
move=> /bigmax_ltP[_]/= xye.
apply/ea; rewrite -ball_normE inE/=; split=> //.
rewrite [X in (X < _)%R]mx_normrE; apply/bigmax_ltP; split=> //=.
case=> i j _; rewrite !SAselectE/= !mxE.
case: (ltnP (s`_j) n.+1) => jn; last first.
  by rewrite nth_default ?size_ngraph// nth_default ?size_ngraph// subrr normr0.
have ->: s`_j = Ordinal jn by [].
rewrite !nth_ngraph.
move: (xye (i, Ordinal jn) isT); rewrite /= !mxE.
by congr (`|x _ _ - y _ _| < e)%R; apply/val_inj; case: i; case.
Qed.

Lemma SAcast_connected (R : rcfType) n m (s : {SAset R^n}) :
  SAconnected s -> SAconnected (SAset_cast m s).
Proof.
move=> scon.
rewrite SAset_castE_select.
apply/SAimset_connected => //=.
apply/(continuous_subspaceW (B:=setT)).
  exact/classical_sets.subsetT.
move=> x y.
move: (@SAselect_continuous R n m (iota 0 m) x y) => /[apply].
by rewrite nbhs_subspaceT.
Qed.

Lemma SAconnected0 (R : rcfType) n :
  SAconnected (SAset0 R n).
Proof. by move=> s t _ _ _; rewrite SAset0I eqxx. Qed.

Lemma SAconnectedX (R : rcfType) n m (s : {SAset R^n}) (t : {SAset R^m}) :
  SAconnected s -> SAconnected t -> SAconnected (s :*: t).
Proof.
case: n s => [|n] s.
  case: (set0Vmem s) => [->|[] y ys].
    by rewrite SAset0X => _ _; apply/SAconnected0.
  suff ->: s :*: t = t by [].
  apply/eqP/SAsetP => x; rewrite inSAsetX.
  have ->: lsubmx x \in s.
    by move: ys; congr (_ \in s); apply/rowP; case.
  congr (_ \in t); apply/rowP => i.
  by rewrite mxE; congr (x _ _); apply/val_inj.
case: m t => [|m] t.
  case: (set0Vmem t) => [->|[]y yt].
    by rewrite SAsetX0 => _ _; apply/SAconnected0.
  suff ->: s :*: t = SAset_cast (n.+1 + 0) s.
    by move=> scon _; apply/SAcast_connected.
  apply/eqP/SAsetP => x; rewrite inSAsetX inSAset_castnD.
  have ->: rsubmx x \in t.
    by move: yt; congr (_ \in t); apply/rowP; case.
  have ->: rsubmx x == 0 by apply/eqP/rowP; case.
  by rewrite !andbT.
move=> scon tcon u v /open_subspace_ballP/= uopen /open_subspace_ballP/= vopen.
case: (set0Vmem (s :*: t :&: u)) => [-> +|[] x xstu] _; first by rewrite eqxx.
case: (set0Vmem (s :*: t :&: v)) => [-> +|[] y ystv] _; first by rewrite eqxx.
move=> /SAset_subP stuv.
move: (scon (SAimset (SAselect _ _ _ (iota 0 n.+1)) (s :*: t :&: u)) (SAimset (SAselect _ _ _ (iota 0 n.+1)) (s :*: t :&: v))).
mp.
  apply/open_subspace_ballP => a.
  rewrite in_setI !mem_setE => /andP[] /SAimsetP[] b.
  rewrite inSAsetI => /andP[] bst bu ->.
  rewrite SAselectE => bs.
  move: (uopen b); rewrite in_setI !mem_setE bu => /(_ bst)[] e [] e0 /subsetP eu.
  exists e; split=> //.
  apply/subsetP => c; rewrite in_setI !mem_setE => /andP[] + cs.
  rewrite -ball_normE inE/= [`|_|]mx_normrE => /bigmax_ltP[_]/= ce.
  suff: c \in (SAimset (SAselect R (n.+1 + m.+1) n.+1 (iota 0 n.+1)) (s :*: t :&: u)) by [].
  apply/SAimsetP; exists (row_mx c (rsubmx b)); last first.
    by rewrite SAselect_iotal row_mxKl.
  move: bst; rewrite inSAsetX => /andP[_] bt.
  rewrite inSAsetI inSAsetX row_mxKl row_mxKr cs bt/=.
  move: (eu (row_mx c (rsubmx b))); rewrite mem_setE; apply.
  rewrite -ball_normE inE/=; split; last first.
    by rewrite inSAsetX row_mxKl row_mxKr cs.
  rewrite [`|_|]mx_normrE; apply/bigmax_lt => //=; case=> i j _ /=.
  rewrite -(@splitK n.+1 m.+1 j) !mxE unsplitK.
  case: (@split n.+1 m.+1 j) => /= k; last first.
    by rewrite mxE subrr normr0.
  move: (ce (i, k) isT); rewrite !mxE/= (nth_iota _ _ (n:=n.+1))//.
  have ->: (0 + k = lshift m.+1 k)%N by [].
  rewrite nth_ngraph; congr (`|b _ _ - _| < e)%R.
  by apply/val_inj; case: i; case.
mp.
  apply/open_subspace_ballP => a.
  rewrite in_setI !mem_setE => /andP[] /SAimsetP[] b.
  rewrite inSAsetI => /andP[] bst bv ->.
  rewrite SAselectE => bs.
  move: (vopen b); rewrite in_setI !mem_setE bv => /(_ bst)[] e [] e0 /subsetP ev.
  exists e; split=> //.
  apply/subsetP => c; rewrite in_setI !mem_setE => /andP[] + cs.
  rewrite -ball_normE inE/= [`|_|]mx_normrE => /bigmax_ltP[_]/= ce.
  suff: c \in (SAimset (SAselect R (n.+1 + m.+1) n.+1 (iota 0 n.+1)) (s :*: t :&: v)) by [].
  apply/SAimsetP; exists (row_mx c (rsubmx b)); last first.
    by rewrite SAselect_iotal row_mxKl.
  move: bst; rewrite inSAsetX => /andP[_] bt.
  rewrite inSAsetI inSAsetX row_mxKl row_mxKr cs bt/=.
  move: (ev (row_mx c (rsubmx b))); rewrite mem_setE; apply.
  rewrite -ball_normE inE/=; split; last first.
    by rewrite inSAsetX row_mxKl row_mxKr cs.
  rewrite [`|_|]mx_normrE; apply/bigmax_lt => //=; case=> i j _ /=.
  rewrite -(@splitK n.+1 m.+1 j) !mxE unsplitK.
  case: (@split n.+1 m.+1 j) => /= k; last first.
    by rewrite mxE subrr normr0.
  move: (ce (i, k) isT); rewrite !mxE/= (nth_iota _ _ (n:=n.+1))//.
  have ->: (0 + k = lshift m.+1 k)%N by [].
  rewrite nth_ngraph; congr (`|b _ _ - _| < e)%R.
  by apply/val_inj; case: i; case.
mp.
  apply/negP => /SAsetP/(_ (lsubmx x)).
  move: (xstu); rewrite !inSAsetI inSAsetX inSAset0 => /andP[]/andP[] xs xt xu /negP; apply.
  by rewrite xs; apply/SAimsetP; exists x => //; rewrite SAselect_iotal.
mp.
  apply/negP => /SAsetP/(_ (lsubmx y)).
  move: (ystv); rewrite !inSAsetI inSAsetX inSAset0 => /andP[]/andP[] ys yt yv /negP; apply.
  by rewrite ys; apply/SAimsetP; exists y => //; rewrite SAselect_iotal.
mp.
  apply/SAset_subP => z zs.
  move: (xstu); rewrite !inSAsetI inSAsetX => /andP[]/andP[] xs xt xu.
  have /stuv: (row_mx z (rsubmx x)) \in s :*: t.
    by rewrite inSAsetX row_mxKl row_mxKr zs.
  rewrite !inSAsetU => /orP[zu|zv]; apply/orP; [left|right]; apply/SAimsetP; exists (row_mx z (rsubmx x)).
  - by rewrite inSAsetI inSAsetX row_mxKl row_mxKr zs xt.
  - by rewrite SAselect_iotal row_mxKl.
  - by rewrite inSAsetI inSAsetX row_mxKl row_mxKr zs xt.
  - by rewrite SAselect_iotal row_mxKl.
move=> {x xstu y ystv}; set sfib := (_ :&: _ :&: _).
case: (set0Vmem sfib) => [->|[] x]; first by rewrite eqxx.
rewrite /sfib !inSAsetI => {sfib} /andP[]/andP[] xs.
move=> /SAimsetP[] yz.
rewrite -(hsubmxK yz) inSAsetI inSAsetX SAselect_iotal row_mxKl row_mxKr.
move: (rsubmx yz) => y /andP[]/andP[_] yt /[swap] <- yu {yz}.
move=> /SAimsetP[] yz.
rewrite -(hsubmxK yz) inSAsetI inSAsetX SAselect_iotal row_mxKl row_mxKr.
move: (rsubmx yz) => z /andP[]/andP[_] zt /[swap] <- zv {yz} _.
move: (tcon (SApreimset (SAjoin (SAfun_const _ x) (SAid _ _)) (s :*: t :&: u)) (SApreimset (SAjoin (SAfun_const _ x) (SAid _ _)) (s :*: t :&: v))).
mp.
  apply/open_subspace_ballP => /= a.
  rewrite in_setI !mem_setE inSApreimset SAjoinE SAfun_constE SAidE inSAsetI.
  move=> /andP[]/andP[_] au aint.
  move: (uopen (row_mx x a)); rewrite in_setI !mem_setE au.
  rewrite inSAsetX row_mxKl row_mxKr xs => /(_ aint)[] e [] e0 /subsetP eu.
  exists e; split=> //.
  apply/subsetP => b; rewrite in_setI !mem_setE => /andP[] + bt.
  rewrite -ball_normE inE/= [`|_|]mx_normrE => /bigmax_ltP[_]/= be.
  rewrite inSApreimset SAjoinE SAfun_constE SAidE inSAsetI inSAsetX.
  rewrite row_mxKl row_mxKr xs bt.
  move: (eu (row_mx x b)); rewrite mem_setE; apply.
  rewrite -ball_normE inE/=; split; last first.
    by rewrite inSAsetX row_mxKl row_mxKr xs.
  rewrite [`|_|]mx_normrE; apply/bigmax_lt => //=; case=> i j _ /=.
  rewrite -(@splitK n.+1 m.+1 j) !mxE unsplitK.
  case: (@split n.+1 m.+1 j) => /= k.
    by rewrite subrr normr0.
  by move: (be (i, k) isT); rewrite !mxE.
mp.
  apply/open_subspace_ballP => /= a.
  rewrite in_setI !mem_setE inSApreimset SAjoinE SAfun_constE SAidE inSAsetI.
  move=> /andP[]/andP[_] av aint.
  move: (vopen (row_mx x a)); rewrite in_setI !mem_setE av.
  rewrite inSAsetX row_mxKl row_mxKr xs => /(_ aint)[] e [] e0 /subsetP ev.
  exists e; split=> //.
  apply/subsetP => b; rewrite in_setI !mem_setE => /andP[] + bt.
  rewrite -ball_normE inE/= [`|_|]mx_normrE => /bigmax_ltP[_]/= be.
  rewrite inSApreimset SAjoinE SAfun_constE SAidE inSAsetI inSAsetX.
  rewrite row_mxKl row_mxKr xs bt.
  move: (ev (row_mx x b)); rewrite mem_setE; apply.
  rewrite -ball_normE inE/=; split; last first.
    by rewrite inSAsetX row_mxKl row_mxKr xs.
  rewrite [`|_|]mx_normrE; apply/bigmax_lt => //=; case=> i j _ /=.
  rewrite -(@splitK n.+1 m.+1 j) !mxE unsplitK.
  case: (@split n.+1 m.+1 j) => /= k.
    by rewrite subrr normr0.
  by move: (be (i, k) isT); rewrite !mxE.
mp.
  apply/negP => /SAsetP/(_ y); rewrite inSAsetI yt inSApreimset.
  rewrite SAjoinE SAfun_constE SAidE inSAsetI inSAsetX row_mxKl row_mxKr.
  by rewrite xs yt yu inSAset0.
mp.
  apply/negP => /SAsetP/(_ z); rewrite inSAsetI zt inSApreimset.
  rewrite SAjoinE SAfun_constE SAidE inSAsetI inSAsetX row_mxKl row_mxKr.
  by rewrite xs zt zv inSAset0.
mp.
  apply/SAset_subP => a aint.
  have /stuv: row_mx x a \in s :*: t by rewrite inSAsetX row_mxKl row_mxKr xs.
  by rewrite !inSAsetU => /orP[au|av]; apply/orP; [left|right];
      rewrite inSApreimset SAjoinE SAfun_constE SAidE inSAsetI inSAsetX
        row_mxKl row_mxKr xs aint.
move=> {y yt yu z zt zv}.
set tfib := (_ :&: _); case: (set0Vmem tfib) => [->|]; first by rewrite eqxx.
rewrite /tfib => {tfib} -[] y; rewrite !inSAsetI => /andP[]/andP[] yt.
rewrite !inSApreimset SAjoinE SAfun_constE SAidE !inSAsetI.
move=> /andP[_] xyu /andP[xyst] xyv _.
apply/negP => /SAsetP/(_ (row_mx x y)).
by rewrite !inSAsetI xyst xyu xyv inSAset0.
Qed.

(* N.B. This breaks the previous proofs. *)
From mathcomp Require Import functions finmap.

Lemma SAconnected_partition_of_graphs_above (R : rcfType) n (s : {SAset R^n}) (xi : seq (SAfunltType R n)) :
  SAconnected s ->
  path.sorted <%O xi ->
  (forall i, i < size xi -> {within [set` s], continuous (xi`_i)}) ->
  forall t, t \in partition_of_graphs_above s xi -> SAconnected t.
Proof.
move=> /= scon.
rewrite lt_sorted_pairwise => /(pairwiseP 0)/= xisort.
move=> xicont t /imfsetP[/=] u + ->.
move=> /(nthP (SAset0 _ _))[] i; rewrite size_map size_iota => ilt <-.
have mx0_continuous (T U : topologicalType) (S : set 'rV[U]_0) (x : U) (f : T -> subspace S) :
  continuous f.
  apply/(@eq_continuous _ (subspace S) (fun=> \row__ x)); last exact/cst_continuous.
  by move=> y; apply/rowP; case.
(* WHAT?????? *)
have lsubmx_continuous (I : interval R) (x : subspace [set` s :*: SAset_itv I]) : {for x, continuous [eta lsubmx : subspace [set` s :*: SAset_itv I] -> subspace [set` s]]}.
  case: n {xi scon xisort xicont t u i ilt} s x => [|n] s x.
    by apply/mx0_continuous; exact: 0.
  move: x; apply/continuousP => a /open_subspace_ballP/= aopen.
  apply/open_subspace_ballP => /= x.
  rewrite in_setI mem_preimage mem_setE inSAsetX => /andP[] xa /andP[] xs _.
  move: aopen => /(_ (lsubmx x)); rewrite in_setI xa mem_setE => /(_ xs)[] e.
  rewrite -ball_normE => -[] e0 /subsetP ea.
  exists e; split=> //; rewrite -ball_normE; apply/subsetP => y.
  rewrite in_setI mem_setE/= [X in X && _]inE mem_setE inSAsetX.
  rewrite [(`|_|)%R]mx_normrE => /andP[] /bigmax_ltP[_]/= xye /andP[] ys _.
  apply/ea; rewrite in_setI mem_setE/= [X in X && _]inE mem_setE ys andbT.
  rewrite [(`|_|)%R]mx_normrE; apply/bigmax_lt => //= -[] u v _ /=.
  move: xye => /(_ (u, lshift 1 v) isT) /=.
  by rewrite !mxE/=.
pose g (f : {SAfun R^n -> R^1}) : {SAfun R^(n + 1) -> R^(n + 1)} :=
  SAjoin (SAselect R (n + 1) n (iota 0 n)) (SAfun_add (SAselect R (n + 1) 1 [:: n]) (SAcomp f (SAselect _ _ _ (iota 0 n)))).
have gE f x : g f x = row_mx (lsubmx x) (rsubmx x + f (lsubmx x)).
  by rewrite /g SAjoinE SAfun_addE SAcompE/= SAselect_iotal SAselect_iotar.
have gcont (f : {SAfun R^n -> R^1}) (I : interval R) : {within [set` s], continuous f} -> {within [set` s :*: SAset_itv I], continuous (g f)}.
  case: n s {xi scon xisort xicont t u i ilt} f g gE lsubmx_continuous => [|n] s f g gE lsubmx_continuous.
    move=> _; apply/(subspace_eq_continuous (f:=fun x : 'cV[R]_1 => x + f 0)).
      move=> x _; rewrite gE row_thin_mx; congr (_ + f _); last first.
        by apply/rowP; case.
      apply/eqP; rewrite rowPE forall_ord1 !mxE/=; apply/eqP.
      by congr (x _ _); apply/val_inj.
    apply/subspace_continuousP => /= x _.
    apply/(@cvg_within_filter 'rV[R]_1 'rV[R]_1 _ (nbhs x) _ (nbhs (x + f 0)) [set` s :*: SAset_itv I]).
    apply/(@continuousD _ _ _ id (fun=> f 0) x); first exact/id_continuous.
    exact/cst_continuous.
  move=> fcont; apply/mx_continuous => i j.
  case: (ltnP j n.+1) => jn.
    apply/(subspace_eq_continuous (f:=fun x : 'rV[R]_(n.+1 + 1) => x i j)); last first.
      apply/subspace_continuousP => /= x _.
      apply/(@cvg_within_filter _ _ _ (nbhs x) _ (nbhs (x i j)) [set` s :*: SAset_itv I]).
      exact/coord_continuous.
    move=> x _; rewrite gE mxE/=.
    have ->: j = lshift 1 (Ordinal jn) by apply/val_inj.
    by rewrite (unsplitK (inl _)) mxE.
  apply/(subspace_eq_continuous (f:=fun x : 'rV[R]_(n.+1 + 1) => x i j + f (lsubmx x) i ord0)).
    move=> x _; rewrite gE !mxE/=.
    suff ->: j = rshift n.+1 (@ord0 0).
      by rewrite (unsplitK (inr _)) !mxE.
    apply/val_inj; rewrite /= addn0; apply/le_anti/andP; split=> //.
    by rewrite -[leRHS]addn1; move: (ltn_ord j); rewrite ltnS.
  move=> x.
  apply/(@continuousD _ R^o (subspace [set` s :*: SAset_itv I]) (fun x : 'rV[R]_(n.+1 + 1) => x i j) (fun x : 'rV[R]_(n.+1 + 1) => f (lsubmx x) i ord0)).
    move: x; apply/subspace_continuousP => /= x _.
    apply/(@cvg_within_filter _ _ _ (nbhs x) _ (nbhs (x i j)) [set` s :*: SAset_itv I]).
    exact/coord_continuous.
  apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) _ _ (fun x : 'rV[R]_(n.+1 + 1) => f (lsubmx x)) (fun x : 'rV[R]_1 => x i ord0)); last first.
    exact/coord_continuous.
  apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) (subspace [set` s]) _ (fun x : 'rV[R]_(n.+1 + 1) => lsubmx x) f); last first.
    exact/fcont.
  exact/lsubmx_continuous.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota; last by [].
case: (posnP (size xi)) => xi0.
  move: ilt; rewrite xi0 ltnS leqn0 => ->.
  move/eqP: xi0; rewrite size_eq0 => /eqP ->; rewrite big_nil SAsetTI.
  apply/SAconnectedX; first by [].
  suff ->: SAsetT R 1 = SAset_itv `]-oo, +oo[ by apply/SAset_itv_connected.
  by apply/eqP/SAsetP => x; rewrite inSAsetT inSAset_itv in_itv.
have xisort': {in gtn (size xi) &,
    {homo nth 0 xi : i j / (i <= j)%N >-> ((i : SAfunleType _ _) <= j)%R}}.
  move=> x y xlt ylt.
  rewrite leq_eqVlt => /orP[/eqP ->|]; first exact/lexx.
  move=> /xisort-/(_ xlt ylt)/SAfun_ltP xy.
  by apply/SAfun_leP => z; apply/ltW.
case: (posnP i) => [_|i0].
  set S := _ :&: _.
  suff ->: S = SAimset (g (xi`_0)) (s :*: SAset_itv `]-oo, 0[). 
    apply/SAimset_connected; last exact/gcont/xicont.
    apply/SAconnectedX; first by [].
    exact/SAset_itv_connected.
  apply/eqP/SAsetP => x.
  rewrite /S inSAsetI inSAset_bigcap inSAsetX inSAsetT andbT.
  apply/andP/SAimsetP.
    move=> [] /allP xxi xs.
    exists (row_mx (lsubmx x) (rsubmx x - xi`_0 (lsubmx x))); last first.
      by rewrite gE row_mxKl row_mxKr addrAC -addrA subrr addr0 hsubmxK.
    rewrite inSAsetX row_mxKl row_mxKr xs inSAset_itv in_itv/= !mxE/=.
    rewrite subr_lt0.
    by move: xxi => /(_ _ (mem_nth 0 xi0)); rewrite inSAhypograph mxE.
  move=> [] y; rewrite inSAsetX inSAset_itv in_itv/= => /andP[] ys y0 ->.
  rewrite gE row_mxKl; split=> //.
  apply/allP => _ /(nthP 0)[] j jxi <-.
  rewrite inSAhypograph row_mxKl row_mxKr -[ltRHS]add0r mxE; apply/ltr_leD => //.
  by move: xisort' => /(_ 0 j); rewrite !inE => /(_ xi0 jxi (leq0n _)) /SAfun_leP.
move: ilt; rewrite ltnS leq_eqVlt => /orP[->|ilt].
  set S := _ :&: _.
  suff ->: S = SAimset (g (xi`_(size xi).-1)) (s :*: SAset_itv `]0, +oo[). 
    apply/SAimset_connected; last first.
      by apply/gcont/xicont; rewrite [_ < _]ltn_predL.
    apply/SAconnectedX; first by [].
    exact/SAset_itv_connected.
  apply/eqP/SAsetP => x.
  rewrite /S inSAsetI inSAset_bigcap inSAsetX inSAsetT andbT.
  apply/andP/SAimsetP.
    move=> [] /allP xxi xs.
    exists (row_mx (lsubmx x) (rsubmx x - xi`_(size xi).-1 (lsubmx x))); last first.
      by rewrite gE row_mxKl row_mxKr addrAC -addrA subrr addr0 hsubmxK.
    rewrite inSAsetX row_mxKl row_mxKr xs inSAset_itv in_itv/= !mxE/= andbT.
    rewrite subr_gt0; move: xxi => /(_ (xi`_(size xi).-1)); mp.
      by apply/mem_nth; rewrite ltn_predL.
    by rewrite inSAepigraph mxE.
  move=> [] y; rewrite inSAsetX inSAset_itv in_itv/= andbT => /andP[] ys y0 ->.
  rewrite gE row_mxKl; split=> //.
  apply/allP => _ /(nthP 0)[] j jxi <-.
  rewrite inSAepigraph row_mxKl row_mxKr -[ltLHS]add0r mxE; apply/ltr_leD => //.
  move: xisort' => /(_ j (size xi).-1); rewrite !inE ltn_predL => /(_ jxi xi0).
  by rewrite -ltnS prednK// => /(_ jxi) => /SAfun_leP.
have ->: i == (size xi).*2 = false.
  apply/negP => /eqP iE.
  by move: ilt; rewrite iE ltnn.
case/boolP: (odd i) => iodd.
  set S := _ :&: _.
  suff ->: S = SAimset (g (xi`_i./2)) (s :*: SAset_itv `[0, 0]). 
    apply/SAimset_connected; last first.
      by apply/gcont/xicont; rewrite [_ < _]ltn_half_double.
    apply/SAconnectedX; first by [].
    exact/SAset_itv_connected.
  apply/eqP/SAsetP => x.
  rewrite /S inSAsetI -{1}[x]hsubmxK -inSAfun inSAsetX inSAsetT andbT.
  apply/andP/SAimsetP.
    move=> [] /eqP xE xs.
    exists (row_mx (lsubmx x) (rsubmx x - xi`_i./2 (lsubmx x))); last first.
      by rewrite gE row_mxKl row_mxKr addrAC -addrA subrr addr0 hsubmxK.
    rewrite inSAsetX row_mxKl row_mxKr xs inSAset_itv in_itv/= !mxE/=.
    by rewrite xE mxE subrr lexx.
  move=> [] y; rewrite inSAsetX inSAset_itv in_itv/= => /andP[] ys.
  move=> /andP[] y0 y0' ->.
  have {y0'}y0: rsubmx y ord0 ord0 = 0 by apply/le_anti/andP.
  rewrite gE row_mxKl row_mxKr; split=> //; apply/eqP.
  rewrite -[LHS]add0r; congr (_ + _); apply/eqP.
  by rewrite rowPE forall_ord1 y0 mxE eqxx.
(* Why does `move=> {...}` unfold the goal ??? *)
clear g gE gcont.
pose h (f g : {SAfun R^n -> R^1}) : {SAfun R^(n + 1) -> R^(n + 1)} :=
  SAjoin (SAselect R (n + 1) n (iota 0 n))
    (SAfun_add (SAcomp f (SAselect _ _ _ (iota 0 n)))
      (SAfun_mul (SAselect R (n + 1) 1 [:: n]) (SAcomp (SAfun_sub g f) (SAselect _ _ _ (iota 0 n))))).
have hE f g x : h f g x = row_mx (lsubmx x) (f (lsubmx x) + x ord0 (rshift n ord0) *: (g (lsubmx x) - (f (lsubmx x)))).
  rewrite /h SAjoinE SAfun_addE SAfun_mulE !SAcompE/= SAfun_subE.
  rewrite SAselect_iotal SAselect_iotar.
  congr (row_mx _ (_ + _)).
  apply/rowP => j; rewrite !mxE/=; congr (x _ _ * _); apply/val_inj.
  by case: j; case.
have hcont (f g : {SAfun R^n -> R^1}) (I : interval R) : {within [set` s], continuous f}
    -> {within [set` s], continuous g}
    -> {within [set` s :*: SAset_itv I], continuous (h f g)}.
  case: n s {xi scon xi0 xisort xisort' xicont t u i ilt i0 iodd} f g h hE lsubmx_continuous => [|n] s f g h hE lsubmx_continuous.
    move=> _ _; apply/(subspace_eq_continuous (f:=fun x : 'cV[R]_1 => f 0 + x * (g 0 - f 0))).
      move=> x _; rewrite hE row_thin_mx.
      have ->: lsubmx (x : 'rV_(0 + 1)) = 0 by apply/rowP; case.
      congr (_ + _); apply/rowP; case; case=> [|//] j.
      rewrite !mxE/= big_ord_recl big_ord0 addr0 !mxE; congr (x _ _ * _).
      exact/val_inj.
    apply/subspace_continuousP => /= x _.
    apply/(@cvg_within_filter 'rV[R]_1 'rV[R]_1 _ (nbhs x) _ (nbhs (f 0 + x * (g 0 - f 0))) [set` s :*: SAset_itv I]).
    apply/(@continuousD _ _ _ (fun=> f 0) (fun x : 'cV[R]_1 => x * (g 0 - f 0)) x).
      exact/cst_continuous.
    apply/mx_continuous => i j; rewrite !ord1.
    apply/(eq_continuous (f:=fun x : 'cV[R]_1 => x ord0 ord0 * (g 0 - f 0) ord0 ord0)).
      by move=> y; rewrite [in RHS]mxE big_ord_recl big_ord0 addr0.
    move=> {}x.
    apply/(@continuousM R 'cV[R]_1 (fun x : 'cV[R]_1 => x ord0 ord0) (fun=> (g 0 - f 0) ord0 ord0)).
      exact/coord_continuous.
    exact/cst_continuous.
  move=> fcont gcont; apply/mx_continuous => i j.
  case: (ltnP j n.+1) => jn.
    apply/(subspace_eq_continuous (f:=fun x : 'rV[R]_(n.+1 + 1) => x i j)); last first.
      apply/subspace_continuousP => /= x _.
      apply/(@cvg_within_filter _ _ _ (nbhs x) _ (nbhs (x i j)) [set` s :*: SAset_itv I]).
      exact/coord_continuous.
    move=> x _; rewrite hE mxE/=.
    have ->: j = lshift 1 (Ordinal jn) by apply/val_inj.
    by rewrite (unsplitK (inl _)) mxE.
  apply/(subspace_eq_continuous (f:=fun x : 'rV[R]_(n.+1 + 1) => f (lsubmx x) i ord0 + x i j * (g (lsubmx x) - f (lsubmx x)) i ord0)).
    move=> x _; rewrite hE !mxE/=.
    suff ->: j = rshift n.+1 (@ord0 0).
      by rewrite (unsplitK (inr _)) !mxE ord1.
    apply/val_inj; rewrite /= addn0; apply/le_anti/andP; split=> //.
    by rewrite -[leRHS]addn1; move: (ltn_ord j); rewrite ltnS.
  move=> x.
  apply/(@continuousD _ (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod R) (subspace [set` s :*: SAset_itv I])).
    apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) _ _ _ (fun x : 'rV[R]_1 => x i ord0)); last first.
      exact/coord_continuous.
    apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) (subspace [set` s])).
      exact/lsubmx_continuous.
    exact/fcont.
  apply/(@continuousM R (subspace [set` s :*: SAset_itv I])).
    move: x; apply/subspace_continuousP => /= x _.
    apply/(@cvg_within_filter _ _ _ (nbhs x) _ (nbhs (x i j)) [set` s :*: SAset_itv I]).
    exact/coord_continuous.
  apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) _ _ _ (fun x : 'rV[R]_1 => x i ord0)); last first.
    exact/coord_continuous.
  apply/(@continuousB _ 'rV[R]_1 (subspace [set` s :*: SAset_itv I])).
    apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) (subspace [set` s])).
      exact/lsubmx_continuous.
    exact/gcont.
  apply/(@continuous_comp (subspace [set` s :*: SAset_itv I]) (subspace [set` s])).
    exact/lsubmx_continuous.
  exact/fcont.
have i20: (0 < i./2)%N.
  by rewrite half_gt0; case: i i0 iodd {ilt} => [//|]; case.
have ilt': (i./2.-1 < size xi)%N.
  by rewrite prednK// leq_half_double; apply/ltnW/(ltn_trans ilt)/leqnn.
move: (xisort i./2.-1 i./2); rewrite !inE => /(_ ilt').
rewrite ltn_half_double => /(_ ilt).
rewrite prednK// => /(_ (leqnn _)) /SAfun_ltP {}xisort.
set S := _ :&: _.
suff ->: S = SAimset (h xi`_i./2.-1 xi`_i./2) (s :*: SAset_itv `]0, 1[). 
  apply/SAimset_connected; last first.
    apply/hcont; apply/xicont => //.
    by rewrite [_ < _]ltn_half_double.
  apply/SAconnectedX; first by [].
  exact/SAset_itv_connected.
apply/eqP/SAsetP => x.
rewrite /S !inSAsetI inSAepigraph inSAhypograph inSAsetX inSAsetT andbT mxE.
apply/andP/SAimsetP.
  move=> [] /andP[] xix xxi xs.
  exists (row_mx (lsubmx x) (\row__ ((rsubmx x ord0 ord0 - xi`_i./2.-1 (lsubmx x) ord0 ord0) / (xi`_i./2 (lsubmx x) ord0 ord0 - xi`_i./2.-1 (lsubmx x) ord0 ord0)))); last first.
    rewrite -[LHS]hsubmxK hE row_mxKl; congr (row_mx _ _).
    apply/rowP => j; rewrite !ord1 !mxE (unsplitK (inr _)) !mxE.
    rewrite mulrAC -mulrA divff.
      by rewrite mulr1 addrCA subrr addr0.
    rewrite subr_eq0; apply/eqP => xiE.
    by move: (xisort (lsubmx x)); rewrite xiE ltxx.
  rewrite inSAsetX row_mxKl row_mxKr xs inSAset_itv in_itv/= !mxE/=.
  apply/andP; split; first by apply/divr_gt0; rewrite subr_gt0.
  by rewrite ltr_pdivrMr ?subr_gt0// mul1r -subr_gt0 subrBB subr_gt0. 
move=> [] y; rewrite inSAsetX inSAset_itv in_itv/= => /andP[] ys.
rewrite mxE => /andP[] y0 y1 ->.
rewrite hE row_mxKl; split=> //.
rewrite mxE (unsplitK (inr _)) !mxE; apply/andP; split.
  rewrite -subr_gt0 addrAC subrr add0r; apply/mulr_gt0 => //.
  by rewrite subr_gt0.
rewrite -subr_gt0 opprD addrA -[X in (X - _)%R]mul1r -mulrBl.
by apply/mulr_gt0; rewrite subr_gt0.
Qed.
  

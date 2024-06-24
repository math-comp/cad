From mathcomp Require Import freeg ssreflect ssrfun ssrbool eqtype choice seq ssrnat prime binomial bigop tuple order fintype finfun path ssralg ssrnum ssrint poly matrix finmap mpoly complex.
From mathcomp Require Import polydiv polyrcf polyorder qe_rcf qe_rcf_th.

(* TODO: the following imports should not be needed after cleanup. *)
From mathcomp Require Import generic_quotient classical_sets topology normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.
Import GRing.Theory Num.Theory Num.Def.
Import GRing.
Import numFieldTopology.Exports.

Require Import auxresults formula subresultant semialgebraic topology continuity_roots.

Local Open Scope type_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope ring_scope.
Local Open Scope sa_scope.

Section CylindricalDecomposition.
Variables (R : rcfType).

(* How do I assert that the restriction of a function is continuous, and not that the function is continuous at every point in the set? *)
Fixpoint isCylindricalDecomposition n (S : {fset {SAset R^n}}) :=
  SAset_partition S
  /\ match n with | 0 => Logic.True | n.+1 =>
    let S' := [fset SAset_cast n s | s in S] in
    isCylindricalDecomposition S'
    /\ forall (s' : S'),
    exists m, exists xi : m.-tuple {SAfun R^n -> R^1},
      (forall i, {within [set` val s'], continuous (tnth xi i)})
      /\ sorted (@SAfun_lt _ _) xi
      /\ [fset s in S | SAset_cast n s == val s'] = [fset SAset_cast _ x | x in partition_of_graphs_above (val s') xi]
  end.
Print isCylindricalDecomposition.

Local Notation isCD := isCylindricalDecomposition.

Lemma isCylindricalDecomposition_restrict n m S (mn : (m <= n)%N) : @isCD n S -> isCD [fset SAset_cast m s | s in S].
Proof.
move: (n - m)%N mn (subnKC mn) S => + _ <-; elim=> [|d IHd].
  rewrite addn0 => S.
  congr isCD; apply/fsetP => s; apply/idP/imfsetP => [sS|[x]/= xS ->].
    by exists s => //; rewrite SAset_cast_id.
  by rewrite SAset_cast_id.
rewrite addnS => S /= [_] [/IHd] + _; congr isCD.
have md: (m <= m + d)%N by rewrite -{1}[m]addn0 leq_add2l.
by apply/fsetP => s; rewrite -imfset_comp; apply/imfsetP/imfsetP => -[x]/= xS ->;
  exists x => //; rewrite SAset_cast_trans// geq_min md orbT.
Qed.

Definition poly_invariant n (p : {mpoly R[n]}) (s : {SAset R^n}) :=
  {in s &, forall x y, (sgz (meval (tnth (ngraph x)) p) = sgz (meval (tnth (ngraph y)) p))%R}.

Definition poly_adapted n p (S : {fset {SAset R^n}}) := forall s : S, poly_invariant p (val s).

Definition evalpmp {n} (x : 'rV[R]_n) (P : {poly {mpoly R[n]}}) := map_poly (meval (tnth (ngraph x))) P.

Definition truncate (T : ringType) (p : {poly T}) (d : nat) :=
  (\poly_(i < minn d (size p)) p`_i)%R.

Definition truncations n (p : {poly {mpoly R[n]}}) : {fset {poly {mpoly R[n]}}} :=
  (fix F p n :=
    match n with
    | 0 => [fset p]
    | n.+1 => if (0 < mdeg (mlead (lead_coef p)))%N then
        p |` F (truncate p (size p).-1) n
      else [fset p]
    end) p (size p).

Lemma coef_truncate (T : ringType) (p : {poly T}) d n :
  (truncate p d)`_n = p`_n *+ (n < d).
Proof.
rewrite -{2}[p]coefK !coef_poly ltn_min.
by case: (n < d)%N; rewrite ?mulr0n// mulr1n.
Qed.

Lemma truncate_trans (T : ringType) (p : {poly T}) (d e : nat) :
  truncate (truncate p d) e = truncate p (minn d e).
Proof. by apply/polyP => i; rewrite !coef_truncate ltn_min -mulnb mulrnA. Qed.

Lemma truncate_size (T : ringType) (p : {poly T}) :
  truncate p (size p) = p.
Proof. by rewrite /truncate minnn coefK. Qed.

Lemma truncate_ge_sizeP (T : ringType) (p : {poly T}) (d : nat) :
  (truncate p d == p) = (size p <= d)%N.
Proof.
apply/eqP/idP => [<-|/minn_idPl pd].
  exact/(leq_trans (size_poly _ _) (geq_minl _ _)).
by rewrite -[p]truncate_size truncate_trans pd.
Qed.

Lemma truncationsE n (p : {poly {mpoly R[n]}}) :
  truncations p =
  [fset truncate p d | d in [seq d <- iota 0 (size p).+1 | all (fun i => msize p`_i != 1) (iota d ((size p).+1 - d))]].
Proof.
have t00 k: truncate 0 k = 0 :> {poly {mpoly R[n]}}.
  by apply/eqP; rewrite truncate_ge_sizeP size_poly0.
rewrite /truncations.
move dE: (size p) => d.
have {dE}: (size p <= d)%N by rewrite dE leqnn.
elim: d p => [|d IHd] p.
  move=> /= /size_poly_leq0P ->.
  apply/fsetP => x; rewrite coef0 msize0/= inE.
  apply/eqP/imfsetP => [->|[y]]; first by exists 0.
  by rewrite inE t00.
move=> sp; rewrite {}IHd; last first.
  apply/(leq_trans (size_poly _ _))/(leq_trans (geq_minl _ _)).
  by rewrite [d]pred_Sn -!subn1 leq_sub2r.
rewrite !iotanS.
have [->|p0] := eqVneq p 0.
  rewrite lead_coef0 mlead0 mdeg0/=; apply/fsetP => x.
  rewrite in_fset1; apply/eqP/imfsetP => /= [->|[k] _]; last by rewrite t00.
  exists 0; last by rewrite t00.
  rewrite mem_filter -iotanS in_cons eqxx andbT.
  by apply/allP => i _; rewrite coef0 msize0.
case: (ltnP 0 _); last first.
  rewrite leqn0 -eqSS mlead_deg ?lead_coef_eq0// lead_coefE => pn.
  apply/fsetP => x; rewrite in_fset1.
  apply/eqP/imfsetP => [->|[k]] /=.
    exists d.+1; last by apply/esym/eqP; rewrite truncate_ge_sizeP.
    rewrite mem_filter mem_rcons add0n in_cons eqxx andbT /= subSnn/= andbT.
    move/leq_sizeP: sp => /(_ d.+1 (leqnn _)) ->.
    by rewrite msize0.
  rewrite mem_filter => /andP[] /allP sk _ ->.
  apply/eqP; rewrite truncate_ge_sizeP leqNgt; apply/negP => kp.
  move/(_ (size p).-1): sk.
  rewrite pn mem_iota -ltnS (ltn_predK kp) kp/= subnKC.
    by rewrite (leq_trans sp)// => /(_ isT).
  by rewrite -ltnS; apply/(leq_trans kp)/(leq_trans sp)/(leq_trans (leqnSn _)).
rewrite -ltnS mlead_deg ?lead_coef_eq0// => pn.
apply/fsetP => x; rewrite in_fset1U.
apply/orP/imfsetP => /= [[/eqP ->|/imfsetP]|].
- exists d.+1; last by apply/esym/eqP; rewrite truncate_ge_sizeP.
  rewrite mem_filter subSnn/= mem_rcons add0n mem_head.
  move/leq_sizeP: sp => /(_ d.+1 (leqnn _)) ->.
  by rewrite msize0.
- move=> /= [k].
  rewrite mem_filter truncate_trans -iotanS mem_iota iotanS/= add0n.
  move=> /andP[] /allP ks kd ->.
  exists (minn (size p).-1 k) => //.
  rewrite mem_filter -!iotanS mem_iota/= add0n ltnS geq_min (ltnW kd) orbT andbT.
  apply/allP => i; rewrite mem_iota subnKC geq_min; last first.
    by rewrite (leq_trans (ltnW kd))// orbT.
  case: (ltnP i (size p).-1) => /= [ip /andP[] ki id|+ _]; last first.
    rewrite leq_eqVlt => /orP[/eqP <-|].
      by rewrite -lead_coefE eq_sym (ltn_eqF pn).
    rewrite prednK; last by rewrite ltnNge leqn0 size_poly_eq0.
    move=> /leq_sizeP => /(_ i (leqnn _)) ->.
    by rewrite msize0.
  move/(_ i): ks; rewrite mem_iota ki/= subnKC ?(ltnW kd)//.
  move: id; rewrite leq_eqVlt ltnS eqSS => /orP [/eqP -> _|/[swap]/[apply]].
    by move/leq_sizeP: sp => /(_ _ (leqnn _)) ->; rewrite msize0.
  by rewrite coef_truncate ip mulr1n.
move=> [k]; rewrite mem_filter -!iotanS mem_iota iotanS/= add0n ltnS.
move=> /andP[] /allP sk kd ->.
case: (ltnP k (size p)) => [kp|pk]; last by left; rewrite truncate_ge_sizeP.
right; apply/imfsetP; exists k => /=; last first.
  rewrite truncate_trans; congr truncate.
  by apply/esym/minn_idPr; rewrite -ltnS (leq_trans kp)// leqSpred.
rewrite mem_filter -iotanS mem_iota/= add0n (leq_trans kp sp) andbT.
apply/allP => i; rewrite mem_iota subnKC// => /andP[] ki id.
rewrite coef_truncate; case: (i < _)%N; last by rewrite mulr0n msize0.
rewrite mulr1n; apply/sk; rewrite mem_iota ki/= subnKC.
  exact/(leq_trans id).
exact/(leq_trans kd).
Qed.
  
Lemma truncations_witness n d (p : {poly {mpoly R[n]}}) (x : 'rV[R]_n) :
  (size (evalpmp x p) <= d)%N -> truncate p d \in truncations p.
Proof.
rewrite truncationsE => sd; apply/imfsetP; exists (minn d (size p)); last first.
  case: (ltnP d (size p)) => //; rewrite -truncate_ge_sizeP => /eqP ->.
  by rewrite truncate_size.
rewrite mem_filter mem_iota/= add0n ltnS geq_minr andbT.
apply/allP => i; rewrite mem_iota geq_min.
case: (ltnP i (size p)) => [ip|+ _]; last first.
  by move=> /leq_sizeP -> //; rewrite msize0.
rewrite orbF => /andP[] di _.
move/leq_sizeP: sd => /(_ _ di); rewrite coefE ip => pi0.
apply/negP => /msize_poly1P [c] /eqP c0 pE.
by rewrite pE mevalC in pi0.
Qed.

Ltac mp := 
  match goal with
  | |- (?x -> _) -> _ => have /[swap]/[apply]: x
  end.

Import ordered_qelim.ord.

Theorem roots2_on n (P : {poly {mpoly R[n]}}) (d : nat) (s : {SAset R^n}) :
  {in s, forall x, size (rootsR (evalpmp x P)) = d}
  -> {xi : d.-tuple {SAfun R^n -> R^1} | sorted (@SAfun_lt R n) xi /\ {in s, forall x, [seq (xi : {SAfun R^n -> R^1}) x ord0 ord0 | xi <- xi] = (rootsR (evalpmp x P))}}.
Proof.
case: (set0Vmem s) => [-> {s}|[x xs] dE].
  exists (mktuple (fun i => SAfun_const n (\row__ i%:R))).
  split=> [|x]; last by rewrite inSAset0.
  apply/(sortedP (SAfun_const n 0)); rewrite size_tuple => i id.
  rewrite -[i.+1]/(Ordinal id : nat) nth_mktuple.
  rewrite -/(Ordinal (ltnW id) : nat) nth_mktuple/=.
  by apply/SAfun_ltP => x; rewrite !SAfun_constE !mxE ltr_nat.
move: dE; have [->|+ dE] := eqVneq d 0.
  move=> dE; exists (mktuple (fun i => SAfun_const n 0)).
  split=> [|y ys]; first by rewrite /= enum_ord0.
  move/eqP: (dE _ ys); rewrite size_eq0 => /eqP -> /=.
  by rewrite enum_ord0.
move: (dE _ xs); have [-> <-|] := eqVneq (evalpmp x P) 0.
  by rewrite /rootsR roots0.
have [->|P0 Px0 _ d0] := eqVneq P 0.
  by rewrite /evalpmp rmorph0 eqxx.
(* TODO: should this be extracted? *)
have ltn_addL (k m : nat) : (k + m < k)%N = false.
  by rewrite -{2}[k]addn0 ltn_add2l.
pose G_graph (i : 'I_d) : {SAset R^(n+1)} := [set |
    (Not s /\ 'X_n == NatConst _ i)
    \/ (s /\
      nquantify n.+1 d Exists (
      (\big[And/True]_(j < d.-1) ('X_(n.+1+j) <% 'X_(n.+1+j.+1)))
        /\ \big[And/True]_(j < d) (term_mpoly (mmulti P) (fun k => if (k : nat) == n then 'X_(n.+1+j) else 'X_k) == 0)
        /\ ('forall 'X_(n.+1+d), (term_mpoly (mmulti P) (fun k => if (k : nat) == n then 'X_(n.+1+d) else 'X_k) == 0) ==> \big[Or/False]_(j < d) ('X_(n.+1+d) == 'X_(n.+1+j)))
        /\ 'X_n == 'X_(n.+1+i)))].
have GP i (x0 : 'rV[R]_n) (y : 'rV[R]_1) :
  row_mx x0 y \in G_graph i = if x0 \in s then y ord0 ord0 == (rootsR (evalpmp x0 P))`_i
    else y == \row__ i%:R.
  rewrite pi_form /cut rcf_sat_subst.
  rewrite -[X in subst_env _ X]cats0 subst_env_iota_catl ?size_ngraph//.
  rewrite !simp_rcf_sat -rcf_sat_take ngraph_cat take_size_cat ?size_ngraph//.
  move/(_ x0) : dE; rewrite inE; case/boolP: (rcf_sat (ngraph x0) s) => /= x0s dE; last first.
    rewrite nth_cat size_map size_enum_ord ltnn subnn enum_ordSl/= orbF.
    apply/eqP/eqP => [y0|/rowP ->]; last by rewrite !mxE.
    apply/rowP; case; case=> [|//] j0.
    by rewrite !mxE -[RHS]y0; congr (y _ _); apply/val_inj.
  move: dE => /(_ isT) /eqP dE.
  rewrite -ngraph_cat -[X in nquantify X]addn1 -[X in nquantify X](size_ngraph (row_mx x0 y)).
  apply/rcf_satP/eqP => [/nexistsP [z]/= []/holdsAnd zlt []/holdsAnd z0 []z0P|yE].
    rewrite nth_cat size_map size_enum_ord {1}addn1 leqnn enum_ordD map_cat.
    rewrite nth_cat 2!size_map size_enum_ord ltnn subnn enum_ordSl/=.
    rewrite enum_ord0/= nth_cat size_cat 2!size_map size_enum_ord/=.
    rewrite [X in (_ < X)%N]addn1 -addnS -[X in (_ <= X)%N]addn0 leq_add2l/=.
    rewrite mxE (unsplitK (inr ord0)) => ->.
    rewrite addn1 subDnCA// subnn addn0 (rootsRPE (p:=evalpmp x0 P))//.
    - move=> j; move/(_ j (mem_index_enum _) isT) : z0 => /= Pz.
      apply/rootP; rewrite -[RHS]Pz.
      rewrite -(mevalC (tnth (ngraph x0)) (tnth z j)) horner_map/=.
      rewrite eval_term_mpoly meval_mmulti eqxx/= nth_cat size_map.
      rewrite size_enum_ord [X in (_ < X)%N]addn1 ltn_addL.
      rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0 -tnth_nth/=.
      apply/meval_eq => k.
      rewrite (ltn_eqF (ltn_ord k))/= nth_cat size_map size_enum_ord.
      rewrite -[nat_of_ord k]/(nat_of_ord (@unsplit n 1 (inl k))).
      rewrite ltn_ord (nth_map (unsplit (inl k))) ?size_enum_ord//.
      by rewrite nth_ord_enum mxE unsplitK tnth_mktuple.
    - move=> u /rootP; rewrite -(mevalC (tnth (ngraph x0)) u) horner_map/=.
      move/(_ u): z0P => + Pu.
      rewrite eval_term_mpoly meval_mmulti eqxx/= nth_set_nth/= eqxx; mp.
        rewrite -[RHS]Pu; apply/meval_eq => j.
        rewrite (ltn_eqF (ltn_ord j))/= nth_set_nth/=.
        have /ltn_eqF ->: (j < n.+1 + d)%N.
          apply/(leq_trans (ltn_ord j)).
          by rewrite addSn -addnS -{1}[n]addn0 leq_add2l.
        rewrite nth_cat size_map size_enum_ord.
        rewrite -[nat_of_ord j]/(nat_of_ord (@unsplit n 1 (inl j))) ltn_ord.
        rewrite (nth_map (unsplit (inl j))) ?size_enum_ord//.
        by rewrite nth_ord_enum mxE unsplitK tnth_mktuple.
      move=> /holdsOr -[] /= j [_] [_].
      rewrite !nth_set_nth/= eqxx eqn_add2l (ltn_eqF (ltn_ord j)).
      rewrite nth_cat size_map size_enum_ord {1}addn1 ltn_addL addn1.
      by rewrite subDnCA// subnn addn0 mevalC => ->; apply/memt_nth.
    - apply/(sortedP 0) => j; rewrite size_tuple -ltn_predRL => jd.
        move/(_ (Ordinal jd) (mem_index_enum _) isT): zlt => /=.
        rewrite !nth_cat size_map size_enum_ord -[n.+1]addn1.
        by rewrite !ltn_addL !addn1 !subDnCA// subnn !addn0.
    apply/nexistsP; exists (Tuple dE) => /=; split.
    apply/holdsAnd; case=> j + _ _ /=; rewrite ltn_predRL => jd.
    rewrite !nth_cat size_map size_enum_ord -[n.+1]addn1 !ltn_addL !addn1.
    rewrite !subDnCA// subnn !addn0.
    move/(sortedP 0): (let c := cauchy_bound (evalpmp x0 P) in
      sorted_roots (- c) c (evalpmp x0 P)) => /(_ j).
    by rewrite (eqP dE) => /(_ jd).
  split.
    apply/holdsAnd => j _ _ /=.
    rewrite eval_term_mpoly meval_mmulti eqxx/= nth_cat size_map.
    rewrite size_enum_ord [X in (_ < X)%N]addn1 ltn_addL.
    rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
    have: (rootsR (evalpmp x0 P))`_j \in rootsR (evalpmp x0 P).
      by apply/mem_nth; rewrite (eqP dE).
    move=> /root_roots/rootP.
    rewrite -(mevalC (tnth (ngraph x0)) ((rootsR (evalpmp x0 P))`_j)) horner_map/= => Pj.
    rewrite -[RHS]Pj/= mevalC; apply/meval_eq => k.
    rewrite (ltn_eqF (ltn_ord k))/= nth_cat size_map size_enum_ord.
    rewrite -[nat_of_ord k]/(nat_of_ord (@unsplit n 1 (inl k))) ltn_ord.
    rewrite (nth_map (unsplit (inl k))) ?size_enum_ord// nth_ord_enum.
    by rewrite mxE unsplitK tnth_mktuple.
  split=> [u|].
    move: dE; have [->|{}Px0 dE] := eqVneq (evalpmp x0 P) 0.
      by rewrite /rootsR roots0 => /eqP dx; rewrite -dx eqxx in d0.
    rewrite eval_term_mpoly meval_mmulti eqxx/= nth_set_nth/= eqxx => Pu.
    have: (u \in rootsR (evalpmp x0 P)).
      rewrite in_rootsR Px0; apply/rootP.
      rewrite -(mevalC (tnth (ngraph x0)) u) horner_map/=.
      move: Pu; congr (_ = _); apply/meval_eq => j.
      rewrite (ltn_eqF (ltn_ord j))/= nth_set_nth/=.
      have /ltn_eqF ->: (j < n.+1 + d)%N.
        apply/(leq_trans (ltn_ord j)).
        by rewrite addSn -addnS -{1}[n]addn0 leq_add2l.
      rewrite nth_cat size_map size_enum_ord.
      rewrite -[nat_of_ord j]/(nat_of_ord (@unsplit n 1 (inl j))) ltn_ord.
      rewrite (nth_map (unsplit (inl j))) ?size_enum_ord//.
      by rewrite nth_ord_enum mxE unsplitK tnth_mktuple.
    rewrite -index_mem (eqP dE) => u0.
    apply/holdsOr; exists (Ordinal u0).
    split; first exact/mem_index_enum.
    split=> //=.
    rewrite !nth_set_nth/= eqxx eqn_add2l (ltn_eqF u0).
    rewrite nth_cat size_map size_enum_ord {1}addn1 ltn_addL addn1.
    rewrite subDnCA// subnn addn0; apply/esym/nth_index.
    by rewrite -index_mem (eqP dE).
  rewrite !nth_cat size_map size_enum_ord -[n.+1]addn1 leqnn ltn_addL.
  rewrite -[X in _`_X]addn0 -[X in _`_X]/(nat_of_ord (@unsplit n 1 (inr ord0))).
  rewrite (nth_map (unsplit (inr ord0))) ?size_enum_ord// nth_enum_ord.
  by rewrite mxE unsplitK subDnCA// subnn addn0.
have SAfun_G (i : 'I_d) : (G_graph i \in @SAfunc _ n 1) && (G_graph i \in @SAtot _ n 1).
  apply/andP; split.
    apply/inSAfunc => x0 y1 y2; rewrite !GP.
    case: (x0 \in s); last by move=> /eqP -> /eqP.
    move=> /eqP <- /eqP/esym y12; apply/rowP; case; case=> // lt01.
    by move: y12; congr (y1 _ _ = y2 _ _); apply/val_inj.
  apply/inSAtot => x0; case/boolP: (x0 \in s) => [|/negPf] x0s.
    by exists (\row__ (rootsR (evalpmp x0 P))`_i); rewrite GP x0s !mxE.
  by exists (\row__ i%:R); rewrite GP x0s.
pose G i := MkSAfun (SAfun_G i).
have GE (i : 'I_d) (x0 : 'rV_n) :
  G i x0 = \row__ (if x0 \in s then (rootsR (evalpmp x0 P))`_i else i%:R).
  by apply/eqP; rewrite inSAfun GP; case: (x0 \in s) => //; rewrite mxE.
exists (mktuple G).
split.
  apply/(sortedP (@SAfun_const R n 1 0)) => i; rewrite size_tuple => id.
  apply/SAfun_ltP => y; rewrite (nth_mktuple _ _ (Ordinal id)).
  rewrite (nth_mktuple _ _ (Ordinal (ltnW id))) !GE !mxE.
  case/boolP: (y \in s) => /= ys; last by rewrite ltr_nat.
  move/(sortedP 0): (let c := cauchy_bound (evalpmp y P) in
    sorted_roots (- c) c (evalpmp y P)) => /(_ i).
  by rewrite dE// => /(_ id).
move=> y ys; apply/(eq_from_nth (x0:=0)); first by rewrite size_tuple dE.
rewrite size_tuple => i id.
rewrite (nth_map (@SAfun_const R n 1 0)) ?size_tuple//.
by rewrite -[ i ]/(nat_of_ord (Ordinal id)) nth_mktuple GE mxE ys.
Qed.

Lemma normcR (z : R) : `|z%:C%C| = `|z|%:C%C.
Proof. by rewrite normc_def/= expr0n/= addr0 sqrtr_sqr. Qed.

Lemma rootsR_continuous n (p : {poly {mpoly R[n]}}) (s : {SAset R^n}) (x : 'rV[R]_n) i :
  x \in s ->
  {in s, forall y, size (evalpmp y p) = size (evalpmp x p)} ->
  {in s, forall y, size (gcdp (evalpmp y p) (evalpmp y p)^`()) = size (gcdp (evalpmp x p) (evalpmp x p)^`())} ->
  {in s, forall y, size (rootsR (evalpmp y p)) = size (rootsR (evalpmp x p))} ->
  {within [set` s], continuous (fun y => (rootsR (evalpmp y p))`_i)}.
Proof.
  (*
case: (ltnP i (size (rootsR (evalpmp x p)))) => ir; last first.
  move=> _ _ _ r_const.
  apply(@subspace_eq_continuous _ _ R (fun=> 0)); last exact/cst_continuous.
  move=> /= u; rewrite mem_setE => us.
  by apply/esym/nth_default; rewrite (r_const u us).
case: n p s x ir => [|n] p s x ir xs s_const s'_const r_const/=; apply/continuousP => /= A;
  rewrite openE/= => /subsetP Aopen;
  apply/open_subspace_ballP => /= y;
  rewrite in_setI mem_setE => /andP[] {}/Aopen;
  rewrite /interior inE => /nbhs_ballP[] e/= e0 yeA ys.
  exists 1; split=> // z _; apply/yeA.
  suff ->: z = y by apply/ballxx.
  by apply/rowP => -[].
have [p0|px0] := eqVneq (size (evalpmp x p)) 0.
  exists 1; split=> // z [_] zs /=; apply/yeA.
  have {}p0 u : u \in s -> evalpmp u p = 0.
    by move=> us; apply/eqP; rewrite -size_poly_eq0 s_const// p0.
  by rewrite p0// p0//; apply/ballxx.
pose q z := map_poly (real_complex R) (evalpmp z p).
have q0 z : z \in s -> q z != 0.
  by move=> zs; rewrite map_poly_eq0 -size_poly_eq0 s_const.
set e' := \big[Order.min/e]_(u <- dec_roots (q y)) \big[Order.min/e]_(v <- dec_roots (q y) | u != v) (complex.Re `|u - v| / 2).
have e'0: 0 < e'%:C%C.
  rewrite ltcR lt_bigmin e0/=; apply/allP => u _.
  rewrite lt_bigmin e0/=; apply/allP => v _.
  apply/implyP => uv; apply/divr_gt0; last exact/ltr0Sn.
  by rewrite -ltcR (normr_gt0 (u - v)) subr_eq0.
have: exists d : R, 0 < d /\ forall z, z \in s -> `|z - y| < d -> alignp e'%:C%C (q y) (q z).
  case: (aligned_deformed (q y) e'0) => /= [[]] a aI [].
  rewrite ltcE/= => /andP[/eqP ->] a0; rewrite complexr0 => ad.
  have /fin_all_exists /=: forall i : 'I_(size (val p)).+1, exists delta, 0 < delta /\ forall (z : 'rV[R]_n.+1), y \in s -> `|y - z| < delta -> `|(q y)`_i - (q z)`_i| < a%:C%C.
    move=> j.
    move: (@meval_continuous _ _ (val p)`_j y).
    rewrite /= /continuous_at.
    move=> /(@cvgr_dist_lt _ (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod R)).
    move=> /(_ _ a0) /nbhs_ballP[] d'/= d'0 /subsetP xd'.
    exists d'; split=> // z zs yz.
    move: xd' => /(_ z); mp; first by rewrite -ball_normE inE/=.
    rewrite inE/= !coef_map/= -rmorphB/= normc_def/= expr0n/= addr0 sqrtr_sqr ltcR.
    by congr (normr (_ - _) < a); apply/meval_eq => k; rewrite tnth_mktuple.
  move=> [d'] d'P; exists (\big[minr/1]_i d' i).
  split; first by rewrite lt_bigmin ltr01; apply/allP => j _ /=; case: (d'P j).
  move=> z zs; rewrite lt_bigmin => /andP[_] /allP xz; apply/ad.
  split=> [|j]; first by rewrite !size_map_poly s_const// (s_const _ ys).
  move: (ltn_ord j); rewrite [X in (j < X)%N]size_map_poly => jlt.
  have {}jlt := leq_trans (leq_trans jlt (size_poly _ _)) (leqnSn _).
  case: (d'P (Ordinal jlt)) => _ /=; apply=> //.
  by rewrite -opprB normrN; apply/xz/mem_index_enum.
move=> [] d [] d0 dP.
exists d; split=> // z/=.
rewrite -ball_normE/= -opprB normrN => -[] yz zs; apply/yeA.
move: dP => /(_ z zs yz) yze.
rewrite -(@ball_normE R (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod R))/=.
have: exists (fyz : [fset x in dec_roots (q y)] -> [fset x in dec_roots (q z)]),
    forall u, `|val u - val (fyz u)| < e'%:C%C.
  apply/(fin_all_exists (P:=fun u v => `|val u - val v| < e'%:C%C)).
  case=> /= u; rewrite mem_imfset//= mem_dec_roots => /andP[_] pu.
  move: yze => /(_ u pu).
  rewrite -big_filter; case rsy: (seq.filter _ _) => [|v l].  
    by rewrite big_nil leqn0 mu_eq0 ?pu// map_poly_eq0 -size_poly_eq0 s_const.
  move: (mem_head v l); rewrite -rsy mem_filter -normrN opprB => /andP[] uv pv _.
  suff vP: v \in [fset x in dec_roots (q z)]. 
    by exists [` vP].
  by rewrite mem_imfset.
move=> [/=] fyz fyze.
have eP (u v : [fset x | x in dec_roots (q y)]) :
    `|val u - val v| < 2 * e'%:C%C -> u = v.
  move=> uve; apply/eqP/negP => /negP uv; move: uve.
  rewrite -(RRe_real (normr_real _)) mulrC mulr_natr -rmorphMn/= ltcR -mulr_natr.
  rewrite -ltr_pdivrMr; last exact/ltr0Sn.
  rewrite lt_bigmin => /andP[_] /allP-/(_ (val u))/=.
  move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))/= => /[swap]/[apply].
  rewrite lt_bigmin => /andP[_] /allP-/(_ (val v))/=.
  move: (fsvalP v); rewrite (mem_imfset _ _ (@inj_id _))/= => /[swap]/[apply].
  by rewrite (inj_eq val_inj) ltxx => /implyP-/(_ uv).
have R0: [char R[i]] =i pred0 by exact/char_num.
have fyzb: bijective fyz.
  apply/inj_card_bij.
    move=> u v fuv; apply/eP.
    rewrite -(subrBB (val (fyz u))); apply/(le_lt_trans (ler_normB _ _)).
    rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/fyze.
    by rewrite fuv; apply/fyze.
  rewrite -2!cardfE card_imfset//= card_imfset//=.
  do 2 rewrite undup_id ?uniq_dec_roots//.
  rewrite (size_dec_roots (q z) R0) (size_dec_roots (q y) R0).
  rewrite size_divp; last by rewrite gcdp_eq0 negb_and q0.
  rewrite size_divp; last by rewrite gcdp_eq0 negb_and q0.
  rewrite ![(q _)^`()]deriv_map -!gcdp_map !size_map_poly -!/(evalpmp _ _).
  by rewrite s_const// s_const// s'_const// s'_const.
have pyrP j: (j < size (rootsR (evalpmp y p)))%N -> ((rootsR (evalpmp y p))`_j)%:C%C \in [fset x | x in dec_roots (q y)].
  rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots q0//=.
  move=> /(mem_nth 0); rewrite in_rootsR => /andP[_] jr.
  exact/rmorph_root.
rewrite -ltcR.
apply/(le_lt_trans (normc_ge_Re (_%:C%C))) => /=.
rewrite rmorphB/=.
rewrite -(r_const y ys) in ir.
suff ->: ((rootsR (evalpmp z p))`_i)%:C%C = val (fyz [` pyrP i ir]).
  move: (fyze [` pyrP i ir]) => /= pye.
  apply/(lt_le_trans pye).
  by rewrite lecR; apply/bigmin_le_id.
have perm_eqC a: perm_eq [seq u <- dec_roots (q a) | u \is Num.real] [seq x%:C%C | x <- rootsR (evalpmp a p)].
  apply/uniq_perm.
  - exact/filter_uniq/uniq_dec_roots.
  - by rewrite map_inj_uniq ?uniq_roots//; apply/complexI.
  move=> u; rewrite mem_filter mem_dec_roots map_poly_eq0 .
  apply/andP/mapP => [[] uR /andP[] pa0 qu|[] v + ->].
    exists (complex.Re u); last by rewrite (RRe_real uR).
    rewrite in_rootsR pa0.
    by rewrite -(RRe_real uR) fmorph_root in qu.
  rewrite in_rootsR => /andP[] pa0 pv; split.
    by apply/complex_realP; exists v.
  by rewrite pa0/=; apply/rmorph_root.
have ne20: 2 != 0 :> R[i] by rewrite pnatr_eq0.
have fyzr (u : [fset x | x in dec_roots (q y)]) :
    ((val (fyz u)) \is Num.real) -> (val u) \is Num.real.
  move=> fur.
  suff ->: \val u = 'Re (\val u) by apply/Creal_Re.
  apply/(mulfI ne20).
  rewrite -complexRe -addcJ mulr2n mulrDl mul1r; congr (_ + _)%R.
  have uP: ((\val u)^* )%C \in [fset x | x in dec_roots (q y)].
    rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots q0//=.
    rewrite -complex_root_conj/= map_poly_id => [|a].
      move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))/=.
      by rewrite mem_dec_roots => /andP[_].
    move=> /[dup] /(nth_index 0)/=.
    rewrite -index_mem size_map_poly => + alt.
    by rewrite coef_poly alt => <-; rewrite conjc_real.
  rewrite -[((val u)^* )%C]/(val [` uP]).
  rewrite [in LHS](eP u [` uP])//.
  rewrite -(subrBB (val (fyz u))).
  apply/(le_lt_trans (ler_normB _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/fyze.
  rewrite /= -(RRe_real fur) -conjc_real -rmorphB/= norm_conjC (RRe_real fur).
  exact/fyze.
have {}fyzr (u : [fset x | x in dec_roots (q y)]) :
    (val u) \is Num.real = ((val (fyz u)) \is Num.real).
  apply/idP/idP; last exact/fyzr.
  move=> ur; apply/negP => /negP fur.
  pose sr y := [fset x : [fset x in dec_roots (q y)] | val x \is Num.real].
  have srE a: [fset val x | x in sr a] = [fset x | x in dec_roots (q a) & x \is Num.real].
    apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => b;
    rewrite (mem_imfset _ _ (@inj_id _))/=.
      move=> /imfsetP[/=] c /imfsetP[/=] c' cr -> ->.
      apply/andP; split=> //=.
      by move: (fsvalP c'); rewrite (mem_imfset _ _ (@inj_id _))/=.
    move=> /andP[] qb br; apply/imfsetP => /=.
    have bP: b \in [fset x0 | x0 in dec_roots (q a)].
      by rewrite mem_imfset.
    exists [` bP] => //.
    by rewrite (mem_imfset _ _ (@inj_id _))/=.
  suff: (#|` [fset x | x in dec_roots (q z) & x \is Num.real]| < #|` [fset x | x in dec_roots (q y) & x \is Num.real]|)%N.
    rewrite [X in (X < _)%N]card_imfset//= [X in (_ < X)%N]card_imfset//=.
    do 2 rewrite undup_id ?uniq_dec_roots//.
    rewrite (@perm_size _ _ [seq x%:C%C | x <- rootsR (evalpmp z p)]); last exact/perm_eqC.
    rewrite [X in (_ < X)%N](@perm_size _ _ [seq x%:C%C | x <- rootsR (evalpmp y p)]); last exact/perm_eqC.
    by rewrite !size_map r_const// r_const// ltnn.
  rewrite -2!srE [X in (X < _)%N](card_imfset _ _ val_inj)/=.
  rewrite [X in (_ < X)%N](card_imfset _ _ val_inj)/=.
  suff /fsubset_leq_card zy: sr z `<=` [fset fyz x | x in (sr y `\ u)].
    apply/(leq_ltn_trans zy).
    rewrite [X in (X < _)%N]card_imfset/=; last exact/bij_inj.
    rewrite -add1n.
    have/(congr1 nat_of_bool) /= <-: u \in sr y by rewrite mem_imfset.
    by rewrite -cardfsD1 leqnn.
  apply/fsubsetP => /= a.
  rewrite [X in _ X -> _](mem_imfset _ _ (@inj_id _))/= => ar.
  case: (fyzb) => fzy fyzK fzyK.
  apply/imfsetP; exists (fzy a) => /=; last by rewrite [RHS]fzyK.
  rewrite in_fsetD1 -(bij_eq fyzb) fzyK; apply/andP; split.
    apply/eqP; move: ar => /[swap] ->.
    by move/negP: fur.
  rewrite (mem_imfset _ _ (@inj_id _))/=.
  by apply/fyzr; rewrite fzyK.
have fir: val (fyz.[pyrP i ir])%fmap \is Num.real.
  by rewrite -fyzr/=; apply/complex_realP; exists (rootsR (evalpmp y p))`_i.
have fiR: complex.Re (val (fyz [` pyrP i ir])) \in rootsR (evalpmp z p).
  rewrite in_rootsR.
  move: (q0 z zs); rewrite map_poly_eq0 => -> /=.
  move: (fsvalP (fyz [` pyrP i ir])).
  rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots => /andP[_].
  by rewrite -{1}[val _]RRe_real// fmorph_root.
rewrite -(RRe_real fir); congr (_%:C%C).
rewrite -(nth_index 0 fiR); congr (_`__).
rewrite -[LHS](count_lt_nth 0 (sorted_roots _ _ _) ir).
move: (fiR); rewrite -index_mem => fiRs.
rewrite -[RHS](count_lt_nth 0 (sorted_roots _ _ _) fiRs) -!/(rootsR _).
rewrite (nth_index 0 fiR).
pose sr y z := [fset x : [fset x in dec_roots (q y)] | val x < z].
have srE a b: [fset val x | x in sr a b] = [fset x | x in dec_roots (q a) & x < b].
  apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => b';
  rewrite (mem_imfset _ _ (@inj_id _))/=.
    move=> /imfsetP[/=] c /imfsetP[/=] c' cr -> ->.
    apply/andP; split=> //=.
    by move: (fsvalP c'); rewrite (mem_imfset _ _ (@inj_id _))/=.
  move=> /andP[] qb br; apply/imfsetP => /=.
  have bP: b' \in [fset x0 | x0 in dec_roots (q a)].
    by rewrite mem_imfset.
  exists [` bP] => //.
  by rewrite (mem_imfset _ _ (@inj_id _))/=.
have {}perm_eqC a b: perm_eq
    [seq x0 <- dec_roots (q a) | (x0 < b%:C%C)%R]
    [seq x%:C%C | x <- [seq x <- rootsR (evalpmp a p) | (x < b)%R]].
  apply/uniq_perm.
  - exact/filter_uniq/uniq_dec_roots.
  - rewrite map_inj_uniq; last exact/complexI.
    exact/filter_uniq/uniq_roots.
  move=> u; rewrite mem_filter mem_dec_roots map_poly_eq0.
  apply/andP/mapP => [[] ub /andP[] pa0|[] v + ->].
    move: ub; rewrite ltcE/= => /andP[] /eqP u0 ub.
    rewrite (complexE u) -u0 mulr0 addr0 fmorph_root => pu.
    exists (complex.Re u) => //.
    by rewrite mem_filter ub/= in_rootsR pa0.
  rewrite mem_filter in_rootsR => /andP[] vb /andP[] pa0 pv; split.
    by rewrite ltcR.
  by rewrite pa0/=; apply/rmorph_root.
suff: (#|` [fset x | x in dec_roots (q y) & (x < ((rootsR (evalpmp y p))`_i)%:C%C)%R]| = #|` [fset x | x in dec_roots (q z) & (x < val (fyz [` pyrP i ir]))%R]|)%N.
  rewrite [LHS]card_imfset//= [RHS]card_imfset//=.
  do 2 rewrite undup_id ?uniq_dec_roots//.
  rewrite (@perm_size _ _ [seq x%:C%C | x <- [seq x <- rootsR (evalpmp y p) | (x < (rootsR (evalpmp y p))`_i)%R]]); last exact/perm_eqC.
  rewrite -{1}(RRe_real fir).
  rewrite [RHS](@perm_size _ _ [seq x%:C%C | x <- [seq x <- rootsR (evalpmp z p) | (x < complex.Re (val (fyz [` pyrP i ir])))%R]]); last exact/perm_eqC.
  by rewrite !size_map !size_filter.
rewrite -2!srE [LHS](card_imfset _ _ val_inj)/= [RHS](card_imfset _ _ val_inj)/=.
suff ->: sr z (val (fyz [` pyrP i ir])) = [fset fyz x | x in sr y (((rootsR (evalpmp y p))`_i)%:C)%C].
  by rewrite [RHS](card_imfset _ _ (bij_inj fyzb)).
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => /= u.
  rewrite [X in _ X -> _](mem_imfset _ _ (@inj_id _))/= => ui.
  case: (fyzb) => fzy fyzK fzyK.
  apply/imfsetP; exists (fzy u) => /=; last by rewrite fzyK.
  rewrite (mem_imfset _ _ (@inj_id _))/=.
  have {}ui: val u < val (fyz [` pyrP i ir]) by [].
  have ur: val u \is Num.real by apply/negP => /negP/(Nreal_ltF fir)/negP.
  have fur: val (fzy u) \is Num.real by rewrite fyzr fzyK.
  suff: val (fzy u) < ((rootsR (evalpmp y p))`_i)%:C%C by [].
  rewrite -(RRe_real fur) ltcR ltNge; apply/negP => iu.
  suff: [` pyrP i ir] = fzy u by move=> iuE; move: ui; rewrite iuE fzyK ltxx.
  apply/eP; rewrite /= -(RRe_real fur) -rmorphB/= normcR mulrC mulr_natr -rmorphMn/= ltcR.
  apply/ltr_normlP; split; last first.
    rewrite -subr_le0 in iu; apply/(le_lt_trans iu).
    by rewrite pmulrn_lgt0// -ltcR.
  rewrite opprB -(subrBB (complex.Re (val u))) opprB mulr2n; apply/ltrD.
    apply/ltr_normlW; rewrite -ltcR -normcR rmorphB/= (RRe_real fur) (RRe_real ur).
    by rewrite -{2}(fzyK u); apply/fyze.
  rewrite -(subrBB (complex.Re (val (fyz [` pyrP i ir])))) opprB -(add0r e').
  apply/ltrD; first by rewrite subr_lt0; move: ui; rewrite ltcE => /andP[_].
  apply/ltr_normlW; rewrite -ltcR -normcR rmorphB/= [X in X - _]RRe_real.
    by rewrite -normrN opprB; apply/(fyze [` pyrP i ir]).
  by rewrite -fyzr/=; apply/complex_realP; exists (rootsR (evalpmp y p))`_i.
move=> /imfsetP[/=] v + ->.
rewrite (mem_imfset _ _ (@inj_id _))/= => vi.
have {}vi: val v < ((rootsR (evalpmp y p))`_i)%:C%C by [].
have vr: val v \is Num.real.
  apply/negP => /negP vr; move: vi; rewrite Nreal_ltF//.
  by apply/complex_realP; exists (rootsR (evalpmp y p))`_i.
rewrite (mem_imfset _ _ (@inj_id _))/=.
suff: val (fyz v) < val (fyz [` pyrP i ir]) by [].
have fvr: val (fyz v) \is Num.real by rewrite -fyzr.
rewrite -(RRe_real fvr) -(RRe_real fir) ltcR ltNge; apply/negP => iv.
suff vE: v = [` pyrP i ir] by rewrite vE/= ltxx in vi.
apply/eP; rewrite /= -(RRe_real vr) -rmorphB/= normcR mulrC mulr_natr -rmorphMn/= ltcR.
apply/ltr_normlP; split; last first.
  rewrite -(RRe_real vr) ltcR -subr_lt0 in vi; apply/(lt_trans vi).
  by rewrite pmulrn_lgt0// -ltcR.
rewrite opprB -(subrBB (complex.Re (val (fyz [`pyrP i ir])))) opprB mulr2n; apply/ltrD.
  apply/ltr_normlW; rewrite -ltcR -normcR rmorphB/= (RRe_real fir).
  exact/(fyze [` pyrP i ir]).
rewrite -(subrBB (complex.Re (val (fyz v)))) opprB -(add0r e').
apply/ler_ltD; first by rewrite subr_le0.
apply/ltr_normlW; rewrite -ltcR -normcR rmorphB/= (RRe_real fvr) (RRe_real vr).
rewrite -normrN opprB; apply/fyze.
Qed. *)
admit.
Admitted.
  

  




Definition SAevalpmp_graph n (p : {poly {mpoly R[n]}}) : {SAset R^(n + (size p))} :=
  [set| \big[And/True]_(i < size p)
      subst_formula (rcons (iota 0 n) (n + i)%N) (SAmpoly p`_i)].

Lemma SAevalpmp_graphP n (p : {poly {mpoly R[n]}}) (u : 'rV[R]_n) (v : 'rV[R]_(size p)) :
  (row_mx u v \in SAevalpmp_graph p) = (v == \row_i (evalpmp u p)`_i).
Proof.
apply/SAin_setP/eqP => [/holdsAnd /= vE|->].
  apply/rowP => i; rewrite mxE coef_map/=.
  move: vE => /(_ i (mem_index_enum _) isT) /holds_subst.
  rewrite enum_ordD map_cat -2!map_comp -cats1 subst_env_cat.
  rewrite subst_env_iota_catl/=; last by rewrite size_map size_enum_ord.
  rewrite nth_cat size_map size_enum_ord ltnNge leq_addr/=.
  rewrite subDnCA// subnn addn0 nth_map_ord mxE (unsplitK (inr _)) => vE.
  suff: SAmpoly p`_i u = \row__ v ord0 i.
    rewrite SAmpolyE => /eqP; rewrite rowPE forall_ord1 !mxE => /eqP /esym ->.
    by apply/meval_eq => j; rewrite tnth_mktuple.
  apply/eqP; rewrite inSAfun; apply/rcf_satP; move: vE; congr holds.
  rewrite ngraph_cat/= enum_ordSl enum_ord0/= mxE; congr cat.
  by apply/eq_map => j /=; rewrite mxE (unsplitK (inl _)).
apply/holdsAnd => /= i _ _; apply/holds_subst.
rewrite enum_ordD map_cat -2!map_comp -cats1 subst_env_cat.
rewrite subst_env_iota_catl/=; last by rewrite size_map size_enum_ord.
rewrite nth_cat size_map size_enum_ord ltnNge leq_addr/=.
rewrite subDnCA// subnn addn0 nth_map_ord mxE (unsplitK (inr _)) mxE coef_map/=.
move: (SAmpolyE p`_i u) => /eqP; rewrite inSAfun => /rcf_satP; congr holds.
rewrite ngraph_cat/= enum_ordSl enum_ord0/= mxE; congr (_ ++ [:: _]).
  by apply/eq_map => j /=; rewrite mxE (unsplitK (inl _)).
by apply/meval_eq => j; rewrite tnth_mktuple.
Qed.

Fact SAfun_SAevalpmp n (p : {poly {mpoly R[n]}}) :
  (SAevalpmp_graph p \in @SAfunc _ n (size p)) && (SAevalpmp_graph p \in @SAtot _ n (size p)).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAevalpmp_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row_i (evalpmp u p)`_i)%R.
by rewrite SAevalpmp_graphP eqxx.
Qed.

Definition SAevalpmp n (p : {poly {mpoly R[n]}}) := MkSAfun (SAfun_SAevalpmp p).

Lemma SAevalpmpE n (p : {poly {mpoly R[n]}}) (u : 'rV[R]_n) :
  SAevalpmp p u = (\row_i (evalpmp u p)`_i)%R.
Proof. by apply/eqP; rewrite inSAfun SAevalpmp_graphP. Qed.

Lemma evalpmpM n (p q : {poly {mpoly R[n]}}) (x : 'rV_n) :
  (evalpmp x (p * q) = (evalpmp x p) * (evalpmp x q))%R.
Proof.
apply/polyP => i.
rewrite !coef_map/= !coefM meval_sum.
apply/eq_bigr => /= j _.
by rewrite mevalM !coef_map.
Qed.

(* TODO: subsumed by `rmorph_prod` (with occurence) *)
Lemma evalpmp_prod [I : Type] n (x : 'rV_n) (r : seq I) (F : I -> {poly {mpoly R[n]}}) (P : pred I) :
  evalpmp x (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) evalpmp x (F i).
Proof.
elim: r => [|i r IHr].
  by apply/polyP => i; rewrite !big_nil/= coef_map/= !coef1 mevalMn meval1.
rewrite !big_cons; case: (P i) => [|//].
by rewrite evalpmpM IHr.
Qed.

Lemma evalpmp_prod_const n (P : {fset {poly {mpoly R[n]}}}) (s : {SAset R^n}) :
  SAconnected s ->
  {in P, forall p, {in s &, forall x y, size (evalpmp x p) = size (evalpmp y p)}} ->
  {in P, forall p, {in s &, forall x y, size (gcdp (evalpmp x p) (evalpmp x p)^`()) = size (gcdp (evalpmp y p) (evalpmp y p)^`())}} ->
  {in P &, forall p q, {in s &, forall x y, size (gcdp (evalpmp x p) (evalpmp x q)) = size (gcdp (evalpmp y p) (evalpmp y q))}} ->
  {in s &, forall x y, size (gcdp (evalpmp x (\prod_(p : P) (val p))) (evalpmp x (\prod_(p : P) (val p)))^`()) = size (gcdp (evalpmp y (\prod_(p : P) (val p))) (evalpmp y (\prod_(p : P) (val p)))^`())} /\
  {in s &, forall x y, size (rootsR (evalpmp x (\prod_(p : P) (val p)))) = size (rootsR (evalpmp y (\prod_(p : P) (val p))))}.
Proof.
  (*move=> Scon psize proots pqsize.
apply/all_and2 => x; apply/all_and2 => y; apply/all_and2 => xs; apply/all_and2.
case: n P s Scon psize proots pqsize x y xs => [|n] P s Scon psize proots pqsize x y xS yS.
  by have ->: x = y by apply/rowP => -[].
case: (eqVneq (evalpmp x (\prod_(p : P) val p)) 0) => px0.
  rewrite px0.
  move: px0; rewrite !evalpmp_prod => /eqP/prodf_eq0/= [p] _.
  rewrite -size_poly_eq0 (psize (val p) (fsvalP p) x y xS yS) size_poly_eq0 => py0.
  suff ->: \prod_(p : P) evalpmp y (val p) = 0 by [].
  by apply/eqP/prodf_eq0; exists p.
have p0: {in P, forall p, {in s, forall x, size (evalpmp x p) != 0}}.
  move=> p pP z zS; rewrite (psize _ pP z x zS xS) size_poly_eq0.
  by move: px0; rewrite evalpmp_prod => /prodf_neq0/(_ [` pP] isT).
have R0: [char R[i]] =i pred0 by apply/char_num.
have pmsize: {in s &, forall x y, size (evalpmp x (\prod_(p : P) \val p)) = size (evalpmp y (\prod_(p : P) \val p))}.
  move=> {px0} {}x {}y {}xS {}yS.
  rewrite !evalpmp_prod size_prod; last first.
    by move=> /= p _; rewrite -size_poly_eq0 (p0 _ (fsvalP p) x xS).
  rewrite size_prod; last first.
    by move=> /= p _; rewrite -size_poly_eq0 (p0 _ (fsvalP p) y yS).
  under eq_bigr => /= p _.
    rewrite (psize _ (fsvalP p) x y xS yS).
  over.
  by [].
have rE (u : 'rV[R]_n.+1) :
      (size (rootsR (evalpmp u (\prod_(p : P) \val p))))%:R = SAcomp (SAnbroots _ _) (SAevalpmp (\prod_(p : P) \val p)) u ord0 ord0.
  rewrite SAcompE/= SAevalpmpE SAnbrootsE mxE.
  congr (size (rootsR _))%:R.
  apply/polyP => i; rewrite coef_poly.
  case: ltnP => ilt; last first.
    exact/nth_default/(leq_trans (size_poly _ _) ilt).
  by rewrite -/(nat_of_ord (Ordinal ilt)) nth_map_ord mxE.
have cE (u : 'rV[R]_n.+1) :
    (size (dec_roots (map_poly (real_complex R) (evalpmp u (\prod_(p : P) \val p)))))%:R = SAcomp (SAnbrootsC _ _) (SAevalpmp (\prod_(p : P) \val p)) u ord0 ord0.
  rewrite SAcompE/= SAevalpmpE SAnbrootsCE mxE.
  congr (size (dec_roots _))%:R.
  apply/polyP => i; rewrite !coef_poly.
  case: ltnP => ilt; last first.
    case: ltnP => [|//] ilt'.
    by rewrite (nth_mktuple _ _ (Ordinal ilt')) mxE nth_default.
  case: ltnP => [|//] ilt'.
  by rewrite (nth_mktuple _ _ (Ordinal ilt')) mxE coef_map/=.
suff: locally_constant_on (SAcomp (SAnbroots _ _) (SAevalpmp (\prod_(p : P) \val p))) [set` s] /\
  locally_constant_on (SAcomp (SAnbrootsC _ _) (SAevalpmp (\prod_(p : P) \val p))) [set` s].
  move=> [] rc cc; split; last first.
    apply/(mulrIn (@oner_neq0 R)).
    rewrite !rE; congr (_ _ ord0 ord0).
    by move: {px0} x y xS yS; apply/SAconnected_locally_constant_constant.
  move: cc => /(SAconnected_locally_constant_constant Scon)-/(_ x y xS yS).
  move=> /(congr1 (fun x : 'rV_1 => x ord0 ord0)).
  rewrite -!cE => /(mulrIn (@oner_neq0 R)).
  rewrite size_dec_roots// [in RHS]size_dec_roots//.
  rewrite size_divp; last by rewrite gcdp_eq0 map_poly_eq0 negb_and px0.
  rewrite size_divp; last first.
    rewrite gcdp_eq0 map_poly_eq0 -size_poly_eq0 (pmsize y x yS xS) negb_and.
    by rewrite size_poly_eq0 px0.
  rewrite !deriv_map/= -!gcdp_map !size_map_poly.
  rewrite subn_pred ?leq_gcdpl//; last first.
    by rewrite lt0n size_poly_eq0 gcdp_eq0 negb_and px0.
  rewrite subn_pred ?leq_gcdpl//; last first.
  - by rewrite -size_poly_eq0 (pmsize y x yS xS) size_poly_eq0 px0.
  - rewrite lt0n size_poly_eq0 gcdp_eq0 negb_and.
    by rewrite -size_poly_eq0 (pmsize y x yS xS) size_poly_eq0 px0.
  rewrite !succnK (pmsize x y xS yS) => /eqP.
  rewrite eqn_sub2lE; first by move=> /eqP.
    by rewrite (pmsize y x yS xS) leq_gcdpl.
  by rewrite leq_gcdpl// -size_poly_eq0 (pmsize y x yS xS) size_poly_eq0 px0.
move=> {x y xS yS px0}.
apply/all_and2 => x; apply/all_and2; rewrite inE/= => xs.
have ex_and: forall T (P Q : T -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
  move=> T P0 Q [] a [] Pa Qa.
  by split; exists a.
apply/ex_and.
pose pc := fun (p : P) (x : 'rV[R]_n.+1) => map_poly (real_complex R) (evalpmp x (\val p)).
pose rx := dec_roots (\prod_(p : P) pc p x).
pose d := (\big[Order.min/1]_(x <- rx) \big[Order.min/1]_(y <- rx | y != x) (complex.Re `|x - y| / 2))%:C%C.
have d0 : 0 < d.
  rewrite ltcE/= eqxx/= lt_bigmin ltr01/=; apply/allP => u _.
  rewrite -big_filter lt_bigmin ltr01/=; apply/allP => v.
  rewrite mem_filter => /andP[] vu _.
  apply/divr_gt0; last exact/ltr0Sn.
  by rewrite -ltcR (normr_gt0 (u - v)) subr_eq0 eq_sym.
have /= dP: {in rx &, forall u v, (`|u - v| < 2*d)%R -> u = v}.
  move=> u v ux vx uvd; apply/eqP; rewrite -[_ == _]negbK; apply/negP => uv.
  move: uvd.
  rewrite mulrC mulr_natr -rmorphMn/= -(RRe_real (normr_real _)) ltcR -mulr_natr.
  rewrite -ltr_pdivrMr ?ltr0Sn// lt_bigmin => /andP[_] /allP-/(_ u ux) /=.
  rewrite lt_bigmin => /andP[_] /allP-/(_ v vx) /implyP.
  by rewrite eq_sym ltxx => /(_ uv).
have /fin_all_exists /=: forall p : P, exists delta, 0 < delta /\ forall (y : 'rV[R]_n.+1), y \in s -> `|x - y| < delta -> alignp d (pc p x) (pc p y).
  move=> p.
  case: (aligned_deformed (pc p x) d0) => /= [[]] e eI [].
  rewrite ltcE/= => /andP[/eqP ->] e0; rewrite complexr0 => ed.
  have /fin_all_exists /=: forall i : 'I_(size (val p)).+1, exists delta, 0 < delta /\ forall (y : 'rV[R]_n.+1), y \in s -> `|x - y| < delta -> `|(pc p x)`_i - (pc p y)`_i| < e%:C%C.
    move=> i.
    move: (@meval_continuous _ _ (val p)`_i x).
    rewrite /= /continuous_at.
    move=> /(@cvgr_dist_lt _ (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod R)).
    move=> /(_ _ e0) /nbhs_ballP[] d'/= d'0 /subsetP xd'.
    exists d'; split=> // y ys xy.
    move: xd' => /(_ y); mp; first by rewrite -ball_normE inE/=.
    rewrite inE/= !coef_map/= -rmorphB/= normc_def/= expr0n/= addr0 sqrtr_sqr ltcR.
    by congr (normr (_ - _) < e); apply/meval_eq => j; rewrite tnth_mktuple.
  move=> [d'] d'P; exists (\big[minr/1]_i d' i).
  split; first by rewrite lt_bigmin ltr01; apply/allP => i _ /=; case: (d'P i).
  move=> y ys; rewrite lt_bigmin => /andP[_] /allP xy; apply/ed.
  split=> [|i].
    suff ->: size (pc p y) = size (pc p x) by [].
    by rewrite !size_map_poly; apply/psize => //; apply/fsvalP.
  move: (ltn_ord i); rewrite [X in (i < X)%N]size_map_poly => ilt.
  have {}ilt := leq_trans (leq_trans ilt (size_poly _ _)) (leqnSn _).
  case: (d'P (Ordinal ilt)) => _ /=; apply=> //.
  exact/xy/mem_index_enum.
move=> [d'] xd'.
have d'0: 0 < \big[minr/1]_(p : P) d' p.
  rewrite lt_bigmin ltr01; apply/allP => p _ /=.
  by case: (xd' p).
exists (ball x (\big[Order.min/1]_(p : P) d' p)).
have andxx (a b c : Prop) : a /\ b /\ c -> (a /\ b) /\ (a /\ c).
  by move=> [] ? [] ? ?.
apply/andxx; split; first exact/open_subspaceW/ball_open.
apply/andxx; split; first by rewrite inE; apply ballxx.
apply/all_and2 => y; rewrite in_setI.
apply/all_and2 => /andP[]; rewrite inE/= => ys.
rewrite -ball_normE inE/= lt_bigmin => /andP[_] /allP/= xy.
pose rs := fun x => [fset x in (rootsR (evalpmp x (\prod_(p : P) \val p)))].
have card_rs : forall x, #|` rs x | = size (rootsR (evalpmp x (\prod_(p : P) \val p))).
  by move=> z; rewrite /rs card_imfset//= undup_id// uniq_roots.
have pc0 p z: z \in s -> pc p z != 0.
  by rewrite map_poly_eq0 -size_poly_eq0; apply/p0 => //; apply/fsvalP.
have pcM0 z: z \in s -> \prod_(p : P) pc p z != 0.
  by move=> zs; apply/prodf_neq0 => /= p _; apply/pc0.
have: exists (fxy : forall p,
      [fset x in dec_roots (pc p x)] -> [fset x in dec_roots (pc p y)]),
    forall p u, `|val u - val (fxy p u)| < d.
  apply/(fin_all_exists (P:=fun p f => forall u, `|val u - val (f u)| < d)).
  move=> /= p; apply/(fin_all_exists (P:=fun u v => `|val u - val v| < d)).
  case=> /= u; rewrite mem_imfset//= mem_dec_roots => /andP[_] pu.
  move: xy => /(_ p (mem_index_enum _)).
  move: xd' => /(_ p)[_] /(_ y ys) /[apply] /(_ u pu).
  rewrite -big_filter; case rsy: (seq.filter _ _) => [|v l].  
    by rewrite big_nil leqn0 mu_eq0 ?pu// pc0.
  move: (mem_head v l); rewrite -rsy mem_filter -normrN opprB => /andP[] uv pv _.
  suff vP: v \in [fset x in dec_roots (pc p y)]. 
    by exists [` vP].
  by rewrite mem_imfset//= mem_dec_roots pc0.
move=> [/=] fxy fxyd.
have fxy_bij: forall p, bijective (fxy p).
  move=> p; apply/inj_card_bij; last first.
    rewrite -2!cardfE card_imfset//= card_imfset//=.
    do 2 rewrite undup_id ?uniq_dec_roots//.
    rewrite (size_dec_roots (pc p x) R0) (size_dec_roots (pc p y) R0).
    rewrite size_divp; last by rewrite gcdp_eq0 negb_and pc0.
    rewrite size_divp; last by rewrite gcdp_eq0 negb_and pc0.
    rewrite ![(pc _ _)^`()]deriv_map -!gcdp_map !size_map_poly -!/(evalpmp _ _).
    rewrite (psize (val p) (fsvalP p) x y xs ys).
    by rewrite (proots (val p) (fsvalP p) x y xs ys).
  move=> /= u v => uv; apply/val_inj/dP.
  - move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite mem_dec_roots => /andP[_] pu.
    rewrite /rx mem_dec_roots pcM0//= root_bigmul/=.
    by apply/hasP; exists p => //; apply/mem_index_enum.
  - move: (fsvalP v); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite mem_dec_roots => /andP[_] pv.
    rewrite /rx mem_dec_roots pcM0//= root_bigmul/=.
    by apply/hasP; exists p => //; apply/mem_index_enum.
  - rewrite -(subrBB (val (fxy p u))) {2}uv; apply/(le_lt_trans (ler_normB _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD; apply/fxyd.
have: exists (fyx : forall p,
      [fset x in dec_roots (pc p y)] -> [fset x in dec_roots (pc p x)]),
    forall p, cancel (fxy p) (fyx p) /\ cancel (fyx p) (fxy p).
  apply/(fin_all_exists (P:=fun p f => cancel (fxy p) f /\ cancel f (fxy p))).
  move=> /= p.
  by case: (fxy_bij p) => g; exists g.
move=> [] fyx fK.
have fxyK p : cancel (fxy p) (fyx p) by case: (fK p).
have {fK} fyxK p : cancel (fyx p) (fxy p) by case: (fK p).
have fyxd p (u : [fset x in dec_roots (pc p y)]) :
    `|val u - val (fyx p u)| < d.
  move: (fyxK p u) => /(congr1 val)/= uE.
  by rewrite -{1}uE -normrN opprB; apply/fxyd.
have lift p z (u : [fset x in dec_roots (pc p z)]) :
    z \in s ->
    val u \in [fset x in dec_roots (\prod_(p : P) pc p z)].
  case: u => /= u; rewrite mem_imfset//= mem_dec_roots => /andP[_] pu zs.
  rewrite mem_imfset//= mem_dec_roots pcM0//= root_bigmul.
  by apply/hasP; exists p => //; apply/mem_index_enum.
have unlift z (u : [fset x in dec_roots (\prod_(p : P) pc p z)]) :
    {p : P | val u \in [fset x in dec_roots (pc p z)]}.
  case: u => /= u; rewrite mem_imfset//= mem_dec_roots root_bigmul prodf_seq_neq0.
  move=> /andP[+] /hasP/sig2W[/=] p _ pu => /allP/(_ p (mem_index_enum _)) /= pz0.
  by exists p; rewrite mem_imfset//= mem_dec_roots pz0.
have /fin_all_exists/=: forall (u : [fset x in dec_roots (\prod_(p : P) pc p x)]), exists (v : [fset x in dec_roots (\prod_(p : P) pc p y)]), `|val u - val v| < d.
  move=> u; case: (unlift x u) => p pu.
  by exists [` (lift p y (fxy p [` pu]) ys)] => /=; apply/fxyd.
move=> []gxy gxyd.
have /fin_all_exists/=: forall (u : [fset x in dec_roots (\prod_(p : P) pc p y)]), exists (v : [fset x in dec_roots (\prod_(p : P) pc p x)]), `|val u - val v| < d.
  move=> u; case: (unlift y u) => p pu.
  by exists [` (lift p x (fyx p [` pu]) xs)] => /=; apply/fyxd.
move=> []gyx gyxd.
have gyxE p (u : [fset x in dec_roots (pc p y)]) :
    gyx [` lift p y u ys] = [` lift p x (fyx p u) xs].
  apply/val_inj/dP => /=.
  - by move: (fsvalP (gyx [`lift p y u ys])); rewrite (mem_imfset _ _ (@inj_id _))/=.
  - by move: (lift p x (fyx p u) xs); rewrite (mem_imfset _ _ (@inj_id _))/=.
  rewrite -(subrBB (val u)) opprB -normrN opprD opprB.
  apply/(le_lt_trans (ler_normB _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/gyxd.
  exact/fyxd.
have size_pc (p : {poly R[i]}) : size p = ((\sum_(u <- dec_roots p) \mu_u p) + (p != 0%R))%N.
  have [->|{}p0] := eqVneq p 0; first by rewrite size_poly0 dec_roots0 big_nil.
  move: (dec_roots_closedP p) => /(congr1 (fun p : {poly _} => size p)).
  rewrite size_scale; last by rewrite -lead_coefE lead_coef_eq0 p0.
  rewrite size_prod_seq => /= [| w _]; last first.
    by rewrite expf_eq0 polyXsubC_eq0 andbF.
  under eq_bigr do rewrite my_size_exp ?polyXsubC_eq0// size_XsubC/= mul1n -addn1.
  by rewrite big_split/= sum1_size -addSn subDnAC// subnn -addn1.
have dP' p u: (count (fun v => (`|u - v| < d)%R) (dec_roots (pc p x)) <= 1)%N.
  rewrite -size_filter.
  move: (filter_uniq (fun v => `|u - v| < d) (uniq_dec_roots (pc p x))).
  case rsdE: (seq.filter _ _) => [//|a rsd].
  case: rsd rsdE => [//|b rsd] rsdE /= /andP[] + _.
  rewrite in_cons negb_or => /andP[] /eqP + _.
  have: a \in [:: a, b & rsd] by exact/mem_head.
  have: b \in [:: a, b & rsd] by rewrite in_cons mem_head orbT.
  rewrite -rsdE !mem_filter !mem_dec_roots.
  move=> /andP[] wbd /andP[_] bx /andP[] wba /andP[_] ax.
  elim; apply/dP.
  - rewrite mem_dec_roots pcM0//= root_bigmul.
    apply/hasP; exists p => //; apply/mem_index_enum.
  - rewrite mem_dec_roots pcM0//= root_bigmul.
    by apply/hasP; exists p => //; apply/mem_index_enum.
  rewrite -(subrBB u) opprB -normrN opprD opprB.
  apply/(le_lt_trans (ler_normB _ _)).
  by rewrite mulr2n mulrDl mul1r; apply/ltrD.
have ball_root1 (p : P) (u : [fset x | x in dec_roots (\prod_p pc p y)]) :
  root (pc p y) (val u) ->
  [seq v <- dec_roots (pc p y) | `|v - val (gyx u)| < d] = [:: val u].
  move=> pu.
  have: all (fun v => v == val u) [seq v <- dec_roots (pc p y) | `|v - val (gyx u)| < d].
    apply/allP => v; rewrite mem_filter => /andP[] vu vp.
    have uP: val u \in [fset x | x in dec_roots (pc p y)].
      by rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots pc0.
    have vP: v \in [fset x | x in dec_roots (pc p y)] by rewrite mem_imfset.
    apply/eqP; rewrite -[val u]/(val [` uP]) -[v]/(val [` vP]) ; congr val.
    apply/(can_inj (fyxK p))/val_inj/dP.
    - by move: (fsvalP [` lift p x (fyx p [` vP]) xs]); rewrite (mem_imfset _ _ (@inj_id _))/=.
    - by move: (fsvalP [` lift p x (fyx p [` uP]) xs]); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite -(subrBB v) opprB -normrN opprD opprB.
    apply/(le_lt_trans (ler_normB _ _)).
    rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/fyxd.
    move: vu; congr (`|_ - _| < d).
    rewrite -[RHS]/(val [` lift p x (fyx p [` uP]) xs]) -gyxE.
    by congr (val (gyx _)); apply/val_inj.
  have: uniq [seq v <- dec_roots (pc p y) | `|v - val (gyx u)| < d].
    exact/filter_uniq/uniq_dec_roots.
  have: val u \in [seq v <- dec_roots (pc p y) | `|v - val (gyx u)| < d].
    by rewrite mem_filter gyxd mem_dec_roots pc0.
  case: (seq.filter _ _) => [|/= a l]; first by rewrite in_nil.
  move=> _ /[swap] /andP[] /eqP ->.
  by case: l => [//|b l] /= /andP[] /eqP -> _; rewrite mem_head.
have gxyK: cancel gxy gyx.
  move=> u; apply/val_inj/dP.
  - by move: (fsvalP (gyx (gxy u))); rewrite (mem_imfset _ _ (@inj_id _))//.
  - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))//.
  rewrite -(subrBB (val (gxy u))) -normrN !opprB.
  apply/(le_lt_trans (ler_normD _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/gxyd.
  exact/gyxd.
have gyx_root p (u : [fset x | x in dec_roots (\prod_p pc p y)]) :
  root (pc p y) (val u) -> root (pc p x) (val (gyx u)).
  move=> pu.
  have uP: val u \in [fset x | x in dec_roots (pc p y)].
    by rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots pc0.
  move: (fsvalP (fyx p [` uP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
  rewrite mem_dec_roots pc0 //=; congr root.
  rewrite -[LHS]/(val [` lift p x (fyx p [` uP]) xs]) -gyxE.
  by congr (val (gyx _)); apply/val_inj.
have ltnn_ne (a b : nat) : (a < b)%N -> a <> b.
  by move=> /[swap] ->; rewrite ltnn.
have mu_gyx p (u : [fset x | x in dec_roots (\prod_p pc p y)]) :
    root (pc p y) (val u) ->
    \mu_(val (gyx u)) (pc p x) = \mu_(val u) (pc p y).
  move=> pu.
  apply/le_anti/andP; split.
    case: (xd' p) => _ /(_ y ys (xy p (mem_index_enum _)))/(_ (val (gyx u))).
    move=> /(_ (gyx_root p u pu)).
    by rewrite -[X in (_ <= X)%N]big_filter ball_root1 ?big_seq1.
  rewrite /Order.le/= leqNgt; apply/negP => mpu.
  move: (psize (val p) (fsvalP p) x y xs ys).
  move: (size_pc (pc p x)) (size_pc (pc p y)).
  rewrite !size_map_poly => -> -> /eqP.
  rewrite !pc0// !addn1 eqSS => /eqP.
  rewrite -[RHS](big_rmcond_in (fun u => has (fun v => `|u - v| < d) (dec_roots (pc p x))))/=; last first.
    move=> v pv.
    have vP : v \in [fset x | x in dec_roots (pc p y)] by rewrite mem_imfset//=.
    rewrite -all_predC => /allP.
    move: (fsvalP (fyx p [` vP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
    by move=> /[swap]/[apply]; rewrite fyxd.
  rewrite (@big_hasE _ _ _ _ _ _ xpredT)/= => [|v _]; last exact/dP'.
  apply/ltnn_ne; rewrite big_seq_cond [X in (_ < X)%N]big_seq_cond.
  rewrite ltn_sum//= => [v|].
    rewrite andbT mem_dec_roots => /andP[_] pv.
    by case: (xd' p) => _ /(_ y ys (xy p (mem_index_enum _)))/(_ v pv).
  apply/hasP; exists (val (gyx u)).
    by rewrite mem_dec_roots pc0//=; apply/gyx_root.
  rewrite mem_dec_roots pc0//= gyx_root//=.
  apply/(leq_trans mpu).
  rewrite [X in (_ <= X)%N]big_mkcond (bigD1_seq (val u))/=; first last.
  - exact/uniq_dec_roots.
  - by rewrite mem_dec_roots pc0.
  by rewrite gyxd leq_addr.
have gyxK: cancel gyx gxy.
  move=> v; apply/val_inj; move: (gyx v) (gyxd v) => u vud.
  case: (unlift y v) (gxy u) (gxyd u) => p pv w uw.
  case: (unlift y w) => q qw.
  apply/eqP; rewrite -[_ == _]negbK; apply/negP => /eqP wv. 
  move: (pqsize (val p) (val q) (fsvalP p) (fsvalP q) x y xs ys).
  move: (size_pc (gcdp (pc p x) (pc q x))) (size_pc (gcdp (pc p y) (pc q y))).
  rewrite !gcdp_eq0 !negb_and !pc0//= !addn1 -!gcdp_map !size_map_poly => -> -> /eqP.
  rewrite eqSS !gcdp_map -!/(pc _ _) => /eqP/esym.
  under eq_bigr do rewrite mu_gcdp ?pc0//.
  under [in RHS]eq_bigr do rewrite mu_gcdp ?pc0//.
  apply/ltnn_ne.
  rewrite -(big_rmcond_in (fun u => has (fun v => `|u - v| < d) (dec_roots (gcdp (pc p x) (pc q x)))))/=; last first.
    move=> a; rewrite mem_dec_roots root_gcd => /andP[_] /andP[] pa qa.
    rewrite -all_predC => /allP/=.
    have aP: a \in [fset x in dec_roots (\prod_(p : P) pc p y)].
      rewrite mem_imfset//= mem_dec_roots pcM0//= root_bigmul.
      by apply/hasP; exists p => //; apply/mem_index_enum.
    suff /[swap]/[apply]: val (gyx [` aP]) \in dec_roots (gcdp (pc p x) (pc q x)).
      by rewrite gyxd.
    by rewrite mem_dec_roots gcdp_eq0 negb_and !pc0//= root_gcd !gyx_root//.
  rewrite (@big_hasE _ _ _ _ _ _ xpredT)/=; last first.
    move=> a _; rewrite -size_filter.
    move: (filter_uniq (fun v => `|a - v| < d) (uniq_dec_roots (gcdp (pc p x) (pc q x)))).
    case rsdE: (seq.filter _ _) => [//|b rsd].
    case: rsd rsdE => [//|c rsd] rsdE /= /andP[] + _.
    rewrite in_cons negb_or => /andP[] /eqP + _.
    have: b \in [:: b, c & rsd] by exact/mem_head.
    have: c \in [:: b, c & rsd] by rewrite in_cons mem_head orbT.
    rewrite -rsdE !mem_filter !mem_dec_roots !root_gcd.
    move=> /andP[] wcd /andP[_] /andP[_] cx /andP[] wcb /andP[_] /andP[_] bx.
    elim; apply/dP.
    - rewrite mem_dec_roots pcM0//= root_bigmul.
      apply/hasP; exists q => //; apply/mem_index_enum.
    - rewrite mem_dec_roots pcM0//= root_bigmul.
      apply/hasP; exists q => //; apply/mem_index_enum.
    rewrite -(subrBB a) opprB -normrN opprD opprB.
    apply/(le_lt_trans (ler_normB _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD.
  rewrite big_seq_cond [X in (_ < X)%N]big_seq_cond.
  apply/ltn_sum => [a|].
    rewrite andbT mem_dec_roots root_gcd => /andP[_] /andP[] pa qa.
    rewrite -big_filter.
    have aP: a \in [fset x | x in dec_roots (pc p x)].
      by rewrite mem_imfset//= mem_dec_roots pc0.
    have aQ: a \in [fset x | x in dec_roots (pc q x)].
      by rewrite mem_imfset//= mem_dec_roots pc0.
    have: uniq [seq i <- dec_roots (gcdp (pc p y) (pc q y)) | normr (i - a) < d].
      exact/filter_uniq/uniq_dec_roots.
    have: all (fun b => b == val (fxy p [` aP]))
        [seq i <- dec_roots (gcdp (pc p y) (pc q y)) | (normr (i - a) < d)%R].
      apply/allP => b; rewrite mem_filter mem_dec_roots root_gcd.
      move=> /andP[] ba /andP[_] /andP[] pb _.
      have bP: b \in [fset x | x in dec_roots (pc p y)].
        by rewrite mem_imfset//= mem_dec_roots pc0.
      rewrite -[b]/(val [` bP]); apply/eqP; congr fsval.
      apply/(can_inj (fyxK p)); rewrite (fxyK p); apply/val_inj/dP.
      - move: (fsvalP (fyx p [` bP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
        rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pbx.
        apply/hasP; exists p => //; apply/mem_index_enum.
      - move: (fsvalP [` aP]); rewrite (mem_imfset _ _ (@inj_id _))/=.
        rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pax.
        apply/hasP; exists p => //; apply/mem_index_enum.
      rewrite -(subrBB b)/= opprB -normrN opprD opprB.
      apply/(le_lt_trans (ler_normB _ _)).
      by rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/fyxd.
    case: (seq.filter _ _) => /= [_ _|b + /andP[] /eqP ->].
      by rewrite big_nil.
    case=> /= [_ _|c l /andP[] /eqP -> _]; last by rewrite mem_head.
    rewrite big_seq1/=.
    have aE: a = val (gyx [` lift p y (fxy p [` aP]) ys]).
      by rewrite gyxE/= (fxyK p).
    rewrite [in X in (_ <= X)%N]aE mu_gyx/=; last first.
      move: (fsvalP (fxy p [` aP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      by rewrite mem_dec_roots => /andP[_].
    rewrite leq_min [ X in X && _]geq_minl/= geq_min; apply/orP; right.
    case/boolP: (root (pc q y) (val (fxy p [` aP]))) => [qfa|/muNroot -> //].
    by rewrite mu_gyx.
  have upE: u = gyx v.
    apply/val_inj/dP.
    - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))/=.
    - by move: (fsvalP (gyx v)); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite -(subrBB (val v)) opprB -normrN opprD opprB.
    apply/(le_lt_trans (ler_normB _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD; last exact/gyxd.
  have uqE: u = gyx w.
    apply/val_inj/dP.
    - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))/=.
    - by move: (fsvalP (gyx w)); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite -(subrBB (val w)) opprB.
    apply/(le_lt_trans (ler_normD _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD; last exact/gyxd.
  have pv': root (pc p y) (val v).
    move: pv; rewrite (mem_imfset _ _ (@inj_id _))/=.
    by rewrite mem_dec_roots => /andP[_].
  have qw': root (pc q y) (val w).
    move: qw; rewrite (mem_imfset _ _ (@inj_id _))/=.
    by rewrite mem_dec_roots => /andP[_].
  have pqu: \val u \in dec_roots (gcdp (pc p x) (pc q x)).
    rewrite mem_dec_roots gcdp_eq0 negb_and !pc0//= root_gcd.
    rewrite {1}upE gyx_root// uqE gyx_root//.
  apply/hasP; exists (val u) => //=.
  rewrite pqu/= -big_filter.
  suff ->: [seq i <- dec_roots (gcdp (pc p y) (pc q y))
      | (normr (i - fsval u) < d)%R] = [::].
    rewrite big_nil {1}upE uqE (mu_gyx p v pv') (mu_gyx q w qw') leq_min.
    by apply/andP; split; rewrite mu_gt0// pc0.
  apply/eqP/eq_mem_nil => a; rewrite in_nil mem_filter mem_dec_roots.
  rewrite gcdp_eq0 negb_and !pc0//= root_gcd.
  apply/negP => /andP[] au /andP[] pa qa.
  have aP: a \in [fset x | x in dec_roots (pc p y)].
    by rewrite mem_imfset//= mem_dec_roots pc0.
  have aQ: a \in [fset x | x in dec_roots (pc q y)].
    by rewrite mem_imfset//= mem_dec_roots pc0.
  apply/wv; transitivity a.
    rewrite -[a]/(val [` aQ]) -[LHS]/(val [` qw]); congr fsval.
    apply/(can_inj (fyxK q)); apply/val_inj/dP.
    - move: (fsvalP (fyx q [` qw])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pbx.
      apply/hasP; exists q => //; apply/mem_index_enum.
    - move: (fsvalP (fyx q [` aQ])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pax.
      apply/hasP; exists q => //; apply/mem_index_enum.
    rewrite -(subrBB a)/= opprB -normrN opprD opprB.
    apply/(le_lt_trans (ler_normB _ _)).
    rewrite mulr2n mulrDl mul1r; apply/ltrD; last exact/fyxd.
    rewrite -[X in _ - X]/(val [` lift q x (fyx q [` qw]) xs]) -gyxE/=.
    move: au; congr (`|_ - _| < d).
    by rewrite uqE; congr (val (gyx _)); apply/val_inj.
  rewrite -[a]/(val [` aP]) -[RHS]/(val [` pv]); congr fsval.
  apply/(can_inj (fyxK p)); apply/val_inj/dP.
  - move: (fsvalP (fyx p [` aP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pax.
    apply/hasP; exists p => //; apply/mem_index_enum.
  - move: (fsvalP (fyx p [` pv])); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite !mem_dec_roots pcM0//= root_bigmul => /andP[_] pbx.
    apply/hasP; exists p => //; apply/mem_index_enum.
  rewrite -(subrBB a)/= opprB -normrN opprD opprB.
  apply/(le_lt_trans (ler_normB _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/fyxd.
  rewrite -[X in _ - X]/(val [` lift p x (fyx p [` pv]) xs]) -gyxE/=.
  move: au; congr (`|_ - _| < d).
  by rewrite upE; congr (val (gyx _)); apply/val_inj.
have gR (u : [fset x | x in dec_roots (\prod_p pc p x)]) :
    (val u \is Num.real) = (val (gxy u) \is Num.real).
  have ucP z (v : [fset x | x in dec_roots (\prod_(p : P) pc p z)]) :
      z \in s ->
      ((val v)^* )%C \in [fset x | x in dec_roots (\prod_(p : P) pc p z)].
    move=> zs; move: (unlift z v) => [] p pv.
    rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots pcM0//= root_bigmul.
    apply/hasP; exists p; first exact/mem_index_enum.
    rewrite -complex_root_conj/= map_poly_id => [|a].
      move: pv; rewrite (mem_imfset _ _ (@inj_id _))/=.
      by rewrite mem_dec_roots => /andP[_].
    move=> /[dup] /(nth_index 0)/=.
    rewrite -index_mem size_map_poly => + alt.
    by rewrite coef_poly alt => <-; rewrite conjc_real.
  have ne20: 2 != 0 :> R[i] by rewrite pnatr_eq0.
  apply/idP/idP => uR.
    suff ->: \val (gxy u) = 'Re (\val (gxy u)) by apply/Creal_Re.
    apply/(mulfI ne20).
    rewrite -complexRe -addcJ mulr2n mulrDl mul1r; congr (_ + _)%R.
    rewrite -[RHS]/(val [` ucP y (gxy u) ys]); congr val.
    apply/(can_inj gyxK); rewrite gxyK; apply/val_inj/dP.
    - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _)).
    - move: (fsvalP (gyx [` ucP y (gxy u) ys])).
      by rewrite (mem_imfset _ _ (@inj_id _)).
    rewrite -(subrBB (val [` ucP y (gxy u) ys])) opprB.
    apply/(le_lt_trans (ler_normD _ _)).
    rewrite mulr2n mulrDl mul1r; apply/ltrD; last exact/gyxd.
    rewrite /= -(RRe_real uR) -conjc_real -rmorphB/= norm_conjC (RRe_real uR).
    exact/gxyd.
  suff ->: \val u = 'Re (\val u) by apply/Creal_Re.
  apply/(mulfI ne20).
  rewrite -complexRe -addcJ mulr2n mulrDl mul1r; congr (_ + _)%R.
  apply/dP.
  - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _)).
  - by move: (fsvalP ([` ucP x u xs])); rewrite (mem_imfset _ _ (@inj_id _)).
  rewrite -(subrBB (val (gxy u))).
  apply/(le_lt_trans (ler_normB _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/gxyd.
  rewrite /= -(RRe_real uR) -conjc_real -rmorphB/= norm_conjC (RRe_real uR).
  exact/gxyd.
split; last first; apply/eqP; rewrite rowPE forall_ord1.
  rewrite -!cE eqr_nat; apply/eqP.
  pose cs (z : 'rV[R]_n.+1) := dec_roots (map_poly (real_complex R) (evalpmp z (\prod_(p : P) val p))).
  have card_cs z: #|` [fset x in cs z]| = size (cs z).
    by rewrite /rs card_imfset//= undup_id// uniq_dec_roots.
  rewrite -(card_cs x) -(card_cs y).
  have /bij_eq_card: bijective gxy by exists gyx.
  by rewrite /cs /= !cardfE !evalpmp_prod !rmorph_prod.
rewrite -!rE eqr_nat -(card_rs x) -(card_rs y); apply/eqP.
have liftRP: forall z, z \in s ->
    forall (u : [fset x | x in rootsR (\prod_(p : P) (evalpmp z (val p)))]),
    exists (v : [fset x | x in dec_roots (\prod_p pc p z)]),
    val v = (val u)%:C%C.
  move=> z zs; case=> /= u; rewrite mem_imfset//= in_rootsR => /andP[_] pu.
  suff uP: u%:C%C \in [fset x0 | x0 in dec_roots (\prod_p pc p z)].
    by exists [` uP].
  rewrite (mem_imfset _ _ (@inj_id _))/= mem_dec_roots pcM0//=.
  by rewrite -rmorph_prod/= fmorph_root.
move: (fun z zs => fin_all_exists (liftRP z zs)) => {}liftRP.
case: (liftRP x xs) => liftxR liftxRE.
case: (liftRP y ys) => liftyR liftyRE {liftRP}.
have /fin_all_exists: forall (u : [fset x | x in rootsR (\prod_(p : P) (evalpmp x (val p)))]),
    exists (v : [fset x | x in rootsR (\prod_(p : P) (evalpmp y (val p)))]),
    (val v)%:C%C = val (gxy (liftxR u)).
  move=> u.
  have: val (liftxR u) \is Num.real.
    by apply/complex_realP; exists (val u); apply/liftxRE.
  rewrite gR => /Creal_ReP; rewrite -complexRe => uE.
  suff uP: complex.Re (val (gxy (liftxR u)))
      \in [fset x0 | x0 in rootsR (\prod_(p : P) evalpmp y (\val p))].
    by exists [` uP] => /=; apply/uE.
  rewrite (mem_imfset _ _ (@inj_id _))/= in_rootsR. 
  move: (fsvalP (gxy (liftxR u))).
  rewrite -uE (mem_imfset _ _ (@inj_id _))/= mem_dec_roots. 
  by rewrite -{1 2}rmorph_prod/= fmorph_root map_poly_eq0.
move=> [] hxy hxyE.
have /fin_all_exists: forall (u : [fset x | x in rootsR (\prod_(p : P) (evalpmp y (val p)))]),
    exists (v : [fset x | x in rootsR (\prod_(p : P) (evalpmp x (val p)))]),
    (val v)%:C%C = val (gyx (liftyR u)).
  move=> u.
  have: val (liftyR u) \is Num.real.
    by apply/complex_realP; exists (val u); apply/liftyRE.
  rewrite -{1}[liftyR u]gyxK -gR => /Creal_ReP; rewrite -complexRe => uE.
  suff uP: complex.Re (val (gyx (liftyR u)))
      \in [fset x0 | x0 in rootsR (\prod_(p : P) evalpmp x (\val p))].
    by exists [` uP] => /=; apply/uE.
  rewrite (mem_imfset _ _ (@inj_id _))/= in_rootsR. 
  move: (fsvalP (gyx (liftyR u))).
  rewrite -uE (mem_imfset _ _ (@inj_id _))/= mem_dec_roots. 
  by rewrite -{1 2}rmorph_prod/= fmorph_root map_poly_eq0.
move=> [] hyx hyxE.
suff /bij_eq_card: bijective hxy by rewrite /rs /= !evalpmp_prod !cardfE.
exists hyx => u; apply/val_inj/complexI.
  rewrite hyxE.
  have ->: liftyR (hxy u) = gxy (liftxR u).
    by apply/val_inj; rewrite liftyRE hxyE.
  by rewrite gxyK liftxRE.
rewrite hxyE.
have ->: liftxR (hyx u) = gyx (liftyR u).
  by apply/val_inj; rewrite liftxRE hyxE.
by rewrite gyxK liftyRE.
Qed. *)
admit.
Admitted.

Definition elimp_subdef1 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : P) truncations (muni (val p)).

Definition elimp_subdef2 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P | (3 <= size (val p))%N)
      [fset subresultant (val j) (val p) (val p)^`() | j : 'I_(size (val p)).-2].

Definition elimp_subdef3 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P)
    \big[fsetU/fset0]_(q : elimp_subdef1 P | (size (val q) <= size (val p))%N)
      [fset subresultant (val j) (val p) (val q) | j : 'I_(size (val q)).-1].

(* Is that an optimization?
Definition elimp_subdef4 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P)
    \big[fsetU/fset0]_(q : elimp_subdef1 P | (size (val q) == size (val p))%N)
      let q := lead_coef (val p) *: (val q) - lead_coef (val q) *: (val p) in
      [fset subresultant (val j) (val p) (val q)  | j : 'I_(size (val q)).-1].
 *)

Definition elimp_subdef5 n (P : {fset {mpoly R[n.+1]}}) :=
  [fset lead_coef (val p) | p : elimp_subdef1 P].

Definition elimp n (P : {fset {mpoly R[n.+1]}}) :=
  [fset p in elimp_subdef2 P `|` elimp_subdef3 P (* `|` elimp_subdef4 P *) `|` elimp_subdef5 P | (1 < msize (val p))%N].

Lemma map_poly_truncate (A B : ringType) (f : {rmorphism A -> B}) d (p : {poly A}) :
  map_poly f (truncate p d) = truncate (map_poly f p) d.
Proof.
apply/polyP => i.
rewrite coef_map !coef_poly [LHS]fun_if [in RHS]ltn_min andbC.
case: (ltnP i (size (map_poly f p))) => ifp /=.
  by rewrite -if_and ltn_min rmorph0.
case: ifP => _; last exact/rmorph0.
rewrite -coef_map.
by move/leq_sizeP: ifp; apply.
Qed.

Lemma mx_continuous (T : topologicalType) (K : realFieldType) m n (f : T -> 'M[K]_(m.+1, n.+1)) :
  (forall i j, continuous (fun x => f x i j)) ->
  continuous f.
Proof.
move=> fc x; apply/cvg_ballP => e e0.
near=> y.
rewrite -[X in X (f x)]ball_normE/= [X in X < _]mx_normrE bigmax_lt//= => -[] i j _.
rewrite !mxE/=.
suff: ball (f x i j) e (f y i j).
  by rewrite -(@ball_normE _ (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod K)).
move: i j.
near: y.
apply: filter_forall => i.
apply: filter_forall => j.
move: (fc i j x) => /cvg_ballP-/(_ e e0).
exact/filterS.
Unshelve. all: end_near.
Qed.

Lemma subseq_drop_index (T : eqType) (x : T) (s1 s2 : seq T) :
  subseq (x :: s1) s2 = subseq (x :: s1) (drop (index x s2) s2).
Proof.
move nE: (index _ _) => n.
elim: n s2 nE => [|n IHn] s2 nE; first by rewrite drop0.
case: s2 nE => [//|y s2].
have [->|/negPf /=] := eqVneq y x; first by rewrite /= eqxx.
by rewrite eq_sym => -> /succn_inj; apply/IHn.
Qed.

Lemma index_iota n m i :
  index i (iota n m) = if (i < n)%N then m else minn (i - n)%N m.
Proof.
elim: m i n => /= [|m IHm] i n; first by rewrite minn0 if_same.
have [->|/negPf ni] := eqVneq n i; first by rewrite ltnn subnn min0n.
rewrite IHm ltnS leq_eqVlt eq_sym ni/=.
case: (ltnP i n) => [//|] ni'.
by rewrite -minnSS subnS prednK// subn_gt0 ltn_neqAle ni.
Qed.

Lemma subseq_nth_iota (T : eqType) (x : T) (s1 s2 : seq T) :
  reflect (exists t, subseq t (iota 0 (size s2)) /\ s1 = [seq nth x s2 i | i <- t])
      (subseq s1 s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs1] s2/=.
  rewrite sub0seq; apply/Bool.ReflectT.
  by exists [::]; split=> //; apply/sub0seq.
apply/(iffP idP) => [|[]].
  move=> /[dup] /mem_subseq/(_ x1 (mem_head _ _)) x12.
  rewrite subseq_drop_index drop_index//= eqxx => /IHs1[/=] t [].
  rewrite size_drop => tsub ->.
  exists ((index x1 s2) :: [seq (index x1 s2).+1 + i | i <- t]); split=> /=.
    rewrite -[size s2](@subnKC (index x1 s2).+1) ?index_mem// -cat1s iotaD.
    apply/cat_subseq; first by rewrite sub1seq mem_iota/=.
    by rewrite iotaE0; apply/map_subseq.
  rewrite nth_index//; congr cons.
  rewrite -map_comp; apply/eq_map => k.
  by rewrite nth_drop/=.
case=> [[] //|i t] [] /[dup] /mem_subseq/(_ i (mem_head _ _)).
rewrite mem_iota/= => /[dup] ilt /ltnW/minn_idPl is2.
rewrite [subseq (i :: t) _]subseq_drop_index index_iota/= subn0.
rewrite is2 drop_iota.
case jE: (size s2 - i)%N => [//|j] /=.
rewrite eqxx => tsub [] -> s12.
rewrite -[s2](cat_take_drop i) nth_cat size_take is2 ltnn subnn.
apply/(subseq_trans _ (suffix_subseq _ _)).
case s2E: (drop i s2) => /= [|y s3].
  by move: ilt; rewrite -[s2](cat_take_drop i) s2E cats0 size_take is2 ltnn.
rewrite eqxx; apply/IHs1; exists [seq (j - i.+1)%N | j <- t].
move: jE; rewrite -size_drop s2E/= => /succn_inj jE.
rewrite jE; split.
move: tsub; rewrite iotaE0 => /(map_subseq (fun x => x - i.+1)%N).
congr subseq; rewrite -map_comp -[RHS]map_id; apply/eq_map => k /=.
  by rewrite subDnCA// subnn addn0.
rewrite s12 -map_comp; apply/eq_in_map => k /= /(mem_subseq tsub).
rewrite mem_iota => /andP[] ik _.
rewrite -[s2](cat_take_drop i) nth_cat size_take is2 ltnNge (ltnW ik)/=.
by rewrite s2E -[(k - i)%N]prednK ?subn_gt0//= subnS.
Qed.

Lemma muniK (n : nat) (A : ringType) : cancel (@muni n A) (@mmulti n A).
Proof.
move=> p.
apply/mpolyP => m.
rewrite raddf_sum/=.
under eq_bigr => i _.
  have ->: (mwiden (muni p)`_i * 'X_ord_max ^+ i)@_m = (mwiden (muni p)`_i * 'X_ord_max ^+ i)@_m *+ (val i == m ord_max).
    have [_|im] := eqVneq (val i) (m ord_max); first by rewrite mulr1n.
  rewrite mulr0n mcoeffM.
  under eq_bigr => /= j mE.
    have ->: (mwiden (muni p)`_i)@_(j.1)%PAIR * ('X_ord_max ^+ i)@_(j.2)%PAIR = 0.
      move: mE => /eqP /(congr1 (fun x : 'X_{1.. n.+1} => x ord_max)).
      rewrite mnmE mcoeffXn => mE.
      case/boolP: (_ == _) => /eqP j2; last by rewrite mulr0.
      rewrite mulr1.
      move: mE; rewrite -j2 mulmnE mnmE eqxx mul1n => mE.
      rewrite (mwidenE (leqnn _)) raddf_sum/=.
      under eq_bigr => k _.
        rewrite mcoeffZ mcoeffX.
        have /negPf ->: mnmwiden k != (j.1)%PAIR.
          apply/eqP => /(congr1 (fun x : 'X_{1.. n.+1} => x ord_max)).
          rewrite mnmwiden_ordmax => j1.
          by rewrite mE -j1 eqxx in im.
        rewrite mulr0.
        over.
      by rewrite big_const_idem//= addr0.
      over.
    by rewrite big_const_idem//= addr0.
  rewrite mulrb.
  over.
rewrite -big_mkcond/=.
case: (ltnP (m ord_max) (size (muni p))) => mlt; last first.
  under eq_bigl => i.
    have /negPf ->: i != m ord_max :> nat.
      apply/eqP => iE.
      by move: (ltn_ord i); rewrite iE ltnNge mlt.
    over.
  rewrite big_pred0_eq.
  apply/esym/eqP; rewrite mcoeff_eq0.
  Search Measure.type.
  Check (@mmeasure_mnm_ge _ _ (fun m : 'X_{1.. n.+1} => m ord_max)).
  Search msupp.
  
  

Search bigop "0".
  under eq_bigr => i iE.
    
  Check big_pred0.
rewrite (big_pred1 (m ord_max)).
Search bigop pred1.


Theorem cylindrical_decomposition n (P : {fset {mpoly R[n]}}) :
  { S | isCD S /\ forall p : P, poly_adapted (val p) S}.
Proof.
elim: n P => [|n IHn] P.
  exists [fset SAsetT R 0]; split=> [|[] p /= _]; last first.
    case=> _ /= /fset1P -> x y _ _.
    suff ->: x = y by [].
    by apply/matrixP => i; case.
  split=> [|//].
  apply/andP; split; last by rewrite big_fset1/= eqxx.
  apply/andP; split.
    apply/negP; move=> /fset1P/eqP/SAsetP /(_ (\row_i 0)%R).
    by rewrite inSAset0 inSAsetT.
  do 2 (apply/forallP; case => i /= /fset1P -> {i}).
  by rewrite eqxx.
move: IHn => /(_ (elimp P)) [S'][S'CD] S'p.
have S'part : SAset_partition S' by case: (n) S' S'CD {S'p} => [|m] S' [].
have pick (s' : S') : {x | x \in val s'}.
  case: (set0Vmem (val s')) => [s'0|//].
  move: S'part => /andP[] /andP[] /negP S'0 _ _.
  by exfalso; apply/S'0; rewrite -s'0 -in_fsub fsubT finset.in_setT.
have nth_const (s' : S') (p : P) x y :
    x \in val s' -> y \in val s' ->
    forall i, ((size (evalpmp x (muni (val p)))).-1 <= i)%N ->
      sgz (evalpmp x (muni (val p)))`_i = sgz (evalpmp y (muni (val p)))`_i.
  move=> xs ys i xi.
  have iE: forall z, (evalpmp z (muni (\val p)))`_i = (truncate (evalpmp z (muni (\val p))) i.+1)`_i.
    move=> z; rewrite [RHS]coef_poly ltn_min leqnn/=.
    case: ifP => [//|] /negP/negP; rewrite -leqNgt => {}zi.
    by rewrite nth_default.
  rewrite !iE -!map_poly_truncate/= !coef_map/=.
  case: (ltnP 1 (msize ((truncate (muni (val p)) i.+1)`_i))) => [pi1|]; last first.
    by move=> /msize1_polyC ->; rewrite !mevalC.
  move: xi; rewrite -ltnS => /(leq_trans (leqSpred _)) xi.
  suff iP: (truncate (muni (fsval p)) i.+1)`_i \in elimp P.
    exact: (S'p [` iP] s' x y xs ys).
  have si: size (truncate (muni (val p)) i.+1) = i.+1.
    apply/anti_leq/andP; split.
      exact/(leq_trans (size_poly _ _))/geq_minl.
    by apply/gt_size/eqP => pi0; rewrite pi0 msize0 in pi1.
  rewrite inE/= inE/=; apply/andP; split=> //.
  rewrite in_fsetU; apply/orP; right.
  move: si => /(congr1 predn); rewrite succnK => si.
  rewrite -[X in _`_X]si -lead_coefE.
  suff iP: truncate (muni (fsval p)) i.+1 \in elimp_subdef1 P.
    by apply/imfsetP; exists [` iP].
  apply/bigfcupP; exists p; first by rewrite mem_index_enum.
  exact/(truncations_witness xi).
have S'size (s' : S') (p : P) :
    {in val s', forall x, size (evalpmp x (muni (val p))) = size (evalpmp (proj1_sig (pick s')) (muni (val p)))}.
  suff: {in val s' &, forall x y, (size (evalpmp x (muni (val p))) <= size (evalpmp y (muni (val p))))%N}.
    move=> S'size x xS; apply/anti_leq/andP.
    split; apply/S'size => //; exact/(proj2_sig (pick s')).
  move=> x y xs ys; apply/leq_sizeP => i yi.
  apply/eqP; rewrite -sgz_eq0 -(nth_const s' p y x ys xs).
    by rewrite sgz_eq0 nth_default.
  exact/(leq_trans (leq_pred _) yi).
have R0: [char R] =i pred0 by apply/char_num.
have Rn_char: [char mpoly_mpoly__canonical__GRing_IntegralDomain n R] =i pred0.
  move=> a; rewrite !inE; apply/negP => /andP[] /prime_gt0.
  by rewrite -mpolyC_nat mpolyC_eq0 pnatr_eq0 lt0n => /negP.
have res_const (s' : S') (p q : P) (x y : 'rV_n):
    x \in \val s' ->
    y \in \val s' ->
    forall i,
    (i <= (size (evalpmp (val (pick s')) (muni (val p)))).-1)%N ->
    (i <= (size (evalpmp (val (pick s')) (muni (val q)))).-1)%N ->
      sgz (subresultant i (evalpmp x (muni (\val p))) (evalpmp x (muni (\val q)))) =
      sgz (subresultant i (evalpmp y (muni (\val p))) (evalpmp y (muni (\val q)))).
  move=> xs ys i; rewrite {1}leq_eqVlt => /orP[/eqP -> _|ip].
    rewrite -{1}(S'size s' p x xs) -(S'size s' p y ys).
    rewrite !subresultant_last !sgzX; congr (_ ^+ (_.-1 - _.-1)); last first.
    - by rewrite (S'size s' p x xs) (S'size s' p y ys).
    - by rewrite (S'size s' q x xs) (S'size s' q y ys).
    rewrite !lead_coefE (S'size s' p y ys) -(S'size s' p x xs).
    by apply/(nth_const s'); last exact/leqnn.
  rewrite leq_eqVlt => /orP[/eqP ->|iq].
    rewrite subresultantC [in RHS]subresultantC sgzM [in RHS]sgzM.
    congr (_ * _).
      congr (sgz ((-1) ^+ _)); congr 'C(_, 2).
      congr ((_.-1 - _) + (_.-1 - _))%N.
        by rewrite (S'size s' p x xs) (S'size s' p y ys).
      by rewrite (S'size s' q x xs) (S'size s' q y ys).
    rewrite -{1}(S'size s' q x xs) -(S'size s' q y ys).
    rewrite !subresultant_last !sgzX; congr (_ ^+ (_.-1 - _.-1)); last first.
    - by rewrite (S'size s' q x xs) (S'size s' q y ys).
    - by rewrite (S'size s' p x xs) (S'size s' p y ys).
    rewrite !lead_coefE (S'size s' q y ys) -(S'size s' q x xs).
    by apply/(nth_const s'); last exact/leqnn. 
  pose Q (r : P) := truncate (muni (\val r)) (size (evalpmp (val (pick s')) (muni (\val r)))).
  wlog: p q ip iq / (size (Q q) <= size (Q p))%N => qp.
    move/orP: (leq_total (size (Q q)) (size (Q p))).
    case=> [/(qp p q ip iq)//|] /(qp q p iq ip) {}qp.
    rewrite subresultantC [in RHS]subresultantC sgzM [in RHS]sgzM.
    congr (_ * _); last exact: qp.
    congr (sgz ((-1) ^+ _)); congr 'C(_, 2).
    congr ((_.-1 - _) + (_.-1 - _))%N.
      by rewrite (S'size s' p x xs) (S'size s' p y ys).
    by rewrite (S'size s' q x xs) (S'size s' q y ys).
  have QE r z : z \in val s' -> (evalpmp z (muni (val r))) = evalpmp z (Q r).
    move=> zs.
    by rewrite [RHS]map_poly_truncate/= -(S'size s' r z zs) truncate_size.
  have Qsize r z : z \in val s' -> size (evalpmp z (Q r)) = size (Q r).
    move=> zs; rewrite -(QE r z zs) (S'size s' r z zs).
    apply/le_anti/andP; split; last first.
      exact/(leq_trans (size_poly _ _))/geq_minl.
    case: (posnP (size (evalpmp (sval (pick s')) (muni (\val r))))).
      by move=> ->; apply/leq0n.
    move=> s0; rewrite -(prednK s0); apply/gt_size.
    rewrite coef_poly (prednK s0) leq_min leqnn/= size_poly.
    apply/eqP => r0.
    have/eqP {}r0 : evalpmp (sval (pick s')) (muni (fsval r)) == 0.
      by rewrite -lead_coef_eq0 lead_coefE coef_map/= r0 meval0.
    by move: s0; rewrite r0 size_poly0 ltnn.
  (* N.B. Why does Coq stop responding if I do not give the location? *)
  rewrite [X in subresultant i X](QE p x xs) [X in _ = sgz (subresultant i X _)](QE p y ys).
  rewrite [X in subresultant i _ X](QE q x xs) [X in _ = sgz (subresultant i _ X)](QE q y ys).
  have Q0 (r : P) z : z \in val s' ->
      (i < (size (evalpmp (\val (pick s')) (muni (\val r)))).-1)%N ->
      (lead_coef (Q r)).@[tnth (ngraph z)] != 0.
    move=> zs ir.
    rewrite lead_coefE -coef_map -(Qsize r z zs) -lead_coefE lead_coef_eq0.
    rewrite -size_poly_eq0 (Qsize r z zs) -(Qsize r _ (proj2_sig (pick s'))) -(QE _ _ (proj2_sig (pick s'))).
    by apply/eqP => s0; rewrite s0 in ir.
  rewrite !subresultant_map_poly/=; first last.
  - exact/Q0.
  - exact/Q0.
  - exact/Q0.
  - exact/Q0.
  case: (ltnP 1 (msize (subresultant i (Q p) (Q q)))) => [pq1|]; last first.
    by move=> /msize1_polyC ->; rewrite !mevalC.
  suff pqP: subresultant i (Q p) (Q q) \in elimp P.
    exact: (S'p [` pqP] s' x y xs ys).
  rewrite inE/= inE; apply/andP; split=> //.
  rewrite 2!inE orbAC; apply/orP; right.
  have pP: Q p \in elimp_subdef1 P.
    apply/bigfcupP; exists p; first by rewrite mem_index_enum.
    exact/truncations_witness.
  apply/bigfcupP; exists [` pP]; first by rewrite mem_index_enum/=.
  have qP: Q q \in elimp_subdef1 P.
    apply/bigfcupP; exists q; first by rewrite mem_index_enum.
    exact/truncations_witness.
  apply/bigfcupP; exists [` qP]; first by rewrite mem_index_enum/=.
  move: iq; rewrite -(S'size s' q x xs) (QE q x xs) (Qsize q x xs) => iq.
  by apply/imfsetP => /=; exists (Ordinal iq).
have res'_const (s' : S') (p : P) (x y : 'rV_n):
    x \in \val s' ->
    y \in \val s' ->
    forall i,
    (i <= (size (evalpmp (val (pick s')) (muni (val p)))).-2)%N ->
      sgz (subresultant i (evalpmp x (muni (\val p))) (evalpmp x (muni (\val p)))^`()) =
      sgz (subresultant i (evalpmp y (muni (\val p))) (evalpmp y (muni (\val p)))^`()).
  move=> xs ys i.
  rewrite leq_eqVlt => /orP[/eqP ->|ilt].
    rewrite -{1}(S'size s' p x xs) -(S'size s' p y ys) -(size_deriv _ R0).
    rewrite -[in RHS](size_deriv _ R0).
    rewrite subresultantC subresultant_last (size_deriv _ R0) (S'size s' p x xs).
    rewrite subresultantC subresultant_last (size_deriv _ R0) (S'size s' p y ys).
    rewrite !sgzM; congr (_ * _).
    case: (_.-1) => [|j]; first by rewrite !expr0.
    rewrite succnK subSn; last by [].
    rewrite subnn !expr1 !(lead_coef_deriv _ R0).
    rewrite -mulr_natr -[in RHS]mulr_natr !lead_coefE !sgzM.
    rewrite (S'size s' p y ys) -(S'size s' p x xs); congr (_ * _).
    exact/(nth_const s').
  set q := truncate (muni (\val p)) (size (evalpmp (val (pick s')) (muni (\val p)))).
  rewrite -!/(evalpmp _ _).
  have qE z : z \in val s' -> (evalpmp z (muni (val p))) = evalpmp z q.
    move=> zs.
    by rewrite [RHS]map_poly_truncate/= -(S'size s' p z zs) truncate_size.
  have qsize z : z \in val s' -> size (evalpmp z q) = size q.
    move=> zs; rewrite -(qE z zs) (S'size s' p z zs).
    apply/le_anti/andP; split; last first.
      exact/(leq_trans (size_poly _ _))/geq_minl.
    case: (posnP (size (evalpmp (sval (pick s')) (muni (\val p))))) => [-> //|].
    move=> s0; rewrite -(prednK s0); apply/gt_size.
    rewrite coef_poly (prednK s0) leq_min leqnn/= size_poly.
    apply/eqP => p0.
    have/eqP {}p0 : evalpmp (sval (pick s')) (muni (fsval p)) == 0.
      by rewrite -lead_coef_eq0 lead_coefE coef_map/= p0 meval0.
    by move: s0; rewrite p0 size_poly0 ltnn.
  rewrite (qE x xs) (qE y ys).
  have iq: (i < (size q).-2)%N.
    apply/(leq_trans ilt); rewrite (qE _ (proj2_sig (pick s'))).
    exact/leq_predn/leq_predn/size_poly.
  have sq: (2 < size q)%N by rewrite -2!ltn_predRL (leq_trans _ iq).
  have q0 z : z \in val s' -> (lead_coef q).@[tnth (ngraph z)] != 0.
    move=> zs; rewrite lead_coefE -coef_map.
    rewrite -(qsize z zs) -lead_coefE lead_coef_eq0 -size_poly_eq0 qsize//.
    by rewrite -leqn0 leqNgt (leq_trans _ sq).
  rewrite !deriv_map !subresultant_map_poly/=; first last.
  - rewrite lead_coef_deriv// mevalMn mulrn_eq0 -leqn0 leqNgt ltn_predRL.
    by rewrite (leq_trans (leqnSn _) sq)/= q0.
  - exact/q0.
  - rewrite lead_coef_deriv// mevalMn mulrn_eq0 -leqn0 leqNgt ltn_predRL.
    by rewrite (leq_trans (leqnSn _) sq)/= q0.
  - exact/q0.
  case: (ltnP 1 (msize (subresultant i q q^`()))) => [q1|]; last first.
    by move=>/msize1_polyC ->; rewrite !mevalC.
  suff qP: (subresultant i q q^`()) \in elimp P.
    by move: (S'p [` qP] s' x _ xs ys) => /=.
  rewrite inE/= inE; apply/andP; split=> //.
  rewrite 2!inE -orbA; apply/orP; left.
  have qP: q \in elimp_subdef1 P.
    apply/bigfcupP; exists p; first by rewrite mem_index_enum.
    exact/truncations_witness.
  apply/bigfcupP; exists [` qP]; first by rewrite mem_index_enum/=.
  by apply/imfsetP => /=; exists (Ordinal iq).
have S'constR (s' : S') (p : P) :
    {in val s', forall x, size (rootsR (evalpmp x (muni (val p)))) = size (rootsR (evalpmp (proj1_sig (pick s')) (muni (val p))))}.
  move=> x xs; move: (proj2_sig (pick s')); set x' := proj1_sig (pick s') => x's.
  have [p0|x'0] := eqVneq (evalpmp x' (muni (val p))) 0.
    rewrite p0; suff ->: evalpmp x (muni (val p)) = 0 by [].
    by apply/eqP; rewrite -size_poly_eq0 (S'size s')// size_poly_eq0; apply/eqP.
  have x0: (evalpmp x (muni (val p))) != 0.
    by rewrite -size_poly_eq0 (S'size s')// size_poly_eq0.
  apply/eqP; rewrite -eqz_nat -!cindexR_derivp; apply/eqP.
  rewrite -!pmv_subresultant; first last.
  - exact/lt_size_deriv.
  - exact/lt_size_deriv.
  rewrite !polyorder.size_deriv !(S'size s' p x xs).
  apply/PMV.eq_pmv; rewrite all2E !size_cat !size_map eqxx/=.
  rewrite zip_cat ?size_map// !zip_map all_cat !all_map !all_rev.
  apply/andP; split; apply/allP => i; rewrite mem_iota => /=.
    move=> _; apply/eqP; rewrite -mulr_natr -[in RHS]mulr_natr.
    rewrite !sgzM (S'size s' p)//; congr (_ * _).
    rewrite !lead_coefE (S'size s' p x' x's) -(S'size s' p x xs).
    exact/(nth_const s').
  rewrite add0n => /leq_predn; rewrite succnK => ilt; apply/eqP.
  exact/(res'_const s').
pose P' (s : S') := [fset muni (val p) | p : P & evalpmp (val (pick s)) (muni (val p)) != 0].
have size_gcd_const (s' : S') : {in P' s',
  forall p : {poly {mpoly R[n]}},
  {in \val s' &,
    forall x y : 'rV_n,
    size (gcdp (evalpmp x p) (evalpmp x p)^`()) =
    size (gcdp (evalpmp y p) (evalpmp y p)^`())}}.
  move=> q /imfsetP[/=] p _ -> {q} x y xs ys.
  have [px0|px0] := eqVneq (evalpmp x (muni (val p)))^`() 0.
    rewrite px0; move/eqP: px0.
    rewrite -size_poly_eq0 (size_deriv _ R0) (S'size s' p x xs) -(S'size s' p y ys) -(size_deriv _ R0) size_poly_eq0 => /eqP ->.
    by rewrite !gcdp0 (S'size s' p x xs) (S'size s' p y ys).
  move: (px0); rewrite -size_poly_eq0 (size_deriv _ R0) (S'size s' p x xs) -(S'size s' p y ys) -(size_deriv _ R0) size_poly_eq0 => py0.
  rewrite -[LHS]prednK; last first.
    rewrite ltnNge leqn0 size_poly_eq0 gcdp_eq0; apply/andP => -[_ p0].
    by rewrite p0 in px0.
  rewrite -[RHS]prednK; last first.
    rewrite ltnNge leqn0 size_poly_eq0 gcdp_eq0; apply/andP => -[_ p0].
    by rewrite p0 in py0.
  apply/esym/eqP; rewrite eqSS.
  move: (eqxx (size (gcdp (evalpmp x (muni (val p))) (evalpmp x (muni (val p)))^`())).-1).
  rewrite gcdp_subresultant; first last.
  - apply/leq_predn/leq_gcdpr/negP => p0.
    by rewrite p0 in px0.
  - apply/leq_predn/leq_gcdpl/eqP => p0.
    by rewrite p0 deriv0 eqxx in px0.
  - by [].
  - by apply/eqP => p0; rewrite p0 deriv0 eqxx in px0. 
  rewrite gcdp_subresultant; first last.
  - rewrite (size_deriv _ R0) (S'size s' p y ys) -(S'size s' p x xs) -[X in (_ <= X.-1)%N](size_deriv _ R0).
    apply/leq_predn/leq_gcdpr/negP => p0.
    by rewrite p0 in px0.
  - rewrite (S'size s' p y ys) -(S'size s' p x xs).
    apply/leq_predn/leq_gcdpl/eqP => p0.
    by rewrite p0 deriv0 eqxx in px0.
  - by rewrite -size_poly_eq0 (size_deriv _ R0) (S'size s' p y ys) -(S'size s' p x xs) -(size_deriv _ R0) size_poly_eq0.
  - rewrite -size_poly_eq0 (S'size s' p y ys) -(S'size s' p x xs) size_poly_eq0.
    by apply/eqP => p0; rewrite p0 deriv0 eqxx in px0. 
  move=> /andP[] /forallP si sl; apply/andP; split.
    apply/forallP => /= i.
    rewrite -sgz_eq0 (res'_const s' p y x ys xs).
      by rewrite sgz_eq0; apply/si.
    rewrite -[_ i]succnK; apply/leq_predn/(leq_trans (ltn_ord i))/leq_predn.
    rewrite -(S'size s' p x xs); apply/leq_gcdpl/eqP => px0'.
    by rewrite px0' deriv0 eqxx in px0.
  rewrite -sgz_eq0 (res'_const s' p y x ys xs) ?sgz_eq0//.
  apply/leq_predn; rewrite -(S'size s' p x xs) -(size_deriv _ R0).
  exact/leq_gcdpr.
have S'con (s' : S') : SAconnected (val s').
  admit. (* s' connected *)
have size_gcdpq_const (s' : S') : {in P' s' &,
  forall p q : {poly {mpoly R[n]}},
  {in \val s' &,
    forall x y : 'rV_n,
    size (gcdp (evalpmp x p) (evalpmp x q)) =
    size (gcdp (evalpmp y p) (evalpmp y q))}}.
  move=> q r /imfsetP[/=] p _ -> {q} /imfsetP[/=] q _ -> {r} x y xs ys.
  have [p0|/negP p0] := eqVneq (evalpmp x (muni (val p))) 0.
    rewrite {1}p0; move/eqP: p0.
    rewrite -size_poly_eq0 (S'size s' p x xs) -(S'size s' p y ys) size_poly_eq0 => /eqP {1}->.
    by rewrite !gcd0p (S'size s' q x xs) (S'size s' q y ys).
  have [q0|/negP q0] := eqVneq (evalpmp x (muni (val q))) 0.
    rewrite [X in gcdp _ X]q0; move/eqP: q0.
    rewrite -size_poly_eq0 (S'size s' q x xs) -(S'size s' q y ys) size_poly_eq0 => /eqP {}q0.
    rewrite [X in _ = (size (gcdp _ X))]q0.
    by rewrite !gcdp0 (S'size s' p x xs) (S'size s' p y ys).
  rewrite -[LHS]prednK; last first.
    by rewrite ltnNge leqn0 size_poly_eq0 gcdp_eq0; apply/andP => -[_].
  rewrite -[RHS]prednK; last first.
    rewrite ltnNge leqn0 size_poly_eq0 gcdp_eq0; apply/andP => -[_].
    by rewrite -size_poly_eq0 (S'size s' q y ys) -(S'size s' q x xs) size_poly_eq0.
  apply/esym/eqP; rewrite eqSS.
  move: (eqxx (size (gcdp (evalpmp x (muni (val p))) (evalpmp x (muni (val q))))).-1).
  rewrite gcdp_subresultant; first last.
  - exact/leq_predn/leq_gcdpr/negP.
  - exact/leq_predn/leq_gcdpl/negP/p0.
  - exact/negP.
  - exact/negP/p0.
rewrite gcdp_subresultant; first last.
  - rewrite (S'size s' q y ys) -(S'size s' q x xs).
    by apply/leq_predn/leq_gcdpr/negP.
  - rewrite (S'size s' p y ys) -(S'size s' p x xs).
    exact/leq_predn/leq_gcdpl/negP/p0.
  - by rewrite -size_poly_eq0 (S'size s' q y ys) -(S'size s' q x xs) size_poly_eq0; apply/negP.
  - by rewrite -size_poly_eq0 (S'size s' p y ys) -(S'size s' p x xs) size_poly_eq0; apply/negP/p0.
  congr (_ && _).
    apply/eq_forallb => /= i.
    rewrite -sgz_eq0 -[RHS]sgz_eq0 (res_const s' p q x y xs ys)//.
      rewrite -[_ i]succnK -(S'size s' p x xs).
      exact/leq_predn/(leq_trans (ltn_ord i))/(leq_trans (leq_pred _))/leq_gcdpl/negP/p0.
    rewrite -[_ i]succnK -(S'size s' q x xs).
    exact/leq_predn/(leq_trans (ltn_ord i))/(leq_trans (leq_pred _))/leq_gcdpr/negP.
  rewrite -sgz_eq0 -[in RHS]sgz_eq0 (res_const s' p q x y xs ys)//.
    by apply/leq_predn; rewrite -(S'size s' p x xs); apply/leq_gcdpl/negP/p0.
  by apply/leq_predn; rewrite -(S'size s' q x xs); apply/leq_gcdpr/negP.
have S'const (s' : S') :
     {in \val s',
       forall x : 'rV_n,
       size (rootsR (evalpmp x (\prod_(p : P' s') (val p)))) =
       size (rootsR (evalpmp (sval (pick s')) (\prod_(p : P' s') (val p))))}.
  case: (@evalpmp_prod_const _ (P' s') (val s')).
  - exact/S'con.
  - move=> q /imfsetP[/=] p _ -> {q} x y xs ys.
    by rewrite !(S'size s').
  - exact/size_gcd_const.
  - exact/size_gcdpq_const.
  - move=> _ rc x xs; exact/(rc x _ xs (proj2_sig (pick s'))).
have size_gcdpm_const (s' : S') :
     {in \val s',
       forall x : 'rV_n,
       size (gcdp (evalpmp x (\prod_(p : P' s') \val p)) (evalpmp x (\prod_(p : P' s') \val p))^`()) =
       size (gcdp (evalpmp (val (pick s')) (\prod_(p : P' s') \val p)) (evalpmp (val (pick s')) (\prod_(p : P' s') \val p))^`())}.
  case: (@evalpmp_prod_const _ (P' s') (val s')).
  - exact/S'con.
  - move=> q /imfsetP[/=] p _ -> {q} x y xs ys.
    by rewrite !(S'size s').
  - exact/size_gcd_const.
  - exact/size_gcdpq_const.
  - move=> cc _ x xs; exact/(cc x _ xs (proj2_sig (pick s'))).
pose S := [fset SAset_cast n.+1 s' | s' in \big[fsetU/fset0]_(s' : S') partition_of_graphs_above (val s') (proj1_sig (roots2_on (S'const s')))].
have {}Scast : [fset SAset_cast n s | s in S] = S'.
  rewrite /S 2!imfset_bigfcup.
  apply/fsetP => x; apply/bigfcupP/idP => [[] /= s _| xS].
    case: (roots2_on (S'const s)) => /= r [] rsort _.
    move=> /imfsetP[] /= y /imfsetP[] /= z zs -> ->.
    rewrite SAset_cast_trans; last by rewrite geq_min addn1 leqnn.
    by rewrite (SAset_cast_partition_of_graphs_above rsort zs).
  exists [` xS]; first by rewrite mem_index_enum.
  apply/imfsetP => /=.
  case: (roots2_on (S'const [` xS])) => /= r [] rsort _.
  exists (SAset_cast n.+1 ((nth (SAset0 R _) (partition_of_graphs r) 0) :&: (x :*: SAsetT R 1))).
    apply/imfsetP; exists ((nth (SAset0 R _) (partition_of_graphs r) 0) :&: (x :*: SAsetT R 1)) => //=.
    apply/imfsetP => /=; exists (nth (SAset0 R _) (partition_of_graphs r) 0) => //.
    exact/mem_nth.
  rewrite SAset_cast_trans; last by rewrite geq_min addn1 leqnn.
  apply/esym/(SAset_cast_partition_of_graphs_above rsort).
  apply/imfsetP => /=; exists (nth (SAset0 R _) (partition_of_graphs r) 0) => //.
  exact/mem_nth.
have ScastE (s : S') y :
  y \in partition_of_graphs_above (fsval s) (sval (roots2_on (S'const s))) ->
  SAset_cast n (SAset_cast n.+1 y) = fsval s.
  rewrite SAset_cast_trans; last by rewrite geq_min addn1 leqnn.
  case: (roots2_on (S'const s)) => /= r [] + _.
  exact: SAset_cast_partition_of_graphs_above.
exists S.
split.
  split.
    rewrite SAset_partition_cast; last exact/addn1.
    apply/SAset_partition_of_graphs_above => // s.
    by case: (roots2_on (S'const s)) => /= r [].
  rewrite Scast/=; split=> // s.
  move rE: (roots2_on (S'const s)) => rR.
  case: rR rE => /= r [] rsort rroot rE.
  exists (size r), (in_tuple r); split.
    move=> i.
    apply(@subspace_eq_continuous _ _ 'M[R]_(1, 1) (fun x => \row__ (rootsR (evalpmp x (\prod_(p : P' s) val p)))`_i)); last first.
      apply/mx_continuous => j k.
      apply(@subspace_eq_continuous _ _ R (fun x => (rootsR (evalpmp x (\prod_(p : P' s) val p)))`_i)).
        by move=> x; rewrite inE/= => xs; rewrite mxE.
      apply/(rootsR_continuous (proj2_sig (pick s))); first last.
      - exact/S'const.
      - move=> x xs; exact/(size_gcdpm_const s).
      move=> x xs; rewrite ![evalpmp _ _]rmorph_prod/= !size_prod/=.
      + congr (_.+1 - _)%N; apply/eq_bigr; case=> /= q /imfsetP[/=] p _ -> _.
        exact/S'size.
      + by case=> /= q /imfsetP[/=] p p0 -> _.
      + case=> /= q /imfsetP[/=] p p0 -> _.
        by rewrite -size_poly_eq0 (S'size s p x xs) size_poly_eq0.
    move=> x; rewrite inE/= => xs.
    apply/eqP; rewrite rowPE forall_ord1 mxE (tnth_nth 0)/=.
    by rewrite -(rroot x xs) (nth_map 0).
  split=> //.
  apply/fsetP => /= x; rewrite 2!inE/=.
  apply/andP/imfsetP.
    move=> [] /imfsetP /= [y] /bigfcupP/= [t] _ yt ->.
    rewrite (ScastE _ _ yt) => /eqP ts.
    exists y => //.
    move: yt; have ->: t = s by apply/val_inj.
    by rewrite rE.
  move=> [] /= y yr ->; split; last by rewrite (ScastE s) ?rE.
  apply/imfsetP; exists y => //=.
  apply/bigfcupP; exists s; first by rewrite mem_index_enum.
  by rewrite rE.
move=> p; case=> /= s /imfsetP [/=] t /bigfcupP [] {}s _ + ->.
case: (roots2_on (S'const s)) => /= [] r [] rsort rroot tpart.
have [p0|p0] := eqVneq (evalpmp (\val (pick s)) (muni (\val p))) 0.
  move=> x y xt yt.
have t0 x : x \in (SAset_cast n.+1 t) -> (val p).@[tnth (ngraph x)] = 0 ->
    forall y, y \in (SAset_cast n.+1 t) -> (val p).@[tnth (ngraph y)] = 0.
  move=> xt px0.
  have: (\row_i x ord0 (lift ord_max i) \in rootsR (evalpmp x (\prod_(p : P' s) val p))).
  Search tuple_of _.-1.

pose proots : {SAset R^n.+1} := [set| nquantify n.+1 
    subst_formula 
    
      


    rewrite 
   [/imfsetP|]. xS] /=.
    move=> [] y; rewrite inE => /andP[] yS ys ->.
    apply/imfsetP.

    
  apply/andP; split; apply/allP
  app
  Search zip cat.
   Search all2. 
simple refine (exist _ _ _).
  simple refine (\big[fsetU/fset0]_(s' : S') _)%fset.
  have /= {S'p} s'p (q : elimp) : poly_invariant (val q) (val s') by apply/S'p.
  have [x' xs'] := (pick s').
  have /roots2_on: {in val s', forall x, size (rootsR (evalpmp x p)) = size (rootsR (evalpmp x' p))}.
      Search cindexR subresultant.
    Search cauchy_index.
  
  simple refine (
  [fset @SAset_cast R (n + 1) n.+1 s | s in _])%fset.

  
  Check partition_of_graphs.

  Search SAset_partition.
  case=> i /=; rewrite ltnS leq_eqVlt.
  case /boolP: (i == n.+1) => [/eqP -> _|_ /= ilt]; last exact: (S0 (Ordinal ilt)).



  Search (_ <= _.+1).
  case/boolP: (val i == n.+1); last first.
case: (split (cast_ord (esym (addn1 n.+1)) i)).
  exact S0.
    
    
Admitted.


End CylindricalDecomposition.

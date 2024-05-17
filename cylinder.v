From mathcomp Require Import freeg ssreflect ssrfun ssrbool eqtype choice seq ssrnat bigop tuple order fintype finfun path ssralg ssrnum ssrint poly matrix finmap mpoly complex.
From mathcomp Require Import polydiv polyrcf polyorder qe_rcf qe_rcf_th.

(* TODO: the following imports should not be needed after cleanup. *)
From mathcomp Require Import generic_quotient classical_sets topology normedtype.
Require Import auxresults formula subresultant semialgebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope type_scope.
Local Open Scope sa_scope.

Import Order.POrderTheory Order.TotalTheory.
Import GRing.Theory Num.Theory Num.Def.
Import GRing.
Import numFieldTopology.Exports.

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
      (forall i, {within set_of_SAset (val s'), continuous (tnth xi i)})
      /\ sorted (@SAfun_lt _ _) xi
      /\ [fset s in S | SAset_cast n s == val s'] = [fset SAset_cast _ x | x in partition_of_graphs_above (val s') xi]
  end.
Print isCylindricalDecomposition.

Local Notation isCD := isCylindricalDecomposition.

Lemma bool_eq_arrow {b b' : bool} : b = b' -> b -> b'.
Proof. by case: b' => // /negP. Qed.

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

Lemma imfset1 (T U : choiceType) (f : T -> U) (x : T) :
  [fset f x | x in [fset x]] = [fset f x].
Proof.
apply/fsetP => y; rewrite inE; apply/imfsetP/eqP => [[z]|yE].
  by rewrite inE => /eqP ->.
by exists x; rewrite // inE.
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

(*Definition elim_subdef0 n (P : {fset {poly {mpoly R[n]}}}) :=
  \big[fsetU/fset0]_(p : P) \big[fsetU/fset0]_(r : truncations (val p))
    (lead_coef (val r) |` [fset subresultant (val j) (val r) (val r)^`() | j in 'I_(size (val r)).-2]).

Definition elim_subdef1 n (P : {fset {poly {mpoly R[n]}}}) :=
    \big[fsetU/fset0]_(p : P) \big[fsetU/fset0]_(r : truncations (val p))
      \big[fsetU/fset0]_(q : P) (\big[fsetU/fset0]_(s : truncations (val q) | (size (val s) < size (val r))%N)
        (([fset subresultant (val j) (val r) (val s) | j in 'I_((size (val s)).-1)] `|` [fset subresultant (val j) (val s) (val r) | j in 'I_((size (val s)).-1)]))
        `|` \big[fsetU/fset0]_(s : truncations (val q) | size (val s) == size (val r))
          (let rs := ((lead_coef (val s)) *: (val r) - (lead_coef (val r)) *: (val s))%R in
          [fset subresultant (val j) (val s) (val rs) | j in 'I_((size rs).-1)])).

Definition elim n (P : {fset {poly {mpoly R[n]}}}) :=
  [fset x in elim_subdef0 P `|` elim_subdef1 P | mdeg (mlead x) != 0].

 *)

Ltac mp := 
  match goal with
  | |- (?x -> _) -> _ => have /[swap]/[apply]: x
  end.

Lemma set_of_SAset0 n :
  set_of_SAset (SAset0 R n) = set0.
Proof.
by rewrite classical_sets.eqEsubset; split; apply/subsetP => /= x; rewrite !inE /set_of_SAset mksetE inSAset0.
Qed.

Import ordered_qelim.ord.

Lemma rcf_sat_take [n : nat] (f : {formula_n R}) (e : seq R) :
  rcf_sat (take n e) f = rcf_sat e f.
Proof. by apply/rcf_satP/rcf_satP => /holds_take. Qed.

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
have rootsRP (y : 'rV_n) (z : d.-tuple R) : y \in s
  -> (forall i, root (evalpmp y P) (tnth z i))
  -> (forall x, root (evalpmp y P) x -> x \in z)
  -> sorted <%R z
  -> (z : seq R) = rootsR (evalpmp y P).
  move=> ys z0 z0P zsort.
  apply/(irr_sorted_eq_in (leT:=<%R : rel R)) => //.
  - move=> a b c _ _ _; exact/lt_trans.
  - exact/sorted_roots.
  move=> u; rewrite in_rootsR; move/(_ _ ys): dE z z0 z0P zsort.
  have [-> + + _ _ _|Py dE z z0 z0P zsort /=] := eqVneq (evalpmp y P) 0.
    by rewrite /rootsR roots0 => dy; rewrite -dy eqxx in d0.
  by apply/idP/idP => [/tnthP -[] i ->|/z0P].
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
    rewrite addn1 subDnCA// subnn addn0 (rootsRP x0)//.
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

Lemma jump_derivp (p : {poly R}) (x : R) : jump p^`() p x = root p x *+ (p != 0).
Proof.
rewrite /jump.
have [->|p0] := eqVneq p 0.
  by rewrite deriv0 mulr0 sgp_right0 ltxx expr0 eqxx.
rewrite mulr1n; move: (size_deriv p); have [-> /eqP|p'0 _] := eqVneq p^`() 0.
  rewrite size_poly0 -eqSS prednK ?size_poly_gt0// => /eqP p1.
  move: p0; have/size1_polyC -> : (size p <= 1)%N by rewrite -p1.
  by rewrite polyC_eq0 mul0r sgp_right0 ltxx expr0 rootC => /negPf ->.
case/boolP: (root p x) => px; last by rewrite muNroot.
rewrite (mu_deriv px) subn1 -subSS prednK ?mu_gt0// subSnn mulr1n.
by rewrite sgp_right_mul -sgp_right_deriv// -expr2 ltNge sqr_ge0 expr0.
Qed.

Lemma cindexR_derivp (p : {poly R}) : cindexR p^`() p = size (rootsR p).
Proof.
rewrite -sum1_size /cindexR rmorph_sum big_seq [RHS]big_seq.
by apply/eq_bigr => i; rewrite in_rootsR jump_derivp => /andP[] -> ->.
Qed.

Lemma SAset_castXl n m (s : {SAset R^n}) (t : {SAset R^m}) :
  t != SAset0 R m -> SAset_cast n (s :*: t) = s.
Proof.
have [->|[] x0 xt _] := set0Vmem t; first by rewrite eqxx.
apply/eqP/SAsetP => x.
  apply/inSAset_castDn/idP => [[y [+ ->]]|xs].
  by rewrite inSAsetX => /andP[+ _].
by exists (row_mx x x0); rewrite inSAsetX row_mxKl row_mxKr xs.
Qed.

Lemma imfset0 [T U : choiceType] (f : T -> U) :
  [fset f x | x in fset0] = fset0.
Proof.
have [-> //|[x]] := fset_0Vmem [fset f x | x in fset0].
by move=> /imfsetP[y] /=; rewrite inE.
Qed.

Lemma imfsetU [T U : choiceType] (f : T -> U) (s t : {fset T}) :
  [fset f x | x in s `|` t] = [fset f x | x in s] `|` [fset f x | x in t].
Proof.
apply/fsetP => x; rewrite in_fsetU; apply/imfsetP/orP => [[y] /= + ->|].
  by rewrite in_fsetU => /orP [ys|yt]; [left|right]; apply/imfsetP; exists y.
by case=> /imfsetP [y] /= ys ->; exists y => //; rewrite in_fsetU ys// orbT.
Qed.

Lemma imfset_bigfcup [I T U : choiceType] (r : seq I) (P : pred I)
  (F : I -> {fset T}) (f : T -> U) :
  [fset f x | x in \bigcup_(i <- r | P i) F i] =
    \bigcup_(i <- r | P i) [fset f x | x in F i].
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil imfset0.
by rewrite !big_cons; case: (P i) => //; rewrite imfsetU IHr.
Qed.

Lemma SAset_cast_partition_of_graphs_above n (s : {SAset R^n})
  (xi : seq (SAfunltType R n)) t :
  sorted <%O xi ->
  t \in partition_of_graphs_above s xi -> SAset_cast n t = s.
Proof.
move=> xisort /imfsetP[] /= u uxi ->.
apply/eqP/SAsetP => x; apply/inSAset_castDn/idP => [|xs].
  by move=> [y] [+] ->; rewrite inSAsetI inSAsetX => /andP[_] /andP[].
move: uxi => /(nthP (SAset0 R _)) [] i.
rewrite size_map size_iota => ilt <-.
set xi' := [seq (f : {SAfun R^n -> R^1}) x ord0 ord0 | f <- xi].
have: sorted <%O xi' by apply/(homo_sorted _ _ xisort) => f g /SAfun_ltP /(_ x).
move=> /SAset_partition_of_pts.
set S := [fset x0 | x0 in _] => /andP[] /andP[] + _ _.
have [<-|[y] yi _] := set0Vmem (nth (SAset0 R _) (partition_of_pts xi') i).
  move=> /negP; elim; apply/imfsetP.
  exists (nth (SAset0 R 1) (partition_of_pts xi') i) => //=.
  by apply/mem_nth; rewrite 2!size_map size_iota.
exists (row_mx x y); split; last by rewrite row_mxKl.
move: yi; rewrite -SAset_fiber_partition_of_graphs.
rewrite (nth_map (SAset0 R _)) ?size_map ?size_iota// inSAset_fiber inSAsetI => ->.
by rewrite inSAsetX row_mxKl row_mxKr xs inSAsetT.
Qed.

Lemma SAset_partition_cast n m (S : {fset {SAset R^n}}) :
  n = m -> SAset_partition [fset SAset_cast m x | x in S] = SAset_partition S.
Proof.
move=> nm; move: S; rewrite nm => S; congr SAset_partition.
apply/fsetP => /= x; apply/imfsetP/idP => [|xS].
  by move=> /= [y] yS ->; rewrite SAset_cast_id.
by exists x => //; rewrite SAset_cast_id.
Qed.

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
pose p := \prod_(p : P) muni (val p).
pose pT := truncations p.
pose elimp := [fset p in
    \big[fsetU/fset0]_(p : pT)
      (lead_coef (val p)
      |` [fset subresultant (val j) (val p) (val p)^`()
          | j in 'I_(size (val p)).-2])
  | mdeg (mlead p) != 0].
move: IHn => /(_ elimp) [S'][S'CD] S'p.
have S'part : SAset_partition S' by case: (n) S' S'CD {S'p} => [|m] S' [].
have pick (s' : S') : {x | x \in val s'}.
  case: (set0Vmem (val s')) => [s'0|//].
  move: S'part => /andP[] /andP[] /negP S'0 _ _.
  by exfalso; apply/S'0; rewrite -s'0 -in_fsub fsubT finset.in_setT.
have S'size (s' : S') :
    {in val s', forall x, size (evalpmp x p) = size (evalpmp (proj1_sig (pick s')) p)}.
  suff: {in val s' &, forall x y, (size (evalpmp x p) <= size (evalpmp y p))%N}.
    move=> S'size x xS; apply/anti_leq/andP.
    split; apply/S'size => //; exact/(proj2_sig (pick s')).
  move=> x y xS yS; apply/leq_sizeP => i yi.
  have [p0|p0] := eqVneq p`_i 0; first by rewrite coefE p0 meval0 if_same.
  move: (truncations_witness (leq_trans yi (leqnSn _))) => itrunc.
  have ip: (i < (size p))%N.
    rewrite ltnNge; apply/negP => /leq_sizeP/(_ _ (leqnn _)) pi0.
    by rewrite pi0 eqxx in p0.
  have si: size (truncate p i.+1) = i.+1.
    apply/anti_leq/andP; split.
      exact/(leq_trans (size_poly _ _))/geq_minl.
    rewrite ltnNge; apply/negP => /leq_sizeP/(_ _ (leqnn _)).
    rewrite coefE ltn_min leqnn/= ip => pi0.
    by rewrite pi0 eqxx in p0.
  move/leq_sizeP: yi => /(_ _ (leqnn _)).
  case/boolP: (mdeg (mlead p`_i) == 0) => [|psi].
    rewrite -eqSS mlead_deg//= => /msize_poly1P [c] /eqP c0 piE.
    by rewrite coefE ip piE mevalC => /c0.
  have pielim: p`_i \in elimp.
    apply/imfsetP => /=; exists p`_i => //=.
    rewrite inE psi andbT; apply/bigfcupP.
    exists [` itrunc]; first by rewrite mem_index_enum.
    by rewrite /= in_fset1U lead_coefE si -pred_Sn [X in _ == X]coefE ltn_min
      leqnn ip/= eqxx.
  move: (S'p [` pielim]) => /(_ s' x y xS yS) /= /[swap].
  by rewrite coefE ip => -> /eqP; rewrite sgz0 sgz_eq0 [X in X = 0]coefE ip => /eqP.
have S'const (s' : S') :
    {in val s', forall x, size (rootsR (evalpmp x p)) = size (rootsR (evalpmp (proj1_sig (pick s')) p))}.
  move=> x xs; set x' := proj1_sig (pick s').
  have [p0|x'0] := eqVneq (evalpmp x' p) 0.
    rewrite p0; suff ->: evalpmp x p = 0 by [].
    by apply/eqP; rewrite -size_poly_eq0 (S'size s')// size_poly_eq0; apply/eqP.
  have x0: (evalpmp x p) != 0.
    by rewrite -size_poly_eq0 (S'size s')// size_poly_eq0.
  apply/eqP; rewrite -eqz_nat -!cindexR_derivp; apply/eqP.
  rewrite -!pmv_subresultant; first last.
  - exact/lt_size_deriv.
  - exact/lt_size_deriv.
  rewrite !size_deriv !(S'size s' x xs).
  apply PMV.eq_pmv; rewrite all2E !size_cat !size_map eqxx/=.
  rewrite zip_cat ?size_map// !zip_map all_cat !all_map !all_rev.
  apply/andP; split; apply/allP => i; rewrite mem_iota => /=.
    move=> _; case: (i.+1 == _); last by rewrite !mulr0n.
    rewrite !mulr1n !lead_coefE (S'size s' _ xs) coefE [X in _ == _ X]coefE.
    rewrite prednK ?size_poly_gt0// size_poly.
    have [->|p0] := eqVneq (p`_(size (evalpmp x' p)).-1) 0.
      by rewrite !meval0.
    have [/eqP|pconst] := eqVneq (mdeg (mlead (p`_(size (evalpmp x' p)).-1))) 0.
      rewrite -eqSS mlead_deg//= => /msize_poly1P [c] _ ->.
      by rewrite !mevalC.
    suff pelim: p`_(size (evalpmp x' p)).-1 \in elimp.
      by apply/eqP/(S'p [` pelim] s') => //; apply/valP.
    apply/imfsetP; exists p`_(size (evalpmp x' p)).-1 => //.
    apply/andP; split; last by [].
    apply/bigfcupP.
    exists [` truncations_witness (leqnn (size (evalpmp x' p)))].
      by rewrite mem_index_enum.
    rewrite in_fset1U /= lead_coefE coef_truncate; apply/orP; left.
    rewrite [size (truncate _ _)]size_poly_eq (minn_idPl (size_poly _ _))//.
    by rewrite prednK ?size_poly_gt0// leqnn mulr1n.
  rewrite add0n => ilt.
  admit.
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
    admit. (* continuity *)
  split=> //.
  apply/fsetP => /= x; rewrite 2!inE/=.
  apply/andP/imfsetP.
    move=> [] /imfsetP /= [y] /bigfcupP/= [t] _ yt ->.
    rewrite SAset_cast_trans; last by rewrite geq_min addn1 leqnn.
    move rE': (roots2_on (S'const t)) yt => rR' yt.
    case: rR' rE' yt => /= r' [] r'sort r'root rE' yt.
    rewrite (SAset_cast_partition_of_graphs_above r'sort yt).
    rewrite (inj_eq val_inj) => /eqP tE.
    rewrite {t}tE in r' r'sort r'root rE' yt *.
    exists y => //.
    move: yt; congr (_ \in partition_of_graphs_above (val s) _).
    rewrite {}rE' in rE.
    by apply/eqP; rewrite (inj_eq val_inj); apply/eqP/ (EqdepFacts.eq_sig_fst rE).
  move=> [] /= y yr ->; split.
   STOP. 
      


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

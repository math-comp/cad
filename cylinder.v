From mathcomp Require Import freeg ssreflect ssrfun ssrbool eqtype choice seq ssrnat bigop tuple order fintype finfun path ssralg ssrnum ssrint poly matrix finmap mpoly complex.
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

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope type_scope.
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
  [set` SAset0 R n] = set0.
Proof.
by rewrite classical_sets.eqEsubset; split; apply/subsetP => /= x; rewrite !inE mksetE inSAset0.
Qed.

Import ordered_qelim.ord.

Lemma rcf_sat_take [n : nat] (f : {formula_n R}) (e : seq R) :
  rcf_sat (take n e) f = rcf_sat e f.
Proof. by apply/rcf_satP/rcf_satP => /holds_take. Qed.

Lemma rootsRPE d (p : {poly R}) (z : d.-tuple R) :
  (forall i, root p (tnth z i))
  -> (forall x, root p x -> x \in z)
  -> sorted <%R z
  -> (z : seq R) = rootsR p.
Proof.
have [-> _ z0P _|p0] := eqVneq p 0.
  rewrite rootsR0.
  move: z0P => /(_ (1 + \big[Order.max/0]_(x <- z) x)%R (root0 _)) /tnthP-[] i ziE.
  suff: tnth z i <= tnth z i - 1.
    by rewrite -subr_ge0 addrAC subrr add0r oppr_ge0 ler10.
  rewrite -{2}ziE addrAC subrr add0r le_bigmax; apply/orP; right.
  apply/hasP; exists (tnth z i); first exact/mem_tnth.
  exact/lexx.
move=> z0 z0P zsort.
apply/(irr_sorted_eq_in (leT:=<%R : rel R)) => //.
- move=> a b c _ _ _; exact/lt_trans.
- exact/sorted_roots.
move=> u; rewrite in_rootsR p0/=.
by apply/idP/idP => [|/z0P//] /tnthP -[] i ->.
Qed.

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

Definition SAselect_graph n m (x : m.-tuple nat) : {SAset R^(n + m)} :=
  [set| \big[And/True]_(i : 'I_m)
      ('X_(n + i) == 'X_(if (n <= x`_i)%N then (x`_i + m)%N else x`_i))].

Lemma SAselect_graphP n m (x : m.-tuple nat) (u : 'rV[R]_n) (v : 'rV[R]_m) :
  (row_mx u v \in SAselect_graph n x) = (v == \row_i (ngraph u)`_(tnth x i))%R.
Proof.
apply/SAin_setP/eqP => /= [|->].
  move=> /holdsAnd vE; apply/rowP => i.
  move: vE => /(_ i (mem_index_enum _) isT)/=.
  rewrite enum_ordD map_cat nth_catr 2?size_map ?size_enum_ord//.
  rewrite -map_comp (nth_map i) ?size_enum_ord// nth_ord_enum/= !mxE.
  rewrite (unsplitK (inr i)) (tnth_nth 0) nth_cat 2!size_map size_enum_ord.
  case: (ltnP x`_i n) => ni ->.
    rewrite ni -map_comp (nth_map (Ordinal ni)) ?size_enum_ord//.
    rewrite (nth_map (Ordinal ni)) ?size_enum_ord//.
    rewrite -[x`_i]/(nat_of_ord (Ordinal ni)) nth_ord_enum/= mxE.
    by rewrite (unsplitK (inl (Ordinal ni))).
  rewrite ltnNge (leq_trans ni (leq_addr _ _))/= nth_default.
    by rewrite nth_default// size_map size_enum_ord.
  by rewrite size_map size_enum_ord -addnBAC// leq_addl.
apply/holdsAnd => i _ _ /=.
rewrite enum_ordD map_cat nth_catr 2?size_map ?size_enum_ord//.
rewrite -map_comp (nth_map i) ?size_enum_ord// nth_ord_enum/= !mxE.
rewrite (unsplitK (inr i)) mxE (tnth_nth 0) nth_cat 2!size_map size_enum_ord.
case: (ltnP x`_i n) => ni.
  rewrite ni -map_comp (nth_map (Ordinal ni)) ?size_enum_ord//.
  rewrite (nth_map (Ordinal ni)) ?size_enum_ord//.
  rewrite -[x`_i]/(nat_of_ord (Ordinal ni)) nth_ord_enum/= mxE.
  by rewrite (unsplitK (inl (Ordinal ni))).
rewrite ltnNge (leq_trans ni (leq_addr _ _))/= nth_default; last first.
  by rewrite size_map size_enum_ord.
by rewrite nth_default// size_map size_enum_ord -addnBAC// leq_addl.
Qed.

Fact SAfun_SAselect n m (x : m.-tuple nat) :
  (SAselect_graph n x \in @SAfunc _ n m) && (SAselect_graph n x \in @SAtot _ n m).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAselect_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row_i (ngraph u)`_(tnth x i))%R.
by rewrite SAselect_graphP eqxx.
Qed.

Definition SAselect n m (x : m.-tuple nat) := MkSAfun (SAfun_SAselect n x).

Lemma SAselectE n m (x : m.-tuple nat) (u : 'rV[R]_n) :
  SAselect n x u = \row_i (ngraph u)`_(tnth x i).
Proof. by apply/eqP; rewrite inSAfun SAselect_graphP. Qed.

Fixpoint SAsum n : {SAfun R^n -> R^1}.
Proof.
case: n => [|n]; first exact: (SAfun_const 0 0).
apply/(SAcomp (SAadd R 1) (SAjoin _ (SAselect _ (in_tuple [:: n])))).
apply/(SAcomp (SAsum n) _).
apply/SAselect/mktuple => i.
exact/i.
Defined.
  
Lemma SAsumE n (u : 'rV[R]_n) :
  SAsum n u = \row__ \sum_i (u ord0 i)%R.
Proof.
apply/eqP; rewrite rowPE forall_ord1 mxE; apply/eqP.
elim: n u => [|n IHn] u; first by rewrite /SAsum SAfun_constE big_ord0 mxE.
rewrite /= SAcompE/= SAjoinE SAaddE SAcompE/= !SAselectE !mxE IHn.
rewrite (tnth_nth 0)/= (nth_map ord0) ?size_enum_ord//.
rewrite -[X in nth _ _ X]/(nat_of_ord (@ord_max n)) nth_ord_enum big_ord_recr/=.
congr (_ + _)%R; apply/eq_bigr => i _.
rewrite mxE tnth_mktuple (nth_map ord0); last first.
  by rewrite size_enum_ord ltnS ltnW.
congr (u _ _).
have ->: i = lift ord_max i :> nat by rewrite /= /bump leqNgt (ltn_ord i).
rewrite nth_ord_enum; apply/val_inj => /=.
by rewrite /bump leqNgt (ltn_ord i).
Qed.

Definition ifthenelse (P Q R : formula R) :=
  ((P ==> Q) /\ ((~ P) ==> R))%oT.

Definition SAchanges_graph n : {SAset R^(n + n.-1)} :=
  [set| \big[And/True]_(i : 'I_n.-1) (ifthenelse ('X_i * 'X_i.+1 <% 0) ('X_(n + i) == 1) ('X_(n + i) == 0))].

Lemma ltn_neq (n m : nat) : (n < m)%N -> n != m.
Proof. by rewrite ltn_neqAle => /andP[]. Qed.

Lemma forallb_all [n : nat] (a : pred 'I_n) :
  [forall i, a i] = all a (enum 'I_n).
Proof.
apply/forallP/allP => /= aT i //.
by apply/aT; rewrite mem_enum.
Qed.

Lemma nth_map_ord (T : Type) (x : T) n (f : 'I_n -> T) (i : 'I_n) :
  nth x [seq f i | i <- enum 'I_n] i = f i.
Proof. by rewrite (nth_map i) ?nth_enum_ord// size_enum_ord. Qed.

Lemma SAchanges_graphP n (u : 'rV[R]_n) (v : 'rV[R]_n.-1) :
  (row_mx u v \in SAchanges_graph n) = (v == \row_i ((ngraph u)`_i * (ngraph u)`_i.+1 < 0)%R%:R).
Proof.
case: n u v => /= [|n] u v.
  rewrite rowPE forallb_all enum_ord0/=.
  by apply/SAin_setP/holdsAnd; case.
apply/SAin_setP/eqP => /= [|->].
  move=> /holdsAnd vE; apply/rowP => i.
  move: vE => /(_ i (mem_index_enum _) isT) /= []; rewrite !mxE.
  have {1 4 7}->: i = lshift n (lift ord_max i) :> nat.
    by rewrite /= /bump leqNgt ltn_ord.
  have ->: i.+1 = lshift n (lift ord0 i) :> nat by [].
  have ->: (n.+1 + i)%N = rshift n.+1 i :> nat by [].
  rewrite !nth_map_ord !mxE !(unsplitK (inl _)) !(unsplitK (inr _)).
  by case: (_ < 0)%R => [+ _|_]; apply.
apply/holdsAnd => i _ _ /=.
have {1 4}->: i = lshift n (lift ord_max i) :> nat.
  by rewrite /= /bump leqNgt ltn_ord.
have ->: i.+1 = lshift n (lift ord0 i) :> nat by [].
have ->: (n.+1 + i)%N = rshift n.+1 i :> nat by [].
rewrite !nth_map_ord !mxE !(unsplitK (inl _)) !(unsplitK (inr _)) !mxE.
have {1 3}->: i = lshift n (lift ord_max i) :> nat.
  by rewrite /= /bump leqNgt ltn_ord.
have ->: i.+1 = lshift n (lift ord0 i) :> nat by [].
rewrite !nth_map_ord.
by split=> [|/negP/negPf] ->.
Qed.

Fact SAfun_SAchanges n :
  (SAchanges_graph n \in @SAfunc _ n n.-1) && (SAchanges_graph n \in @SAtot _ n n.-1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAchanges_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row_i ((ngraph u)`_i * (ngraph u)`_i.+1 < 0)%R%:R).
by rewrite SAchanges_graphP eqxx.
Qed.

Definition SAchanges n := SAcomp (SAsum n.-1) (MkSAfun (SAfun_SAchanges n)).

Lemma changes_rcons (x : R) (s : seq R) : changes (rcons s x) = ((last 0 s * x < 0)%R + changes s)%N.
Proof.
elim: s => [|y s IHs]; first by rewrite /= mulrC.
rewrite /= {}IHs; case: s => [|z s] /=; first by rewrite mul0r mulr0.
by rewrite !addnA [((y * z < 0)%R + _)%N]addnC.
Qed.

Lemma changes_rev (s : seq R) : changes (rev s) = changes s.
Proof.
move nE: (size s) => n.
elim: n s nE => [|n IHn] s nE; first by rewrite (size0nil nE).
case: s nE => [//|] x s/= /eqP; rewrite eqSS => /eqP sn.
by rewrite rev_cons changes_rcons last_rev mulrC IHn.
Qed.

Lemma big_ordD (T : Type) (idx : T) (op : Monoid.law idx) (n m : nat) (P : pred 'I_(n + m)) (F : 'I_(n + m) -> T) :
  \big[op/idx]_(i < n + m | P i) F i = op (\big[op/idx]_(i < n | P (lshift m i)) F (lshift m i)) (\big[op/idx]_(i < m | P (rshift n i)) F (rshift n i)).
Proof.
pose G i :=
  match ltnP i (n + m) with
  | LtnNotGeq inm => F (Ordinal inm)
  | _ => idx
  end.
pose Q i :=
  match ltnP i (n + m) with
  | LtnNotGeq inm => P (Ordinal inm)
  | _ => false
  end.
have FG i : F i = G i.
  rewrite /G; move: (ltn_ord i); case: ltnP => // j _.
  by congr F; apply/val_inj.
have PQ i : P i = Q i.
  rewrite /Q; move: (ltn_ord i); case: ltnP => // j _.
  by congr P; apply/val_inj.
under eq_bigr do rewrite FG.
under eq_bigl do rewrite PQ.
rewrite big_ord_iota iotaD big_cat add0n -big_ord_iota.
congr (op _ _); first exact/eq_big.
rewrite iotaE0 big_map -big_ord_iota.
by apply/eq_big => /= i; rewrite ?PQ ?HQ.
Qed.

Lemma changesE (s : seq R) :
  changes s = \sum_(i < (size s).-1) ((s`_i * s`_i.+1 < 0)%R : nat).
Proof.
elim: s => /= [|x + ->]; first by rewrite big_ord0.
case=> /= [|y s]; first by rewrite !big_ord0 mulr0 ltxx.
by rewrite big_ord_recl/=.
Qed.

Lemma SAchangesE n (u : 'rV[R]_n) :
  SAchanges n u = \row__ (changes (ngraph u))%:R.
Proof.
apply/eqP; rewrite SAcompE/= SAsumE rowPE forall_ord1 !mxE.
rewrite changesE size_map size_enum_ord natr_sum.
apply/eqP/eq_bigr => /= i _.
move: (inSAfun (MkSAfun (SAfun_SAchanges n)) u
  (\row_i ((ngraph u)`_i * (ngraph u)`_i.+1 < 0)%R%:R)).
rewrite SAchanges_graphP eqxx => /eqP ->.
case: n u i => [|n] u; first by case.
by move=> /= i; rewrite mxE.
Qed.

(* Evaluates a polynomial represented in big-endian in R^n at a point in R. *)
Definition SAhorner_graph n : {SAset R^(n + 1 + 1)} :=
  [set| nquantify n.+2 n Exists (
  subst_formula (rcons (iota n.+2 n) n.+1) (SAsum n) /\
  \big[And/True]_(i < n) ('X_(n.+2 + i) == ('X_i * 'X_n ^+ i)))].

Lemma SAhorner_graphP n (u : 'rV[R]_(n + 1)) (v : 'rV[R]_1) :
  (row_mx u v \in SAhorner_graph n) = (v == \row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
Proof.
rewrite /SAhorner_graph.
rewrite -2![X in nquantify X]addn1 -[X in nquantify X](size_ngraph (row_mx u v)).
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
apply/nexistsP; exists ([tuple ((ngraph u)`_i * u ord0 (rshift n ord0) ^+ i)%R | i < n]).
move=> /=; split.
  apply/holds_subst.
  rewrite -cats1 subst_env_cat/= subst_env_iota_catr; first last.
  - by rewrite size_map size_enum_ord.
  - by rewrite size_map size_enum_ord !addn1.
  rewrite nth_cat size_map size_enum_ord 2![in X in (_ < X)%N]addn1 leqnn.
  have nsE: n.+1 = rshift (n + 1) (@ord0 0) by rewrite /= addn0 addn1.
  rewrite [X in _`_X]nsE nth_map_ord mxE (unsplitK (inr _)).
  suff: SAsum _ (\row_(i < n) ((ngraph u)`_i * u ord0 (rshift n ord0) ^+ i)%R) = v.
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
rewrite nth_cat size_map size_enum_ord [X in (_ < X + 1)%N]addn1 leq_addr nth_map_ord.
have nE: n = lshift 1 (rshift n (@ord0 0)) by rewrite /= addn0.
have {1 3}->: i = lshift 1 (lshift 1 i) :> nat by [].
by rewrite [X in _`_X ^+ _]nE !nth_map_ord !mxE !(unsplitK (inl _)).
Qed.

Fact SAfun_SAhorner n :
  (SAhorner_graph n \in @SAfunc _ (n + 1) 1) && (SAhorner_graph n \in @SAtot _ (n + 1) 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAhorner_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
by rewrite SAhorner_graphP eqxx.
Qed.

Definition SAhorner n := MkSAfun (SAfun_SAhorner n).

Lemma SAhornerE n (u : 'rV[R]_(n + 1)) :
  SAhorner n u = (\row__ (\poly_(i < n) (ngraph u)`_i).[u ord0 (rshift n ord0)])%R.
Proof. by apply/eqP; rewrite inSAfun SAhorner_graphP. Qed.

(* Function giving the number of roots of a polynomial of degree at most n.-1
   encoded in big endian in R^n *)
Definition SAnbroots_graph n : {SAset R^(n + 1)} :=
  [set| (\big[And/True]_(i < n.+1) ('X_i == 0)) \/ \big[Or/False]_(i < n) (('X_n == Const i%:R%R) /\
    nquantify n.+1 i Exists (
      \big[And/True]_(j < i) subst_formula (iota 0 n ++ [:: n.+1 + j; n.+1 + i]%N)
        (SAhorner n) /\
        \big[And/True]_(j < i.-1) ('X_(n.+1 + j) <% 'X_(n.+1 + j.+1)) /\
      'forall 'X_(n.+1 + i), subst_formula (iota 0 n ++ [:: n.+1 + i; (n.+1 + i).+1]%N)
        (SAhorner n) ==> \big[Or/False]_(j < i) ('X_(n.+1 + i) == 'X_(n.+1 + j))))].

Lemma SAnbroots_graphP n (u : 'rV[R]_n) (v : 'rV[R]_1) :
  (row_mx u v \in SAnbroots_graph n) = (v == \row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R).
Proof.
  have subst_env0 (u' : 'rV[R]_n) (i : 'I_n) (r : i.-tuple R) (x : R):
    (subst_env (iota 0 n ++ [:: (n.+1 + i)%N; (n.+1 + i).+1])
      (set_nth 0 ([seq row_mx u' v ord0 i0 | i0 <- enum 'I_(n + 1)] ++ r)
        (n.+1 + i) x)) =
    ([seq row_mx u' v ord0 i0 | i0 <- [seq lshift 1 i | i <- enum 'I_n]] ++
        [:: x; 0]).
  rewrite subst_env_cat {1}set_nth_catr; last first.
    by rewrite size_map size_enum_ord addn1 leq_addr.
  rewrite {1}enum_ordD map_cat -catA subst_env_iota_catl/=; last first.
    by rewrite -map_comp size_map size_enum_ord.
  rewrite nth_set_nth/= eqxx nth_set_nth/= -[X in (X == _)]addn1.
  rewrite -[X in (_ == X)]addn0 eqn_add2l/= -addnS nth_cat.
  rewrite size_map size_enum_ord [X in (_ < X)%N]addn1 ltnNge leq_addr/=.
  rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
  by rewrite [r`_i.+1]nth_default// size_tuple.
have [->|u0] := eqVneq u 0.
  have ->: \poly_(i < n) (@ngraph R n 0)`_i = 0.
    apply/polyP => i; rewrite coef_poly coef0.
    case: (ltnP i n) => [ilt|//].
    by rewrite -/(nat_of_ord (Ordinal ilt)) nth_map_ord mxE.
  rewrite rootsR0/=; apply/SAin_setP/eqP => [/= [/holdsAnd|/holdsOr-[] i]| ->].
  - move=> /(_ ord_max (mem_index_enum _) isT) /=.
    have nE: n = rshift n (@ord0 0) by rewrite /= addn0.
    rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inr _)) => v0.
    by apply/eqP; rewrite rowPE forall_ord1 mxE; apply/eqP.
  - move=> [_][_]/= [_].
    rewrite -[X in nquantify X]addn1 -[X in nquantify X](size_ngraph (row_mx 0 v)).
    move=> /nexistsP[r]/= [_][_] /(_ (1 + \big[Order.max/0]_(x <- r) x))%R; mp.
      apply/holds_subst; rewrite subst_env0 -map_comp.
      have /eqP: SAhorner n (row_mx 0 (\row__ (1 + \big[maxr/0]_(x <- r) x)%R)) = 0.
        apply/eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
        apply/eqP; rewrite -[in RHS](horner0 (1 + \big[maxr/0]_(x <- r) x)%R).
        rewrite mxE; congr (_.[_])%R.
        apply/polyP => j; rewrite coef0 coef_poly.
        case: (ltnP j n) => [jn|//]; rewrite ngraph_cat nth_cat size_ngraph jn.
        by rewrite -/(nat_of_ord (Ordinal jn)) nth_map_ord mxE.
      rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      congr (holds (_ ++ _) _); last by rewrite /= enum_ordSl enum_ord0/= !mxE.
      apply/(@eq_from_nth _ 0) => [|k]; rewrite size_ngraph.
        by rewrite size_map size_enum_ord.
      move=> kn; rewrite /= -[k]/(nat_of_ord (Ordinal kn)) !nth_map_ord.
      by rewrite [in RHS]mxE (unsplitK (inl _)).
    move=> /holdsOr[j] [_][_]/= .
    rewrite nth_set_nth/= eqxx nth_set_nth/= eqn_add2l.
    move: (ltn_ord j); rewrite ltn_neqAle => /andP[] /negPf -> _.
    rewrite nth_cat size_map size_enum_ord [X in (_ < X)%N]addn1 ltnNge leq_addr/=.
    rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0 => jE.
    have: r`_j <= \big[maxr/0]_(x <- r) x.
      rewrite le_bigmax; apply/orP; right; apply/hasP; exists r`_j.
        by apply/mem_nth; rewrite size_tuple.
      exact/lexx.
    by rewrite -jE; rewrite -subr_ge0 opprD addrCA subrr addr0 oppr_ge0 ler10.
  left; apply/holdsAnd; case=> i /= ilt _ _ /=.
  rewrite enum_ordD map_cat -2!map_comp nth_cat size_map size_enum_ord.
  case: (ltnP i n) => iltn.
    by rewrite -/(nat_of_ord (Ordinal iltn)) nth_map_ord mxE (unsplitK (inl _)) mxE.
  have ->: i = n by apply/le_anti/andP.
  rewrite subnn -[X in _`_X]/(nat_of_ord (@ord0 0)) nth_map_ord mxE.
  by rewrite (unsplitK (inr _)) mxE.
apply/SAin_setP/eqP => [[/holdsAnd|/holdsOr/=[] i [_][_]]|].
  - move=> uv0; suff: u = 0 by move/eqP: u0.
  apply/rowP => i; rewrite mxE.
  move: uv0 => /(_ (lift ord_max i) (mem_index_enum _) isT)/=.
  rewrite /bump leqNgt (ltn_ord i)/= add0n.
  rewrite -[X in _`_X]/(nat_of_ord (lshift 1 i)) nth_map_ord mxE.
  by rewrite (unsplitK (inl _)).
  - have nE: n = @rshift n 1 ord0 by rewrite /= addn0.
  rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inr _)) => -[] vE.
  rewrite -[X in nquantify X]addn1 -[X in nquantify X](size_ngraph (row_mx u v)).
  move=> /nexistsP[r]/= [] /holdsAnd/= rroot [] rsort rall. 
  apply/eqP; rewrite rowPE forall_ord1 vE mxE eqr_nat -(size_tuple r); apply/eqP.
  congr size; apply/rootsRPE => [j|x x0|].
  - move: rroot => /(_ j (mem_index_enum _) isT) /holds_subst.
    rewrite subst_env_cat {1}enum_ordD map_cat -catA subst_env_iota_catl/=; last first.
      by rewrite -map_comp size_map size_enum_ord.
    rewrite nth_cat size_map size_enum_ord ltnNge [X in (X <= _)%N]addn1 leq_addr/=.
    rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
    rewrite nth_cat size_map size_enum_ord ltnNge [X in (X <= _)%N]addn1 leq_addr/=.
    rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
    rewrite [r`_i]nth_default; last by rewrite size_tuple.
    move=> r0; suff {}r0': SAhorner n (row_mx u (\row__ r`_j)) = 0.
      move: r0' => /eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
      rewrite !mxE -tnth_nth /root; congr (_.[_]%R == 0).
      by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
    apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
    move: r0; congr (holds (_ ++ _) _); last first.
      by rewrite /= enum_ordSl enum_ord0/= !mxE.
    rewrite -map_comp; apply/(@eq_from_nth _ 0) => [|k];
        rewrite size_map size_enum_ord.
      by rewrite size_ngraph.
    move=> kn; rewrite /= -[k]/(nat_of_ord (Ordinal kn)) !nth_map_ord.
    by rewrite mxE (unsplitK (inl _)).
  - move: rall => /(_ x); mp.
      apply/holds_subst; rewrite subst_env0.
      have /eqP: SAhorner n (row_mx u (\row__ x)) = 0.
        apply/eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
        move: x0; rewrite !mxE /root; congr (_.[_]%R == 0).
        by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
      rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
      congr (holds (_ ++ _) _); last by rewrite /= enum_ordSl enum_ord0/= !mxE.
      rewrite -map_comp; apply/(@eq_from_nth _ 0) => [|k]; rewrite size_ngraph.
        by rewrite size_map size_enum_ord.
      move=> kn; rewrite /= -[k]/(nat_of_ord (Ordinal kn)) !nth_map_ord.
      by rewrite mxE (unsplitK (inl _)).
    move=> /holdsOr /= [j] [_][_].
    rewrite nth_set_nth/= eqxx nth_set_nth/= eqn_add2l.
    move: (ltn_ord j); rewrite ltn_neqAle => /andP[] /negPf -> _.
    rewrite nth_cat size_map size_enum_ord [X in (_ < X)%N]addn1 ltnNge leq_addr/=.
    rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0 => ->.
    by apply/mem_nth; rewrite size_tuple.
  - apply/(sortedP 0) => j; rewrite size_tuple -ltn_predRL => ji.
    move: rsort => /holdsAnd /(_ (Ordinal ji) (mem_index_enum _) isT)/=.
    rewrite nth_cat size_map size_enum_ord {1}addn1 ltnNge leq_addr/=.
    rewrite {1}addn1 subDnCA// subnn addn0.
    rewrite nth_cat size_map size_enum_ord {1}addn1 ltnNge leq_addr/=.
    by rewrite {1}addn1 subDnCA// subnn addn0.
set r := (rootsR (\poly_(i < n) (ngraph u)`_i)) => vE.
right; apply/holdsOr => /=.
have rn: (size r < n)%N.
  rewrite ltnNge; apply/negP.
  move=> /(leq_trans (size_poly _ (fun i => (ngraph u)`_i)))/poly_ltsp_roots.
  move=> /(_ (uniq_roots _ _ _)); mp.
    by apply/allP => x; rewrite in_rootsR => /andP[_].
  move=> /polyP => u0'; move/eqP: u0; apply.
  apply/rowP => i; move: u0' => /(_ i).
  by rewrite coef_poly ltn_ord nth_map_ord mxE coef0.
exists (Ordinal rn); split; first exact/mem_index_enum.
split=> //=.
split.
  have nE: n = rshift n (@ord0 0) by rewrite /= addn0.
  by rewrite [X in _`_X]nE nth_map_ord mxE (unsplitK (inr _)) vE mxE.
rewrite -[X in nquantify X]addn1 -[X in nquantify X](size_ngraph (row_mx u v)).
apply/nexistsP; exists (in_tuple r).
split.
  apply/holdsAnd => /= i _ _; apply/holds_subst.
  rewrite subst_env_cat {1}enum_ordD map_cat -catA subst_env_iota_catl/=; last first.
    by rewrite -map_comp size_map size_enum_ord.
  rewrite nth_cat size_map size_enum_ord ltnNge [X in (X <= _)%N]addn1 leq_addr/=.
  rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
  rewrite nth_cat size_map size_enum_ord ltnNge [X in (X <= _)%N]addn1 leq_addr/=.
  rewrite [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
  rewrite [r`_(size r)]nth_default//.
  have: r`_i \in r by apply/mem_nth.
  rewrite in_rootsR => /andP[_] r0.
  have {}r0: SAhorner n (row_mx u (\row__ r`_i)) = 0.
    apply/eqP; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
    move: r0; rewrite !mxE /root; congr (_.[_]%R == 0).
    by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
  move/eqP : r0; rewrite inSAfun => /rcf_satP; rewrite !ngraph_cat -catA.
  congr (holds (_ ++ _) _); last first.
    by rewrite /= enum_ordSl enum_ord0/= !mxE.
  rewrite -map_comp; apply/(@eq_from_nth _ 0) => [|k];
      rewrite size_ngraph.
    by rewrite size_map size_enum_ord.
  move=> kn; rewrite /= -[k]/(nat_of_ord (Ordinal kn)) !nth_map_ord.
  by rewrite mxE (unsplitK (inl _)).
split=> /= [|x /holds_subst].
  apply/holdsAnd => /= i _ _.
  rewrite nth_cat size_map size_enum_ord {1}addn1 ltnNge leq_addr/=.
  rewrite {1}addn1 subDnCA// subnn addn0.
  rewrite nth_cat size_map size_enum_ord {1}addn1 ltnNge leq_addr/=.
  rewrite {1}addn1 subDnCA// subnn addn0.
  have /(sortedP 0)/(_ i) : sorted <%R r by apply/sorted_roots.
  by rewrite -ltn_predRL => /(_ (ltn_ord i)).
rewrite -/(nat_of_ord (Ordinal rn)) -[r]/(tval (in_tuple r)) subst_env0 => x0.
have /(nthP 0) []: x \in r.
  rewrite in_rootsR; apply/andP; split.
    apply/eqP => /polyP u0'; move/eqP: u0; apply.
    apply/rowP => i; move: u0' => /(_ i).
    by rewrite coef_poly ltn_ord nth_map_ord mxE coef0.
  suff {}r0: SAhorner n (row_mx u (\row__ x)) = 0.
    move/eqP : r0; rewrite SAhornerE rowPE forall_ord1 !mxE (unsplitK (inr _)).
    rewrite !mxE /root; congr (_.[_]%R == 0).
    by apply/eq_poly => k kn; rewrite ngraph_cat nth_cat size_ngraph kn.
  apply/eqP; rewrite inSAfun; apply/rcf_satP; rewrite !ngraph_cat -catA.
  move: x0; congr (holds (_ ++ _) _); last first.
    by rewrite /= enum_ordSl enum_ord0/= !mxE.
  rewrite -map_comp; apply/(@eq_from_nth _ 0) => [|k];
      rewrite size_map size_enum_ord.
    by rewrite size_ngraph.
  move=> kn; rewrite /= -[k]/(nat_of_ord (Ordinal kn)) !nth_map_ord.
  by rewrite mxE (unsplitK (inl _)).
move=> i ir <-; apply/holdsOr; exists (Ordinal ir).
split; first exact/mem_index_enum.
split=> //=.
rewrite nth_set_nth/= eqxx nth_set_nth/= eqn_add2l.
rewrite (ltn_eqF ir) nth_cat size_map size_enum_ord [X in (_ < X)%N]addn1.
by rewrite ltnNge leq_addr/= [X in (_ - X)%N]addn1 subDnCA// subnn addn0.
Qed.

Fact SAfun_SAnbroots n :
  (SAnbroots_graph n \in @SAfunc _ n 1) && (SAnbroots_graph n \in @SAtot _ n 1).
Proof.
apply/andP; split.
  by apply/inSAfunc => u y1 y2; rewrite !SAnbroots_graphP => /eqP -> /eqP.
apply/inSAtot => u; exists (\row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R)%R.
by rewrite SAnbroots_graphP eqxx.
Qed.

Definition SAnbroots n := MkSAfun (SAfun_SAnbroots n).

Lemma SAnbrootsE n (u : 'rV[R]_n) :
  SAnbroots n u = (\row__ (size (rootsR (\poly_(i < n) (ngraph u)`_i)))%:R)%R.
Proof. by apply/eqP; rewrite inSAfun SAnbroots_graphP. Qed.

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

Lemma id_continuous {T : topologicalType} : continuous (@id T).
Proof. by apply/continuousP => A; rewrite preimage_id. Qed.

Lemma horner_continuous {K : numFieldType} (p : {poly K}) :
  continuous (horner p)%R.
Proof.
apply/(eq_continuous (f:=fun x : K => \sum_(i < size p) p`_i * x ^+ i)) => x.
  by rewrite -[p in RHS]coefK horner_poly.
apply/(@continuous_sum K (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod K)).
move=> /= i _.
apply/continuousM; first exact/cst_continuous.
exact/continuousX/id_continuous.
Qed.

Lemma meval_continuous n {K : numFieldType} (p : {mpoly K[n]}) :
  continuous (fun x : 'rV[K]_n => p.@[x ord0])%R.
Proof.
apply/(eq_continuous (f:=fun x : 'rV[K]_n => \sum_(m <- msupp p) p@_m * \prod_i x ord0 i ^+ m i)) => x.
  exact/mevalE.
apply/(@continuous_sum K (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod K)).
move=> /= i _.
apply/continuousM; first exact/cst_continuous.
apply/continuous_prod => j _.
exact/continuousX/coord_continuous.
Qed.

Lemma meval_sum [I : Type] {n : nat} {K : ringType} (v : 'I_n -> K) (r : seq I) (F : I -> {mpoly K[n]}) (P : pred I) :
  (\sum_(i <- r | P i) F i).@[v] = \sum_(i <- r | P i) (F i).@[v].
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil meval0.
rewrite !big_cons; case: (P i) => [|//].
by rewrite mevalD IHr.
Qed.

Lemma evalpmpM n (p q : {poly {mpoly R[n]}}) (x : 'rV_n) :
  (evalpmp x (p * q) = (evalpmp x p) * (evalpmp x q))%R.
Proof.
apply/polyP => i.
rewrite !coef_map/= !coefM meval_sum.
apply/eq_bigr => /= j _.
by rewrite mevalM !coef_map.
Qed.

Lemma evalpmp_prod [I : Type] n (x : 'rV_n) (r : seq I) (F : I -> {poly {mpoly R[n]}}) (P : pred I) :
  evalpmp x (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) evalpmp x (F i).
Proof.
elim: r => [|i r IHr].
  by apply/polyP => i; rewrite !big_nil/= coef_map/= !coef1 mevalMn meval1.
rewrite !big_cons; case: (P i) => [|//].
by rewrite evalpmpM IHr.
Qed.

(* mu_eq0 is stated with rcfType in real_closed.qe_rcf_th *)
Lemma mu_eq0 (F : idomainType) (p : {poly F}) (x : F) :
  p != 0 -> (\mu_x p == 0%N) = ~~ root p x.
Proof. by move=> /mu_gt0 <-; rewrite lt0n negbK. Qed.

Lemma big_hasE (T I J : Type) (idx : T) (op : Monoid.com_law idx)
  (r : seq I) (P : pred I) (F : I -> T) (s : seq J) (a : I -> pred J) :
  (forall i, P i -> (count (a i) s <= 1)%N) ->
  \big[op/idx]_(i <- r | P i && has (a i) s) F i = \big[op/idx]_(j <- s) \big[op/idx]_(i <- r | P i && a i j) F i.
Proof.
move=> s1.
elim: r => [|i r IHr].
  under [in RHS]eq_bigr do rewrite big_nil.
  rewrite big_nil big_const_idem//.
  exact/Monoid.mulm1.
under [in RHS]eq_bigr do rewrite big_cons.
rewrite big_cons; case /boolP: (P i) => //= Pi.
case/boolP: (has (a i) s) => [si|]; last first. 
  rewrite -all_predC.
  rewrite {}IHr; elim: s s1 => /= [|j s IHs] s1 si; first by rewrite !big_nil.
  rewrite !big_cons.
  move/andP: si => [] /negPf -> /IHs -> // k /s1.
  by case: (a k j) => //=; rewrite add1n ltnS leqn0 => /eqP ->.
rewrite {}IHr; elim: s s1 si => /= [//|] j s IHs s1.
rewrite !big_cons Monoid.mulmA.
case: (a i j) (s1 i Pi) => /= [|_].
  rewrite add1n ltnS leqNgt -has_count => ais _; congr (op _ _).
  elim: s ais {IHs s1} => [_|k s IHs] /=.
    by rewrite !big_nil.
  by rewrite negb_or !big_cons => /andP[] /negPf -> /IHs ->.
move=> /IHs <-.
  by rewrite Monoid.mulmCA Monoid.mulmA.
move=> k /s1.
by case: (a k j) => //=; rewrite add1n ltnS leqn0 => /eqP ->.
Qed.

Lemma big_pred1_seq [T : Type] [idx : T] (op : Monoid.law idx) 
    [I : eqType] (r : seq I) (i : I) (F : I -> T) :
  uniq r ->
  \big[op/idx]_(j <- r | j == i) F j = if i \in r then F i else idx.
Proof.
elim: r => [_|j r IHr /= /andP[] jr runiq]; first by rewrite big_nil.
rewrite big_cons in_cons eq_sym.
move: jr; have [<- /= /negP jr|ij _ /=] := eqVneq i j; last exact/IHr.
rewrite big_seq_cond big_mkcond big1_idem; first exact/Monoid.mulm1.
  exact/Monoid.mulm1.
by move=> k _; case: ifP => [/andP[] /[swap] /eqP ->|//].
Qed.

Lemma dvdp_mu (F : closedFieldType) (p q : {poly F}) :
  p != 0 -> q != 0 ->
  (p %| q) = all (fun x => \mu_x p <= \mu_x q)%N (dec_roots p).
Proof.
move: (dec_roots p) (uniq_dec_roots p) (dec_roots_closedP p)
    (dec_roots_closedP q) => r.
rewrite -!lead_coefE -lead_coef_eq0.
elim: r p => [p _ pE _ p0 _|x r IHr p /= /andP[] xr runiq pE qE p0 q0].
  by rewrite pE/= big_nil alg_polyC /dvdp modpC ?eqxx// lead_coef_eq0.
rewrite {1}pE big_cons dvdpZl// Gauss_dvdp; last first.
  rewrite /coprimep (eqp_size (gcdpC _ _)) -/(coprimep _ _).
  apply/coprimep_expr; rewrite coprimep_XsubC root_bigmul -all_predC.
  apply/allP => y yr/=.
  case: (\mu_y p) => [|n]; first by rewrite expr0 root1.
  rewrite root_exp_XsubC; apply/eqP => xy.
  by move/negP: xr; rewrite xy.
rewrite root_le_mu//; congr andb.
rewrite -(dvdpZl _ _ p0) IHr//.
- apply/eq_in_all => y yr; congr (_ <= _)%N.
  rewrite mu_mulC// mu_prod; last first.
    rewrite prodf_seq_neq0; apply/allP => z _ /=.
    by rewrite expf_eq0 polyXsubC_eq0 andbF.
  under eq_bigr do rewrite mu_exp mu_XsubC mulnbl eq_sym.
  by rewrite -big_mkcond/= big_pred1_seq// yr.
- rewrite lead_coefZ lead_coef_prod.
  under [in RHS]eq_bigr do rewrite lead_coef_exp lead_coefXsubC expr1n.
  rewrite [in RHS]big1_idem//= ?mulr1//; congr (_ *: _).
  apply/eq_big_seq => y yr.
  rewrite mu_mulC// mu_prod; last first.
    rewrite prodf_seq_neq0; apply/allP => z _ /=.
    by rewrite expf_eq0 polyXsubC_eq0 andbF.
  under eq_bigr do rewrite mu_exp mu_XsubC mulnbl eq_sym.
  by rewrite -big_mkcond/= big_pred1_seq// yr.
- rewrite lead_coef_eq0 scaler_eq0 (negPf p0)/= prodf_seq_neq0.
  by apply/allP => y _ /=; rewrite expf_eq0 polyXsubC_eq0 andbF.
Qed.

Lemma mu_eqp (F : closedFieldType) (p q : {poly F}) (x : F) :
  p %= q -> \mu_x p = \mu_x q.
Proof.
have [->|p0] := eqVneq p 0; first by rewrite eqp_sym eqp0 => /eqP ->.
have [->|q0] := eqVneq q 0; first by rewrite eqp0 => /eqP <-.
move=> /andP[]; rewrite !dvdp_mu// => /allP/(_ x) pq /allP/(_ x) qp.
apply/le_anti/andP; split.
  case/boolP: (x \in dec_roots p) pq => [_ //|+ _]; first by apply.
  by rewrite mem_dec_roots p0/= => /muNroot ->.
case/boolP: (x \in dec_roots q) qp => [_ //|+ _]; first by apply.
by rewrite mem_dec_roots q0/= => /muNroot ->.
Qed.

Lemma mu_gcdp (F : closedFieldType) (p q : {poly F}) (x : F) :
  p != 0 -> q != 0 ->
  \mu_x (gcdp p q) = minn (\mu_x p) (\mu_x q).
Proof.
wlog: p q / (\mu_x p <= \mu_x q)%N => pq.
  case/orP: (leq_total (\mu_x p) (\mu_x q)).
    exact/pq.
  by rewrite minnC (mu_eqp _ (gcdpC _ _)) => + /[swap]; apply/pq.
rewrite (minn_idPl pq) => p0 q0.
apply/esym/eqP; rewrite -muP//; last first.
  by rewrite gcdp_eq0 (negPf p0).
by rewrite !dvdp_gcd root_mu root_muN// root_le_mu// pq.
Qed.

Lemma gcdp_mul (F : closedFieldType) (p q : {poly F}) :
  p != 0 -> q != 0 ->
  gcdp p q %= \prod_(x <- dec_roots p) ('X - x%:P) ^+ (minn (\mu_x p) (\mu_x q)).
Proof.
move=> p0 q0.
have pq0 : gcdp p q != 0 by rewrite gcdp_eq0 (negPf p0).
have pq0' : \prod_(x <- dec_roots p) ('X - x%:P) ^+ minn (\mu_x p) (\mu_x q) != 0.
  rewrite prodf_seq_neq0; apply/allP => x _ /=.
  by rewrite expf_eq0 polyXsubC_eq0 andbF.
by apply/andP; split; rewrite dvdp_mu//; apply/allP => x _;
  rewrite mu_gcdp// mu_prod//;
  under eq_bigr do rewrite mu_exp mu_XsubC mulnbl eq_sym;
  rewrite -big_mkcond/= big_pred1_seq// ?uniq_dec_roots//;
  case: ifP => //; rewrite mem_dec_roots p0 => /= /negP/negP /muNroot ->;
  rewrite min0n.
Qed.

Lemma mu_deriv (F : idomainType) x (p : {poly F}) :
  (((\mu_x p)%:R : F) != 0)%R -> \mu_x (p^`()) = (\mu_x p).-1.
Proof.
move=> px0; have [-> | nz_p] := eqVneq p 0; first by rewrite derivC mu0.
have [q nz_qx Dp] := mu_spec x nz_p.
case Dm: (\mu_x p) => [|m]; first by rewrite Dm eqxx in px0.
rewrite Dp Dm !derivCE exprS mul1r mulrnAr -mulrnAl mulrA -mulrDl.
rewrite cofactor_XsubC_mu // rootE !(hornerE, hornerMn) subrr mulr0 add0r.
by rewrite -mulr_natr mulf_neq0// -Dm.
Qed.

Lemma leq_predn n m : (n <= m)%N -> (n.-1 <= m.-1)%N.
Proof.
case: n => [//|n]; case: m => [//|m].
by rewrite !succnK ltnS.
Qed.

Lemma size_deriv [F : idomainType] (p : {poly F}) :
  [char F] =i pred0 -> size p^`() = (size p).-1.
Proof.
move=> /charf0P F0.
have [->|p0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
apply/le_anti/andP; split.
  by rewrite -[X in (X <= _)%O]succnK; apply/leq_predn/lt_size_deriv.
case: (posnP (size p).-1) => [-> //|] p0'.
rewrite -(prednK p0'); apply/gt_size; rewrite coef_poly.
rewrite (prednK p0') leqnn -mulr_natr mulf_eq0 negb_or.
by rewrite -lead_coefE lead_coef_eq0 p0 F0 -lt0n.
Qed.

Lemma dvdp_prod (A : idomainType) (I : Type) (r : seq I) (P : pred I) (F G : I -> {poly A}) :
  (forall i, P i -> F i %| G i) ->
  \prod_(i <- r | P i) F i %| \prod_(i <- r | P i) G i.
Proof.
move=> FG; elim: r => [|i r IHr]; first by rewrite !big_nil dvd1p.
rewrite !big_cons; case/boolP: (P i) => [Pi|//].
by apply/dvdp_mul => //; apply/FG.
Qed.

Lemma divp_prod_dvdp (A : fieldType) (I : Type) (r : seq I) (P : pred I) (F G : I -> {poly A}) :
  (forall i, P i -> G i %| F i) ->
  \prod_(i <- r | P i) F i %/ \prod_(i <- r | P i) G i = \prod_(i <- r | P i) (F i %/ G i).
Proof.
move=> FG; elim: r => [|i r IHr]; first by rewrite !big_nil divp1.
rewrite !big_cons; case/boolP: (P i) => [Pi|//].
rewrite -divp_divl mulrC -divp_mulA ?FG// mulrC -divp_mulA ?IHr//.
exact/dvdp_prod.
Qed.

Lemma subn_pred n m : (0 < m)%N -> (m <= n)%N -> (n - m.-1)%N = (n - m).+1.
Proof.
case: m => [//|m _]; case: n => [//|n].
by rewrite ltnS succnK subSS => /subSn.
Qed.

Lemma size_dec_roots (F : closedFieldType) (p : {poly F}) :
  [char F] =i pred0 ->
  size (dec_roots p) = (size (p %/ gcdp p p^`())).-1.
Proof.
move=> F0.
have /= [->|p0] := eqVneq p 0.
  rewrite div0p size_poly0/=.
  case rE : (dec_roots 0) => [//|x r].
  have: x \in (dec_roots 0) by rewrite rE mem_head.
  by rewrite mem_dec_roots eqxx.
have [p'0|p'0] := eqVneq p^`() 0.
  rewrite p'0 gcdp0 divpp// size_polyC oner_neq0/=.
  have /size1_polyC ->: (size p <= 1)%N.
    move: (size_deriv p F0); rewrite p'0 size_poly0.
    by case: (size p) => [//|]; case.
  case rE: (dec_roots _) => [//|x r].
  by move: (mem_head x r); rewrite -rE mem_dec_roots rootC polyC_eq0 andNb.
rewrite (eqp_size (eqp_divr p (gcdp_mul p0 p'0))).
move: (dec_roots_closedP p) => pE.
rewrite {2}pE -lead_coefE divpZl size_scale ?lead_coef_eq0//.
rewrite divp_prod_dvdp; last first.
  move=> x _.
  rewrite root_le_mu; last by rewrite expf_eq0 polyXsubC_eq0 andbF.
  by rewrite mu_exp mu_XsubC eqxx mul1n geq_minl.
rewrite big_seq_cond.
under eq_bigr => x.
  rewrite andbT mem_dec_roots => /andP[_] px.
  rewrite -expp_sub ?polyXsubC_eq0// ?geq_minl//.
  rewrite mu_deriv; last first.
    rewrite (proj1 (charf0P _) F0) mu_eq0// px//.
  rewrite (minn_idPr (leq_pred _)) subn_pred// ?mu_gt0// subnn expr1.
over.
rewrite -big_seq_cond size_prod_seq; last first.
  by move=> x _; rewrite polyXsubC_eq0.
under eq_bigr do rewrite size_XsubC.
rewrite big_const_seq count_predT iter_addn_0 subSKn.
by rewrite mul2n subDnAC// subnn.
Qed.

Lemma dec_roots0 (F : decFieldType) : (@dec_roots F 0) = [::].
Proof.
case rE: (dec_roots 0) => [//|x r].
by move: (mem_head x r); rewrite -rE mem_dec_roots eqxx.
Qed.

Lemma const_roots n (P : {fset {poly {mpoly R[n]}}}) (s : {SAset R^n}) :
  SAconnected s ->
  {in P, forall p, {in s &, forall x y, size (evalpmp x p) = size (evalpmp y p)}} ->
  {in P, forall p, {in s &, forall x y, size (gcdp (evalpmp x p) (evalpmp x p)^`()) = size (gcdp (evalpmp y p) (evalpmp y p)^`())}} ->
  {in P &, forall p q, {in s &, forall x y, size (gcdp (evalpmp x p) (evalpmp x q)) = size (gcdp (evalpmp y p) (evalpmp y q))}} ->
  {in s &, forall x y, size (rootsR (evalpmp x (\prod_(p : P) (val p)))) = size (rootsR (evalpmp y (\prod_(p : P) (val p))))}.
Proof.
case: n P s => [|n] P s Scon psize proots pqsize x y xS yS.
  by have ->: x = y by apply/rowP => -[].
case: (eqVneq (evalpmp x (\prod_(p : P) val p)) 0) => px0.
  rewrite px0; congr (size (rootsR _)).
  move: px0; rewrite !evalpmp_prod => /eqP/prodf_eq0/= [p] _.
  rewrite -size_poly_eq0 => px0.
  apply/esym/eqP/prodf_eq0; exists p => //.
  by rewrite -size_poly_eq0 (psize _ (fsvalP p) y x yS).
have p0: {in P, forall p, {in s, forall x, size (evalpmp x p) != 0}}.
  move=> p pP z zS; rewrite (psize _ pP z x zS xS) size_poly_eq0.
  by move: px0; rewrite evalpmp_prod => /prodf_neq0/(_ [` pP] isT).
apply/(mulrIn (@oner_neq0 R)) => {px0}.
have rE (u : 'rV[R]_n.+1) :
  (size (rootsR (evalpmp u (\prod_(p : P) \val p))))%:R = SAcomp (SAnbroots _) (SAevalpmp (\prod_(p : P) \val p)) u ord0 ord0.
  rewrite SAcompE/= SAevalpmpE SAnbrootsE mxE.
  congr (size (rootsR _))%:R.
  apply/polyP => i; rewrite coef_poly.
  case: ltnP => ilt; last first.
    exact/nth_default/(leq_trans (size_poly _ _) ilt).
  by rewrite -/(nat_of_ord (Ordinal ilt)) nth_map_ord mxE.
rewrite !rE; congr (_ _ ord0 ord0).
move: x y xS yS; apply/SAconnected_locally_constant_constant => // x.
rewrite inE/= => xs.
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
split; first exact/open_subspaceW/ball_open.
split; first by rewrite inE; apply ballxx.
move=> y; rewrite in_setI => /andP[]; rewrite inE/= => ys.
rewrite -ball_normE inE/= lt_bigmin => /andP[_] /allP/= xy.
apply/eqP; rewrite rowPE forall_ord1 -!rE eqr_nat; apply/eqP.
pose rs := fun x => [fset x in (rootsR (evalpmp x (\prod_(p : P) \val p)))].
have card_rs : forall x, #|` rs x | = size (rootsR (evalpmp x (\prod_(p : P) \val p))).
  by move=> z; rewrite /rs card_imfset//= undup_id// uniq_roots.
rewrite -!card_rs.
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
have R0: [char R[i]] =i pred0 by apply/charf0P => i; rewrite pnatr_eq0.
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
  suff: (`|(val u - val (fxy p u)) - (val v - val (fxy p v))| < 2 * d)%R.
    by rewrite opprB addrC addrCA addrAC uv subrr add0r.
  apply/(le_lt_trans (ler_normB _ _)).
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
  - by move: (fsvalP gyx.[lift p y u ys]); rewrite (mem_imfset _ _ (@inj_id _))/=.
  - by move: (lift p x (fyx p u) xs); rewrite (mem_imfset _ _ (@inj_id _))/=.
  suff: `|(val u - val gyx.[lift p y u ys]) - (val u - val (fyx p u))| < (2 * d)%R.
    by rewrite opprB addrCA addrAC subrr add0r -normrN opprB.
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
  have: (`|(u - a) - (u - b)| < 2 * d)%R.
    apply/(le_lt_trans (ler_normB _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD.
  rewrite opprB addrAC addrCA subrr addr0 => /dP -> //.
    rewrite mem_dec_roots pcM0//= root_bigmul.
    apply/hasP; exists p => //; apply/mem_index_enum.
  rewrite mem_dec_roots pcM0//= root_bigmul.
  by apply/hasP; exists p => //; apply/mem_index_enum.
have mu_gyx p (u : [fset x | x in dec_roots (\prod_p pc p y)]) :
    \mu_(val (gyx u)) (pc p x) = \mu_(val u) (pc p y).
  move: (psize (val p) (fsvalP p) x y xs ys).
  move: (size_pc (pc p x)) (size_pc (pc p y)).
  rewrite !size_map_poly => -> ->.
  rewrite pc0.


have gxyK: cancel gxy gyx.
  move=> u; apply/val_inj/dP.
  - by move: (fsvalP (gyx (gxy u))); rewrite (mem_imfset _ _ (@inj_id _))//.
  - by move: (fsvalP u); rewrite (mem_imfset _ _ (@inj_id _))//.
    suff: (`|(val u - val (gxy u)) + (val (gxy u) - val (gyx (gxy u)))| < 2 * d)%R.
      rewrite -[(`|_ - _|)%R]normrN opprB; congr (normr _ < _).
      by rewrite addrC addrCA addrAC subrr add0r.
  apply/(le_lt_trans (ler_normD _ _)).
  rewrite mulr2n mulrDl mul1r; apply/ltrD; first exact/gxyd.
  exact/gyxd.
have gyxK: cancel gyx gxy.
  move=> v; apply/val_inj; move: (gyx v) (gyxd v) => u vud.
  case: (unlift y v) (gxy u) (gxyd u) => p pv w uw.
  case: (unlift y w) => q qw.
  case: u v vud => /= u.
  rewrite mem_imfset/= => pu; last by [].
  case=> /= v; rewrite mem_imfset/=; last by [].
  rewrite mem_dec_roots root_bigmul => /andP[_] /hasP/= [] p _ pv vu.
  case=> /= w; rewrite mem_imfset/=; last by [].
  rewrite mem_dec_roots root_bigmul => /andP[_] /hasP/= [] q _ qw uw.
  case: (fxy_bij p) => gp fpK gpK.
  case: (fxy_bij q) => gq fqK gqK.
  apply/eqP; rewrite -[_ == _]negbK; apply/negP => wv.
  move: (pqsize (val p) (val q) (fsvalP p) (fsvalP q) x y xs ys).
  move: (size_pc (gcdp (pc p x) (pc q x))) (size_pc (gcdp (pc p y) (pc q y))).
  rewrite !gcdp_eq0 !negb_and !pc0//= !addn1 -!gcdp_map !size_map_poly => -> -> /eqP.
  rewrite eqSS !gcdp_map -!/(pc _ _) => /eqP.
  under eq_bigr do rewrite mu_gcdp ?pc0//.
  under [in RHS]eq_bigr do rewrite mu_gcdp ?pc0//.
  move=> pq.
  suff: ((\sum_(i <- dec_roots (gcdp (pc p y) (pc q y)))
      minn (\mu_i (pc p y)) (\mu_i (pc q y))) <
    (\sum_(i <- dec_roots (gcdp (pc p x) (pc q x)))
      minn (\mu_i (pc p x)) (\mu_i (pc q x))))%N.
    by rewrite -pq ltnn.
  rewrite -(big_rmcond_in (fun u => has (fun v => `|u - v| < d) (dec_roots (gcdp (pc p x) (pc q x)))))/=; last first.
    move=> a; rewrite mem_dec_roots root_gcd => /andP[_] /andP[] pa qa.
    rewrite -all_predC => /allP.
    have apP: a \in [fset x in dec_roots (pc p y)].
      by rewrite mem_imfset//= mem_dec_roots pc0.
    move=> /(_ (val (gp [` apP]))).
    rewrite mem_dec_roots gcdp_eq0 negb_and !pc0//= root_gcd.
    move: (fsvalP (gp [` apP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
    rewrite mem_dec_roots => /andP[_] -> /=.
    have aqP: a \in [fset x in dec_roots (pc q y)].
      by rewrite mem_imfset//= mem_dec_roots pc0.
    suff ->: val (gp [` apP]) = val (gq [` aqP]).
      move: (fsvalP (gq [` aqP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      rewrite mem_dec_roots => /andP[_] /[swap]/[apply].
      move: (gqK [` aqP]) => /(congr1 val)/= aE.
      by rewrite -{1}aE -normrN opprB fxyd.
    apply/dP.
    - move: (fsvalP (gp [` apP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      rewrite mem_dec_roots => /andP[_] pga.
      rewrite mem_dec_roots pcM0//= root_bigmul.
      apply/hasP => /=; exists p => //; apply/mem_index_enum.
    - move: (fsvalP (gq [` aqP])); rewrite (mem_imfset _ _ (@inj_id _))/=.
      rewrite mem_dec_roots => /andP[_] qga.
      rewrite mem_dec_roots pcM0//= root_bigmul.
      apply/hasP => /=; exists q => //; apply/mem_index_enum.
    suff: (`|(val (gp [` apP]) - val (fxy p (gp [` apP]))) - (val (gq [` aqP]) - val (fxy q (gq [` aqP])))| < 2 * d)%R.
      by rewrite gpK/= gqK/= opprB addrC addrCA addrAC subrr add0r.
    apply/(le_lt_trans (ler_normB _ _)).
    rewrite mulr2n mulrDl mul1r; apply/ltrD; apply/fxyd.
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
    have: (`|(a - b) - (a - c)| < 2 * d)%R.
      apply/(le_lt_trans (ler_normB _ _)).
      by rewrite mulr2n mulrDl mul1r; apply/ltrD.
    rewrite opprB addrAC addrCA subrr addr0 => /dP -> //.
      rewrite mem_dec_roots pcM0//= root_bigmul.
      apply/hasP; exists q => //; apply/mem_index_enum.
    rewrite mem_dec_roots pcM0//= root_bigmul.
    by apply/hasP; exists q => //; apply/mem_index_enum.
  rewrite (bigD1_seq u)/=; first last.
  - exact/uniq_dec_roots.
  - rewrite mem_dec_roots gcdp_eq0 negb_and pc0//= root_gcd.

    rewrite vP -[X in (X <= _)%N]addn0; apply/leq_add => //.
      by rewrite mu_gt0// pc0.
      by move=> w _; apply/dP'.
    apply/leq_sum => v _.
    case/boolP: (root (pc p x) v) => [vx|/muNroot -> //].
    by move: (xd' p) => [_]; apply=> //; apply/xy/mem_index_enum.

    


  Search multiplicity gcdp.
  rewrite -(gcdp_map (meval (tnth (ngraph x)) : {rmorphism {mpoly R[n.+1]} -> R})).
  rewrite /evalpmp. -gcdp_map.
  Check gcdp_map.
  have [pq|pq] := eqVneq q p.
    move: qw pv; rewrite {}pq => {q} pw pv.
    


have fxybij : bijective fxy.
  apply/inj_card_bij => [u v fuv|].
    apply/val_inj/dP.
    - by move: (fsvalP u); rewrite -[fsval u]/(id _) mem_imfset//.
    - by move: (fsvalP v); rewrite -[fsval v]/(id _) mem_imfset//.
    suff: (`|(val u - val (fxy u)) - (val v - val (fxy v))| < 2 * d)%R.
      by congr (normr _ < _); rewrite fuv addrC opprB addrCA addrAC subrr add0r.
    apply/(le_lt_trans (ler_normB _ _)).
    by rewrite mulr2n mulrDl mul1r; apply/ltrD; apply/fxyd.
  rewrite -2!cardfE card_imfset//= card_imfset//=.
  do 2 rewrite undup_id ?uniq_dec_roots//.
  move: (size_dec_roots (pc p x) R0).
  rewrite size_divp; last by rewrite gcdp_eq0 negb_and pc0.
  rewrite deriv_map -gcdp_map/= !size_map_poly.
  rewrite (proots (val p) (fsvalP p) x y xs ys).
  rewrite (psize (val p) (fsvalP p) x y xs ys).
  move: (size_dec_roots (pc p y) R0).
  rewrite size_divp; last by rewrite gcdp_eq0 negb_and pc0.
  rewrite deriv_map -gcdp_map/= !size_map_poly => <- pxy.
  rewrite card_finset.
  Search card Imfset.imfset.
have roots_uniq u v (ux : root (\prod_(p : P) pc p x) u) : root (\prod_(p : P) pc p y) v -> `|u - v| < d ->
    v = sval (has_roots u ux).
  case: (has_roots _ _) => /= w [].
  rewrite !root_bigmul => /hasP/sig2W /= [] p _ wp wu /hasP/sig2W /= [] q _ vq vu.
  
    
    Search bijective card.
    Check bij_eq_card.

    rewrite /pc.
    Search gcdp "morph".
    Search size gcdp (_ %/ _).
    Search size dec_roots.
    
  move=> vy uv; case: (has_roots _ _) => /= w [].
  move: rewrite root_bigmul. wy uw.



    
    Check root_bigmul.
    Search (_ < _ * _)%R (_ / _)%R.
        

    -/(size [:: w.
    Search (count _ _ <= _)%N.



    Search seq.filter has.
  Search bigop orb.
  rewrite size_map_poly => ->.

  rewrite -(size_map_poly (
  rewrite size_scale; last first.
    by rewrite -lead_coefE lead_coef_eq0 map_poly_eq0 -size_poly_eq0; apply/p0 => //; apply/fsvalP.
  rewrite size_prod_seq => /= [| w _]; last first.
    by rewrite expf_eq0 polyXsubC_eq0 andbF.
    Search (size (_ ^+ _)).
  under eq_bigr do rewrite size_
  Search multiplicity bigop size.
have size_pc p z : z \in s -> size (pc p z) = (\sum_(u <- dec_roots (\prod_(p : P) pc p z)) \mu_u (pc p z)).+1.
  move=> zs.
  rewrite (bigID (fun u => root (pc p z) u))/= -[LHS]addn0 -addSn.
  congr (_ + _)%N; last first.
    apply/esym; rewrite big_mkcond/=; apply/big1_idem => //= u _.
    by case /boolP: (root (pc p z) u) => //= /muNroot ->.
  rewrite -big_filter.
  rewrite (perm_big (dec_roots (pc p z)))/=.
    move: (dec_roots_closedP (pc p z)) => /(congr1 (fun p : {poly _} => size p)).
    rewrite size_scale; last by rewrite -lead_coefE lead_coef_eq0 pc0.
    rewrite size_prod_seq => /= [| w _]; last first.
      by rewrite expf_eq0 polyXsubC_eq0 andbF.
    under eq_bigr do rewrite my_size_exp ?polyXsubC_eq0// size_XsubC/= mul1n -addn1.
    by rewrite big_split/= sum1_size -addSn subDnAC// subnn.
  apply/uniq_perm; first exact/filter_uniq/uniq_dec_roots.
    exact/uniq_dec_roots.
  move=> u; rewrite mem_filter !mem_dec_roots.
  apply/andP/andP => [[] zu _|[] _ zu].
    by split=> //; apply/pc0.
  split=> //; apply/andP; split.
    by apply/prodf_neq0 => /= q _; apply/pc0.
  rewrite root_bigmul/=; apply/hasP => /=.
  by exists p => //; apply/mem_index_enum.

apply/(bij_eq_card (f:=fun u => [arg min_(v < 
Print Order.arg_min.
Search "arg_min".

Check    bij_eq_card.


Definition elimp_subdef1 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : P) truncations (muni (val p)).

Definition elimp_subdef2 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P | (3 <= size (val p))%N)
      [fset subresultant (val j) (val p) (val p)^`() | j : 'I_(size (val p)).-2].

Definition elimp_subdef3 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P)
    \big[fsetU/fset0]_(q : elimp_subdef1 P | (size (val q) < size (val p))%N)
      [fset subresultant (val j) (val p) (val q) | j : 'I_(size (val q)).-1].

Definition elimp_subdef4 n (P : {fset {mpoly R[n.+1]}}) :=
  \big[fsetU/fset0]_(p : elimp_subdef1 P)
    \big[fsetU/fset0]_(q : elimp_subdef1 P | (size (val q) == size (val p))%N)
      let q := lead_coef (val p) *: (val q) - lead_coef (val q) *: (val p) in
      [fset subresultant (val j) (val p) (val q)  | j : 'I_(size (val q)).-1].

Definition elimp_subdef5 n (P : {fset {mpoly R[n.+1]}}) :=
  [fset lead_coef (val p) | p : elimp_subdef1 P].

Definition elimp n (P : {fset {mpoly R[n.+1]}}) :=
  [fset p : elimp_subdef2 P `|` elimp_subdef3 P `|` elimp_subdef4 P `|` elimp_subdef5 P | msize (val p) != 0].
    

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
    admit. (* continuity *)
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
move=> q; case=> /= s /imfsetP [/=] t /bigfcupP [] {}s _ + ->.
case: (roots2_on (S'const s)) => /= [] r [] rsort rroot.
Search partition_of_graphs_above.
    
      


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

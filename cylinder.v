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

Lemma const_roots n (P : {fset {poly {mpoly R[n]}}}) (s : {SAset R^n}) :
  SAconnected s ->
  {in P, forall p, {in s &, forall x y, size (evalpmp x p) = size (evalpmp y p)}} ->
  {in P, forall p, {in s &, forall x y, size (evalpmp x (gcdp p p^`())) = size (evalpmp y (gcdp p p^`()))}} ->
  {in P &, forall p q, {in s &, forall x y, size (evalpmp x (gcdp p q)) = size (evalpmp y (gcdp p q))}} ->
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
pose pc := fun (x : 'rV[R]_n.+1) => (map_poly [eta real_complex R] (evalpmp x (\prod_(p : P) \val p))).
pose rx := dec_roots (pc x).
pose d := (\big[Order.min/1]_(x <- rx) \big[Order.min/1]_(y <- rx | y != x) complex.Re `|x - y|)%:C%C.
have d0 : 0 < d.
  rewrite ltcE/= eqxx/= lt_bigmin ltr01/=; apply/allP => u _.
  rewrite -big_filter lt_bigmin ltr01/=; apply/allP => v.
  rewrite mem_filter => /andP[] vu _.
  by rewrite -ltcR (normr_gt0 (u - v)) subr_eq0 eq_sym.
case: (aligned_deformed (pc x) d0) => /= [[]] e eI [].
rewrite ltcE/= => /andP[/eqP ->] e0; rewrite complexr0 => ed.
have /fin_all_exists /=: forall i : 'I_(size (pc x)).+1, exists delta, 0 < delta /\ forall (y : 'rV[R]_n.+1), `|x - y| < delta -> `|(pc x)`_i - (pc y)`_i| < (e%:C)%C.
  move=> i.
  move: (@meval_continuous _ _ (\prod_(p : P) \val p)`_i x).
  rewrite /= /continuous_at.
  move=> /(@cvgr_dist_lt _ (GRing_regular__canonical__normedtype_PseudoMetricNormedZmod R)).
  move=> /(_ _ e0) /nbhs_ballP[] d'/= d'0 /subsetP xd'.
  exists d'; split=> // y xy.
  move: xd' => /(_ y); mp; first by rewrite -ball_normE inE/=.
  rewrite inE/= !coef_map/= -rmorphB/= normc_def/= expr0n/= addr0 sqrtr_sqr ltcR.
  by congr (normr (_ - _) < e); apply/meval_eq => j; rewrite tnth_mktuple.
move=> [d'] xd'.
have d'0: 0 < \big[minr/1]_(i < (size (pc x)).+1) d' i.
  rewrite lt_bigmin ltr01; apply/allP => i _ /=.
  by case: (xd' i).
exists (ball x (\big[Order.min/1]_(i < (size (pc x)).+1) d' i)).
split; first exact/open_subspaceW/ball_open.
split; first by rewrite inE; apply ballxx.
move=> y; rewrite in_setI => /andP[]; rewrite inE/= => ys.
rewrite -ball_normE inE/= lt_bigmin => /andP[_] /allP/= xy.
apply/eqP; rewrite rowPE forall_ord1 -!rE eqr_nat; apply/eqP.
have {}/ed pxy: deformp e%:C%C (pc x) (pc y).
  split=> [|i]; last first.
    case: (xd' (lift ord_max i)) => _ /=.
    rewrite /bump leqNgt (ltn_ord i) add0n; apply.
    exact/xy/mem_index_enum.
  suff ->: size (pc y) = size (pc x) by [].
  rewrite !size_map_poly !evalpmp_prod !size_prod/=. 
  - by congr (_.+1 - _)%N; apply/eq_bigr => i _; apply/psize.
  - by move=> p _; rewrite -size_poly_eq0; apply/p0.
  - by move=> p _; rewrite -size_poly_eq0; apply/p0.
rewrite -![rootsR _](undup_id (uniq_roots _ _ _)) -!/(rootsR _).
    Search roots uniq.
    Search size seq_fset.


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

From mathcomp Require Import freeg ssreflect ssrfun ssrbool eqtype choice seq ssrnat bigop tuple fintype finfun path ssralg ssrnum poly matrix finmap mpoly complex.
Require Import semialgebraic.
(* TODO: the following imports should not be needed after cleanup. *)
From mathcomp Require Import generic_quotient.
Require Import formula subresultant.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope type_scope.
Local Open Scope sa_scope.

Import GRing.

Section CylindricalDecomposition.
Variables (R : rcfType).

Definition isCylindricalDecomposition n (S : forall i : 'I_n.+1, {fset {SAset R^i}}) :=
  (forall i : 'I_n.+1, SAset_partition (S i))
  /\ forall (i : 'I_n) (s : S (lift ord_max i)),
    exists m, exists xi : m.-tuple {SAfun R^(lift ord_max i) -> R^1},
      sorted (@SAfun_lt _ _) xi
      /\ [fset s' in S (lift ord0 i) | SAset_cast _ s' == val s] = [fset SAset_cast i.+1 x | x in partition_of_graphs_above (val s) xi].

Local Notation isCD := isCylindricalDecomposition.

Lemma bool_eq_arrow {b b' : bool} : b = b' -> b -> b'.
Proof. by case: b' => // /negP. Qed.

Lemma isCylindricalDecomposition_restrict n m S (mn : m <= n) : isCD n S -> isCD m (fun i => S (widen_ord (bool_eq_arrow (esym (ltnS m n)) mn) i)).
Proof.
move=> [] Spart Scyl; split => [i|i s].
  exact/(Spart ((widen_ord (m:=n.+1) (bool_eq_arrow (esym (ltnS m n)) mn) i))).
move/(_ (widen_ord mn i)) : Scyl.
have ->: lift ord_max (widen_ord mn i) = widen_ord (bool_eq_arrow (esym (ltnS m n)) mn) (lift ord_max i).
  by apply/val_inj; rewrite /= /bump leqNgt (leq_trans (ltn_ord i) mn) leqNgt ltn_ord.
move=> /(_ s) [k][xi][xisort] /= partE.
exists k, xi; split; first by [].
rewrite -partE.
congr [fset _ in _ | _]; congr (mem_fin (fset_finpred (S (Ordinal _)))).
exact/bool_irrelevance.
Qed.

Definition poly_invariant n (p : {mpoly R[n]}) (s : {SAset R^n}) :=
  {in s &, forall x y, let x := meval (tnth (ngraph x)) p in let y := meval (tnth (ngraph y)) p in (x / `|x| = y / `|y|)%R}.

Definition poly_adapted n p (S : forall i : 'I_n.+1, {fset {SAset R^i}}) := forall s : S ord_max, poly_invariant n p (val s).

Definition truncate (T : ringType) (p : {poly T}) (d : nat) :=
  (\poly_(i < size p) (p`_i *+ (i < d)%N))%R.

Definition truncations n (p : {poly {mpoly R[n]}}) : {fset {poly {mpoly R[n]}}} :=
  (fix F p n :=
    match n with
    | 0 => [fset p]
    | n.+1 => if 0 < mdeg (mlead (lead_coef p)) then
        p |` F (truncate _ p (size p).-1) n
      else [fset p]
    end) p (size p).

Definition elim_subdef0 n (P : {fset {poly {mpoly R[n]}}}) :=
  \big[fsetU/fset0]_(p : P) \big[fsetU/fset0]_(r : truncations n (val p))
    (lead_coef (val r) |` [fset subresultant (val j) (val r) (val r)^`() | j in 'I_(size (val r)).-2]).

Definition elim_subdef1 n (P : {fset {poly {mpoly R[n]}}}) :=
    \big[fsetU/fset0]_(p : P) \big[fsetU/fset0]_(r : truncations n (val p))
      \big[fsetU/fset0]_(q : P) (\big[fsetU/fset0]_(s : truncations n (val q) | size (val s) < size (val r))
        (([fset subresultant (val j) (val r) (val s) | j in 'I_((size (val s)).-1)] `|` [fset subresultant (val j) (val s) (val r) | j in 'I_((size (val s)).-1)]))
        `|` \big[fsetU/fset0]_(s : truncations n (val q) | size (val s) == size (val r))
          (let rs := ((lead_coef (val s)) *: (val r) - (lead_coef (val r)) *: (val s))%R in
          [fset subresultant (val j) (val s) (val rs) | j in 'I_((size rs).-1)])).

Definition elim n (P : {fset {poly {mpoly R[n]}}}) :=
  [fset x in elim_subdef0 n P `|` elim_subdef1 n P | mdeg (mlead x) != 0].

(* Lemma poly_neigh_decomposition (p q : {poly R[i]}) :
  monic p -> monic q -> coprime p q ->
   exists rho : R, 0 < rho /\ forall P  *)
From mathcomp Require Import polydiv polyrcf.

Definition evalpmp {n} (x : 'rV[R]_n) (P : {poly {mpoly R[n]}}) := map_poly (fun p => p.@[tnth (ngraph x)]) P.

Theorem roots2_on n (P : {fset {poly {mpoly R[n]}}}) (rP : P -> nat) (s : {SAset R^n}) :
  SAset_path_connected s
  -> {in P, forall p, {in s, forall x, size (evalpmp x p) > 0}}
  -> {in P &, forall p q, {in s &, forall x y, size (gcdp (evalpmp x p) (evalpmp x q)) = size (gcdp (evalpmp y p) (evalpmp y q))}}
  -> (forall p, {in s, forall x, size (rootsR (evalpmp x (val p))) = rP p})
  -> { xi : seq {SAfun R^n -> R^1} | sorted (@SAfun_lt R n) xi /\ {in s, forall x, perm_eq [seq (xi : {SAfun R^n -> R^1}) x ord0 ord0 | xi <- xi] (rootsR (\prod_(p : P) (evalpmp x (val p))))}}.
Proof.
case: (set0Vmem s) => [-> {s}|[x xs]] spc psize gsize proots.
  by exists [::]; split=> // x; rewrite inSAset0.
have: {in s, forall y, size (rootsR (evalpmp y (\prod_(p : P) (val p)))) = size (rootsR (evalpmp x (\prod_(p : P) (val p))))}.
  move=> y ys; move/(_ x y xs ys): spc => [g][<- <-] {x xs y ys}.
  apply/eqP/negP => /negP.


Theorem cylindrical_decomposition n (P : {fset {mpoly R[n]}}) :
  { S | isCD n S /\ forall p : P, poly_adapted n (val p) S}.
Proof.
elim: n P => [|n IHn] P.
  exists (fun i => [fset SAsetT R i]); split=> [|[] p /= _]; last first.
    case=> _ /= /fset1P -> x y _ _.
    suff ->: x = y by [].
    by apply/matrixP => i; case.
  split=> [[]|[]//]; case=> /= [|//] _.
  apply/andP; split; last by rewrite big_fset1/= eqxx.
  apply/andP; split.
    apply/negP; move=> /fset1P/eqP/SAsetP /(_ (\row_i 0)%R).
    by rewrite inSAset0 inSAsetT.
  do 2 (apply/forallP; case => i /= /fset1P -> {i}).
  by rewrite eqxx.
move: IHn => /(_ (elim n [fset muni p | p in P])) [S0 [S0CD S0p]].
simple refine (exist _ _ _).
  case=> i /=; rewrite ltnS leq_eqVlt.
  case /boolP: (i == n.+1) => [/eqP -> _|_ /= ilt]; last exact: (S0 (Ordinal ilt)).



  Search (_ <= _.+1).
  case/boolP: (val i == n.+1); last first.
case: (split (cast_ord (esym (addn1 n.+1)) i)).
  exact S0.
    
    
Admitted.


End CylindricalDecomposition.

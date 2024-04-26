From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq ssrnat bigop fintype tuple order ssralg ssrnum poly polydiv complex polyorder.
From mathcomp Require Import matrix topology normedtype signed classical_sets.
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope complex_scope.
Local Open Scope classical_set_scope.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory Num.Def complex.

Lemma sum1_ord (n : nat) :
  (\sum_(i < n) 1)%N = n.
Proof. by rewrite big_const_ord iter_addn_0 mul1n. Qed.

Lemma iotanS (n m : nat) :
  iota n m.+1 = rcons (iota n m) (n + m)%N.
Proof.
elim: m n => /= [|m IHm] n; first by rewrite addn0.
by rewrite IHm addSn addnS.
Qed.

Lemma ler_p1X (R : numDomainType) (x y : R) (n m : nat) :
  1 <= x -> x <= y -> (n <= m)%N -> x ^+ n <= y ^+ m.
Proof.
move=> x1 xy nm; apply/(le_trans (y:=x ^+ m)).
  by rewrite -(subnK nm) exprD ler_peMl// ?exprn_ege1// exprn_ge0// (le_trans ler01 x1).
elim: m {n nm} => [|n IHn]; first by rewrite !expr0.
by rewrite !exprS ler_pM// (le_trans ler01)// exprn_ege1.
Qed.

Lemma sumr_gt0 (R : numDomainType) (I : Type) (r : seq I) 
         (P : pred I) (F : I -> R):
  (forall i : I, P i -> 0 <= F i)
  -> has (fun i => P i && (0 < F i)) r
  -> 0 < \sum_(i <- r | P i) F i.
Proof.
move=> F0; elim: r => [//|] i r IHr /= /orP; case=> [/andP[Pi Fi]|/IHr {}IHr].
  by rewrite big_cons Pi; apply/(lt_le_trans Fi); rewrite lerDl sumr_ge0.
by rewrite big_cons; case/boolP: (P i) => // Pi; apply/(lt_le_trans IHr); rewrite lerDr F0.
Qed.

Lemma psumr_gt0 (R : numDomainType) (I : Type) (r : seq I) 
         (P : pred I) (F : I -> R):
  (forall i : I, P i -> 0 < F i)
  -> has P r
  -> 0 < \sum_(i <- r | P i) F i.
Proof.
move=> F0 Pr; apply/sumr_gt0 => [i /F0 /ltW //|].
elim: r Pr => [//|] i r IHr /= /orP; case=> [Pi|/IHr -> //]; last by rewrite orbT.
by rewrite Pi F0.
Qed.

Lemma big_ord_iota [R : Type] (idx : R) (op : Monoid.law idx) (n : nat) (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < n | P i) F i = \big[op/idx]_(i <- iota 0 n | P i) F i.
Proof.
elim: n P F => [|n IHn] P F; first by rewrite big_ord0 big_nil.
rewrite [LHS]big_mkcond big_ord_recr iotanS.
rewrite -cats1 big_cat big_cons big_nil add0n Monoid.mulm1/=; congr (op _ _).
by rewrite -big_mkcond IHn.
Qed.

(* Lemma rdivpP (R : ringType) (p d q r : {poly R}) (k : nat) :
  (size r < size d)%N ->
  let kp := Pdiv.CommonRing.rscalp p d in
  let qp := Pdiv.CommonRing.rdivp p d in
  let rp := Pdiv.CommonRing.rmodp p d in
  (lead_coef d ^+ k *: p == q * d + r) = ((kp <= k)%N && (q == lead_coef d ^+ (k-kp)%N *: qp) && (r == lead_coef d ^+ (k-kp)%N *: rp)).
Proof.


Lemma mu_div (R : idomainType) (p q : {poly R}) (x : R) :
  q != 0 -> \mu_x (p %/ q) = (\mu_x p - \mu_x q)%N.
Proof.
move=> /(mu_spec x) [q'] qx {1}->.
have [->|/(mu_spec x) [p'] px {1}->] := eqVneq p 0; first by rewrite div0p mu0 sub0n.
case: (ltnP (\mu_x p) (\mu_x q)) => pq.
Print Pdiv.CommonRing.
Search "divp" "P" (_ %/ _).
Locate Pdiv.IdomainMonic.mulpK.
  rewrite -{1}(subnK (ltnW pq)) exprD mulrA Pdiv.IdomainUnit.divp_pmul2r.
Search ((_ * _) %/ (_ * _)).


  Search (0 %
Check mu_spec.
 *)

Lemma mu_XsubC (R : idomainType) (x y : R) :
  \mu_x ('X - y%:P) = (x == y).
Proof.
have [->|xy] := eqVneq x y; first exact: mu_XsubC.
by rewrite muNroot// root_XsubC.
Qed.

Lemma eq_continuous_at {T S : topologicalType} (f g : T -> S) (x : T) :
  f =1 g -> continuous_at x f -> continuous_at x g.
Proof. by move=> fg; rewrite /continuous_at fg (eq_cvg _ _ fg). Qed.

Lemma eq_continuous {T S : topologicalType} (f g : T -> S) :
  f =1 g -> continuous f -> continuous g.
Proof. by move=> fg f_cont x; exact/(eq_continuous_at fg). Qed.

Lemma expn_continuous {K : numFieldType} (n : nat) :
  continuous (fun x : K => x ^+ n).
Proof.
elim: n => [|n IHn]; first exact/cst_continuous.
apply/(eq_continuous (f:=fun x : K => x * x ^+ n)) => x.
  by rewrite exprS.
by apply/(@continuousM _ _ _ _ x) => //; apply/IHn.
Qed.

Lemma cvgX {K : numFieldType} {T : Type} [F : set_system T] :
  Filter F ->
  forall (f : T -> K) (n : nat) (a : K),
  cvg_to (nbhs (fmap f (nbhs F))) (nbhs a) ->
  cvg_to (nbhs (fmap ((fun x => x ^+ n) \o f) (nbhs F))) (nbhs (a ^+ n)).
Proof.
move=> FF f n a fa.
by apply: continuous_cvg => //; apply/expn_continuous.
Qed.

Lemma continuousX [K : numFieldType] [T : topologicalType] (s : T -> K) (n : nat) (x : T) :
  {for x, continuous s} -> {for x, continuous (fun x => s x ^+ n)}.
Proof. by move=> f_cont; apply: cvgX. Qed.

Lemma lift_inord (n : nat) (i : 'I_n) :
  lift ord0 i = inord i.+1.
Proof. by apply/val_inj; rewrite /= inordK ?ltnS. Qed.

(* N.B. I do not need a numFieldType. *)
Lemma cvg_big {K : topologicalType} {T : Type} [F : set_system T] [I : Type] (r : seq I) (P : pred I) (Ff : I -> T -> K) (Fa : I -> K) (op : K -> K -> K) (x0 : K):
  Filter F ->
  (forall (f g : T -> K) (a b : K),
    cvg_to (nbhs (fmap f (nbhs F))) (nbhs a) ->
    cvg_to (nbhs (fmap g (nbhs F))) (nbhs b) ->
    cvg_to (nbhs (fmap (fun x => op (f x) (g x)) (nbhs F))) (nbhs (op a b))) ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \big[op/x0]_(i <- r | P i) (Ff i x))) (nbhs F))) (nbhs (\big[op/x0]_(i <- r | P i) Fa i)).
Proof.
move=> FF cvg_op cvg_f.
elim: r => [|x r IHr].
  rewrite big_nil (eq_cvg _ _ (fun x => big_nil _ _ _ _)).
  exact: cvg_cst.
rewrite big_cons (eq_cvg _ _ (fun x => big_cons _ _ _ _ _ _)).
case/boolP: (P x) => // Px.
apply/cvg_op => //.
exact/cvg_f.
Qed.

Lemma continuous_big [K T : topologicalType] [I : Type] (r : seq I) (P : pred I) (F : I -> T -> K) (op : K -> K -> K) (x0 : K) (x : T) :
  continuous (fun x : K * K => op x.1 x.2) ->
  (forall i, P i -> {for x, continuous (F i)}) ->
  {for x, continuous (fun x => \big[op/x0]_(i <- r | P i) F i x)}.
Proof.
move=> op_cont f_cont.
apply: cvg_big => // f g a b fa gb.
rewrite (eq_cvg _ (g:=(fun x => op x.1 x.2) \o (fun x => (f x, g x))))//.
apply: (cvg_comp (G:=nbhs (a, b))); first exact: cvg_pair.
exact: (op_cont (a, b)).
Qed.

Lemma cvg_sum {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type} [F : set_system T] [I : Type] (r : seq I) (P : pred I) (Ff : I -> T -> V) (Fa : I -> V):
  Filter F ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \sum_(i <- r | P i) (Ff i x))) (nbhs F))) (nbhs (\sum_(i <- r | P i) Fa i)).
Proof.
move=> FF fa.
apply/(cvg_big FF) => // f g a b {}fa gb.
exact: cvgD.
Qed.

Lemma continuous_sum {K : numFieldType} {V : pseudoMetricNormedZmodType K} [T : topologicalType] [I : Type] (r : seq I) (P : pred I) (F : I -> T -> V) (x : T) :
  (forall i, P i -> {for x, continuous (F i)}) ->
  {for x, continuous (fun x => \sum_(i <- r | P i) F i x)}.
Proof.
move=> f_cont.
apply: continuous_big => //=.
exact: add_continuous.
Qed.

Lemma cvg_prod {K : numFieldType} {T : Type} [F : set_system T] [I : Type] (r : seq I) (P : pred I) (Ff : I -> T -> K) (Fa : I -> K):
  Filter F ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \prod_(i <- r | P i) (Ff i x))) (nbhs F))) (nbhs (\prod_(i <- r | P i) Fa i)).
Proof.
move=> FF fa.
apply/(cvg_big FF) => // f g a b {}fa gb.
exact: cvgM.
Qed.

Lemma continuous_prod {K : numFieldType} [T : topologicalType] [I : Type] (r : seq I) (P : pred I) (F : I -> T -> K) (x : T) :
  (forall i, P i -> {for x, continuous (F i)}) ->
  {for x, continuous (fun x => \prod_(i <- r | P i) F i x)}.
Proof.
move=> f_cont.
apply: continuous_big => //=.
exact: mul_continuous.
Qed.

Lemma mu_prod [R : idomainType] (I : Type) (s : seq I) (P : pred I) (F : I -> {poly R}) (x : R) :
  \prod_(i <- s | P i) F i != 0 -> \mu_x (\prod_(i <- s | P i) F i) = \sum_(i <- s | P i) \mu_x (F i).
Proof.
elim: s => [|p s IHs].
  rewrite !big_nil => _; apply/muNroot/root1.
rewrite !big_cons; case: (P p) => // ps0.
by rewrite mu_mul//; move: ps0; rewrite mulf_eq0 negb_or => /andP[] p0 s0; rewrite IHs.
Qed.

(* What is the root_bigmul in mathcomp??? *)
Lemma root_bigmul [R : idomainType] [I : Type] (x : R) (s : seq I) (P : pred I) (F : I -> {poly R}) :
  root (\prod_(i <- s | P i) F i) x = has (fun i : I => P i && root (F i) x) s.
Proof.
elim: s => [|y s IHs]; first by rewrite big_nil (negPf (root1 _)).
by rewrite big_cons/=; case: (P y) => //; rewrite rootM IHs.
Qed.

Definition dec_roots (F : decFieldType) (p : {poly F}) : seq F :=
  if p == 0 then [::] else
  [seq x <- undup (projT1 (dec_factor_theorem p)) | root p x].

Lemma uniq_dec_roots (F : decFieldType) (p : {poly F}) :
  uniq (dec_roots p).
Proof. by rewrite /dec_roots; case: (p == 0) => //; apply/filter_uniq/undup_uniq. Qed.

Lemma mem_dec_roots (F : decFieldType) (p : {poly F}) x :
  x \in dec_roots p = (p != 0) && (root p x).
Proof.
rewrite /dec_roots.
have [->|p0]/= := eqVneq p 0 => //.
rewrite /dec_roots mem_filter; apply/andP/idP => [[]//|px].
split=> //; rewrite mem_undup.
case: (dec_factor_theorem p) => s [q]/= [pE] qroot.
move: p0 px; rewrite pE rootM root_bigmul.
have [->|/qroot {}qroot _] := eqVneq q 0; first by rewrite mul0r eqxx.
rewrite (negPf (qroot _)) => /= /hasP [y] ys.
by rewrite root_XsubC => /eqP ->.
Qed.

Lemma dec_rootsP (F : decFieldType) (p : {poly F}) :
  exists q : {poly F}, p = (q * \prod_(x <- dec_roots p) ('X - x%:P) ^+ (\mu_x p))%R /\ (q != 0 -> forall x : F, ~~ root q x).
Proof.
rewrite /dec_roots.
have [->|p0] := eqVneq p 0.
  by exists 0; rewrite mul0r eqxx.
case: (dec_factor_theorem p) => s [q]/= [pE] qroot.
exists q; move: pE p0; have [->|/[dup] q0 /qroot {}qroot pE p0] := eqVneq q 0.
  by rewrite !mul0r => ->.
split=> //.
rewrite big_filter big_mkcond/= {1}pE -prodr_undup_exp_count; congr (_ * _).
apply/eq_big_seq => x; rewrite mem_undup => xs.
have ->: root p x.
  rewrite pE rootM (negPf (qroot x)) root_bigmul; apply/hasP; exists x => //=.
  by rewrite root_XsubC.
congr (_ ^+ _).
rewrite pE mu_mul; last first.
  rewrite mulf_eq0 negb_or (negPf q0)/= prodf_seq_neq0; apply/allP => y _ /=.
  by rewrite polyXsubC_eq0.
rewrite muNroot// add0n mu_prod; last first.
  rewrite prodf_seq_neq0; apply/allP => y _ /=.
  by rewrite polyXsubC_eq0.
rewrite -sum1_count big_mkcond/=; apply/eq_bigr => y _.
by rewrite mu_XsubC eq_sym; case: (x == y).
Qed.

Lemma lead_coef_prod (R : idomainType) (I : Type) (r : seq I) (P : pred I) (F : I -> {poly R}) :
  lead_coef (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) lead_coef (F i).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil lead_coef1.
rewrite !big_cons; case: (P i) => //.
by rewrite lead_coefM IHr.
Qed.

Lemma dec_roots_closedP (F : closedFieldType) (p : {poly F}) :
  p = p`_(size p).-1 *: \prod_(x <- dec_roots p) ('X - x%:P) ^+ (\mu_x p).
Proof.
have [->|p0] := eqVneq p 0; first by rewrite coef0 scale0r.
move: (dec_rootsP p) => [q].
have [->|q0 [pE]/(_ isT) qr] := eqVneq q 0; first by rewrite mul0r => [][p0']; move/eqP: p0.
have [sq|/closed_rootP [x]] := eqVneq (size q) 1; last by move/negP: (qr x).
have /size1_polyC qE : (size q <= 1)%N by rewrite sq.
rewrite {1}pE qE mul_polyC; congr (_ *: _).
move/(congr1 lead_coef): pE.
rewrite lead_coefM lead_coef_prod.
under eq_bigr do rewrite lead_coef_exp lead_coefXsubC expr1n.
by rewrite big_const_idem/= ?mulr1// qE lead_coefC lead_coefE coefC/=.
Qed.

Lemma gt_size (R : semiRingType) (p : {poly R}) (n : nat) :
  p`_n != 0 -> (n < size p)%N.
Proof.
by rewrite ltnNge => /eqP pn; apply/negP => /leq_sizeP/(_ n (leqnn _)).
Qed.

Lemma prodr_const_seq (R : semiRingType) (I : Type) (r : seq I) (x : R) :
  \prod_(i <- r) x = x ^+ (size r).
Proof.
elim: r => [|y r IHr].
  by rewrite big_nil expr0. 
by rewrite big_cons IHr/= exprS.
Qed.

Lemma bigmin_le {disp : unit} {T : orderType disp} (I : Type) (r : seq I) (x : T) (P : pred I) (F : I -> T) (y : T) :
  (\big[Order.min/x]_(i <- r | P i) F i <= y)%O = (x <= y)%O || has (fun i => P i && (F i <= y)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
by rewrite ge_min IHr !orbA; congr (_ || _); apply/orbC.
Qed.

Lemma bigmin_lt {disp : unit} {T : orderType disp} (I : Type) (r : seq I) (x : T) (P : pred I) (F : I -> T) (y : T) :
  (\big[Order.min/x]_(i <- r | P i) F i < y)%O = (x < y)%O || has (fun i => P i && (F i < y)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
by rewrite gt_min IHr !orbA; congr (_ || _); apply/orbC.
Qed.

Lemma le_bigmin {disp : unit} {T : orderType disp} (I : Type) (r : seq I) (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y <= \big[Order.min/x]_(i <- r | P i) F i)%O = (y <= x)%O && all (fun i => P i ==> (y <= F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil andbT.
rewrite big_cons/=; case: (P i) => //=.
by rewrite le_min IHr !andbA; congr (_ && _); apply/andbC.
Qed.

Lemma lt_bigmin {disp : unit} {T : orderType disp} (I : Type) (r : seq I) (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y < \big[Order.min/x]_(i <- r | P i) F i)%O = (y < x)%O && all (fun i => P i ==> (y < F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil andbT.
rewrite big_cons/=; case: (P i) => //=.
by rewrite lt_min IHr !andbA; congr (_ && _); apply/andbC.
Qed.

Lemma le_bigmax {disp : unit} {T : orderType disp} (I : Type) (r : seq I) (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y <= \big[Order.max/x]_(i <- r | P i) F i)%O = (y <= x)%O || has (fun i => P i && (y <= F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
rewrite le_max IHr !orbA; congr (_ || _); exact/orbC.
Qed.

Section ContinuityRoots.
Variable (R : rcfType).

Definition alignp eps (p q : {poly R[i]}) :=
  {in root p, forall u,
        (\sum_(v <- dec_roots q | (`|v - u| < eps)%R) \mu_v q >= \mu_u p)%N}.

Definition deformp eps (p q : {poly R[i]}) :=
  (size q <= size p)%N /\ forall i : 'I_(size p), `|p`_i - q`_i| < eps.

Lemma close_root_deformp (eps : R[i]) (p : {poly R[i]}) : 0 < eps ->
  exists delta : R[i], 0 < delta /\ forall q, deformp delta p q -> forall x, root p x -> exists y, root q y /\ `|x - y| < eps.
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
  exists 1; split=> [//|] q [sq] _ x _; exists x; split; last by rewrite subrr normr0.
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
  rewrite ler_pdivrMr ?ltr0n// mulrBl lerBrDr -lerBrDl [1 * 2]mulr_natr -{2}[2]natr1 -addrA subrr addr0.

  rewrite -[2]divr1 mulf_div mulr1.
  rewrite -[4%N]/(2 * 2)%N mulrnA -[X in _ / X]mulr_natr -mulf_div divff ?pnatr_eq0// mulr1.
  rewrite -mulr_natr -natrM ler_pdivrMr ?ltr0n ?muln_gt0// mul1r.
  have le1: (eps / M) ^+ n <= 1.
    apply/exprn_ile1.
      apply/divr_ge0; first exact/ltW.
      exact/(le_trans ler01).
    rewrite ler_pdivrMr ?mul1r; last exact/(lt_le_trans ltr01).
    exact/(le_trans eps1).
  by apply/(le_trans le1); rewrite ler1n muln_gt0.
move=> /(ler_pM _ _ (lexx (normr p`_ord_max))) => /(_ n (normr_ge0 _)).
rewrite div1r invr_ge0 => /(_ (ler0n _ _)) => le2 /(le_lt_trans le2) {le2} /= pqn x px.
have n0: (0 < n)%N.
  rewrite lt0n; apply/eqP => n0; move: sp; rewrite n0 => ps.
  have /size1_polyC pE : (size p <= 1)%N by rewrite ps.
  by move: px ps; rewrite pE rootC => /eqP ->; rewrite size_polyC eqxx.
have qn0: q`_n != 0.
  apply/eqP => qn.
  move: pqn; rewrite qn normr0 ltr_pdivrMr ?ltr0n// mul0r => /(le_lt_trans (normr_ge0 _)).
  by rewrite ltxx.
have {}sq : size q = n.+1.
  apply/eqP; rewrite eqn_leq; apply/andP; split; first by rewrite -sp.
  exact/gt_size.
case: (closed_field_poly_normal q) => /= r; rewrite lead_coefE sq -pred_Sn => qE.
move: (sq); rewrite qE size_scale// size_prod_seq; last first.
  by move=> i _; rewrite polyXsubC_eq0.
under eq_bigr do rewrite size_XsubC.
rewrite big_const_seq count_predT iter_addn_0 subSn ?leq_pmull// mul2n -addnn subDnCA// subnn addn0 => /eqP.
rewrite eqSS => /eqP sr.
pose m := (\big[Order.min/Re `|x - head 0 r|]_(z <- r) Re `|x - z|)%:C.
have m0: 0 <= m.
  rewrite /m lecE/= eqxx/=.
  rewrite le_bigmin -lecR (normr_ge0 (x - head 0 r)); apply/allP => y _ /=.
  by rewrite -lecR (normr_ge0 (x - y)).
have: `|p`_n| / 2 * m ^+ n <= `|q.[x]|.
  rewrite qE hornerE horner_prod normrM normr_prod; apply/ler_pM.
  - apply/divr_ge0; [apply/normr_ge0|apply/ler0n].
  - exact/exprn_ge0.
  - exact/ltW.
    rewrite -sr -prodr_const_seq big_seq [X in _ <= X]big_seq; apply/ler_prod => y yr.
    apply/andP; split=> //.
    rewrite !hornerE -[`|x - y|]RRe_real ?normr_real// /m lecR.
    rewrite bigmin_le; apply/orP; right; apply/hasP; exists y => //=.
rewrite -[q.[x]]subr0 -{2}(rootP px) distrC -hornerN -hornerD.
rewrite -[p - q]coefK horner_poly => mle.
move: (le_trans mle (ler_norm_sum _ _ _)).
under eq_bigr do rewrite normrM normrX coefD coefN; move=> {}mle.
have: normr (p`_n) / 2 * m ^+ n <=
    \sum_(i < size (p - q)) normr p`_n * ((eps / M) ^+ n / (n.+1%:R *+ 4)) * M ^+ n.
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
  - rewrite -[M ^+ i]mul1r -ler_pdivrMr; last exact/exprn_gt0/(lt_le_trans ltr01).
    rewrite -expr_div_n; apply/exprn_ile1.
      by apply/divr_ge0; [apply/normr_ge0|apply/(le_trans ler01)].
    rewrite ler_pdivrMr ?mul1r /M; last exact/(lt_le_trans ltr01).
    rewrite -[X in X <= _]RRe_real ?normr_real// lecR.
    rewrite le_bigmax; apply/orP; right; apply/hasP; exists x => //=.
    by rewrite mem_dec_roots -size_poly_leq0 sp.
  - exact/exprn_ege1.
rewrite sumr_const card_ord -[(_ * _) *+ _]mulr_natr -!mulrA -subr_ge0 -mulrBr pmulr_rge0; last first.
rewrite normr_gt0; apply/eqP => pn.
  suff: (size p <= n)%N by rewrite sp ltnn.
  apply/leq_sizeP => i; rewrite leq_eqVlt => /orP[/eqP <- //|].
  by rewrite -sp => /leq_sizeP/(_ i (leqnn i)).
rewrite subr_ge0 mulrC expr_div_n -[_ *+ 4]mulr_natr [_^-1 * _]mulrC [_ * 4]mulrC -mulf_div.
rewrite [X in _ <= X]mulrA mulf_div [_ * 4]mulrC -mulf_div divff; last first.
  exact/expf_neq0/lt0r_neq0/(lt_le_trans ltr01).
rewrite mulr1 => {}mle.
have /(le_trans mle) {}mle: eps ^+ n / 4 * ((size (p - q))%:R / n.+1%:R) <= eps ^+ n / 4.
  rewrite -[X in _ <= X]mulr1; apply/ler_pM.
  - apply/mulr_ge0; first exact/exprn_ge0/ltW.
    by rewrite invr_ge0.
  - exact/divr_ge0.
  - exact/lexx.
  by rewrite mulrC ler_pdivrMl ?ltr0n// mulr1 ler_nat -(maxnn n.+1) -{1}sp -sq -(size_opp q) size_add.
have /(le_lt_trans mle) : eps ^+ n / 4 < eps ^+ n / 2.
  by rewrite mulrC ltr_pdivrMl ?ltr0n// -[4%N]/((2 * 2)%N) natrM mulrACA divff ?pnatr_eq0// mulr1 mulrC mulr_natr mulr2n -subr_gt0 -addrA subrr addr0 exprn_gt0.
rewrite -subr_gt0 -(@pmulr_rgt0 _ 2%:R)// mulrBr subr_gt0 mulrCA divff ?pnatr_eq0// mulr1.
rewrite mulrCA divff ?pnatr_eq0// -ltr_pdivrMl ?exprn_gt0// mulrC -expr_div_n expr_lt1//; last first.
  by apply/mulr_ge0 => //; rewrite invr_ge0 ltW.
rewrite mulrC ltr_pdivrMl// mulr1 /m -[eps]RRe_real ?gtr0_real// ltcR.
rewrite bigmin_lt; case: r {qE m m0 mle} sr n0 => [<- //|] y r sr n0/=.
rewrite orbA orbb -/(has _ (y :: r)) => /hasP [z] zr zx.
exists z; split; last by rewrite -[`|x - z|]RRe_real ?normr_real// ltcR.
rewrite rootZ// root_bigmul; apply/hasP; exists z => //=.
by rewrite root_XsubC.
Qed.

Lemma rm_root_poly (p : {poly R[i]}) (x : R[i]) :
  x != 0 -> root p x -> p %/ ('X - x%:P) = \poly_(i < (size p).-1) (- x ^- (i.+1) * \sum_(j < i.+1) p`_j * x ^+ j).
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
under eq_bigr do rewrite mulrBr coefD coefN mulrBl coefMC -mulrA -exprS opprB coefMX {1}[X in q`_X]pred_Sn.
pose f i := (if i == 0%N then 0 else q`_i.-1) * x ^+ i.
rewrite -(big_mkord xpredT (fun i => f (i.+1) - f i)) telescope_sumr// /f/= mul0r subr0 mulrCA [X in _ * X]mulrC divff ?mulr1//.
exact/expf_neq0.
Qed.

Lemma close_rm_root (eps : R[i]) (p : {poly R[i]}) (xp : R[i]) : 0 < eps -> xp != 0 -> root p xp ->
  exists delta, 0 < delta /\ forall (q : {poly R[i]}) (xq : R[i]), root q xq -> deformp delta p q -> `|xp - xq| < delta -> deformp eps (p %/ ('X - xp%:P)) (q %/ ('X - xq%:P)).
Proof.
move=> e0 xp0 pxp /=.
have [->|] := poly0Vpos p.
  by exists 1; split=> [//|] q xq qxq []; rewrite size_poly0 => /size_poly_leq0P -> _ _; rewrite !div0p; split=> //; case; rewrite size_poly0.
move sp: (size p) => n; case: n sp => // n sp _.
pose f := fun i (x : 'rV[R[i]^o]_n.+1 * (R[i]^o)) => - (x.2 ^- i.+1) * \sum_(j < n.+1 | (j <= i)%N) x.1 ord0 j * x.2 ^+ j.
have cont : forall i, {for (\row_(i < n.+1) p`_i, xp), continuous (f i)}.
  move=> i /=.
  apply/(@continuousM R[i] ('rV[R[i]^o]_n.+1 * (R[i]^o))%type).
    apply (@continuousN R[i] R[i]^o ('rV[R[i]^o]_n.+1 * (R[i]^o))%type).
    apply/continuousV; first by rewrite expf_eq0.
    apply/continuousX.
    apply/cvg_snd.
  apply (@continuous_sum R[i] R[i]^o ('rV[R[i]^o]_n.+1 * (R[i]^o))%type) => j ji.
  apply/(@continuousM R[i] ('rV[R[i]^o]_n.+1 * (R[i]^o))%type); last first.
    exact/continuousX/cvg_snd.
  apply/(@eq_continuous_at ('rV[R[i]^o]_n.+1 * (R[i]^o))%type _ ((fun x : 'rV[R[i]^o]_n.+1 => x ord0 j) \o fst)) => //.
  apply/continuous_comp; first exact/cvg_fst.
  exact/coord_continuous.
have /fin_all_exists /=: forall i : 'I_n.+1, exists delta, 0 < delta /\ forall (q : {poly R[i]}) (xq : R[i]),
  deformp delta p q ->
  normr (xp - xq) < delta ->
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
rewrite -(RRe_real (normr_real _)) ltcR lt_bigmin lt_min -!ltcR !(RRe_real (normr_real _)) => /andP[] /andP[xpq] xqpn /allP xdelta.
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
  by move/(_ ord_max): dpq; rewrite -(RRe_real (normr_real _)) ltcR lt_bigmin lt_min qn0 subr0 ltxx andbF.
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
  rewrite (big_ord_iota _ n.+1 (fun i0 => (i0 <= i)%N) (fun i => p`_i * xp ^+ i)) -big_filter -{1}[i : nat]add0n filter_iota_leq; last by apply/ltnW; rewrite ltnS.
  by rewrite -big_ord_iota.
rewrite (big_ord_iota _ n.+1 (fun i0 => (i0 <= i)%N) (fun i => q`_i * xq ^+ i)) -big_filter -{1}[i : nat]add0n filter_iota_leq; last by apply/ltnW; rewrite ltnS.
by rewrite -big_ord_iota.
Qed.

Lemma deformpW (e e' : R[i]) (p q : {poly R[i]}) :
  e <= e' -> deformp e p q -> deformp e' p q.
Proof. by move=> ee [spq pqe]; split=> // i; apply/(lt_le_trans (pqe i)). Qed.

Lemma aligned_deformed (eps : R[i]) (p : {poly R[i]}) :
  0 < eps -> exists delta, 0 < delta /\ forall q, deformp delta p q -> alignp eps p q.
Proof.
wlog : eps / eps < 1 => [H|e1 e0].
  case: eps => eR eI.
  rewrite ltcE/= => /andP[/eqP ->] e0.
  case: (H (minr eR (1 / 2))%:C) => /= [||delta [d0 dP]] {H}.
  - by rewrite ltcR gt_min ltr_pdivrMr// mul1r -[1]/(1%:R) ltr_nat leqnn orbT.
  - rewrite ltcR lt_min e0/=; apply/mulr_gt0; first exact: ltr01.
    by rewrite invr_gt0 ltr0n.
  exists delta; split=> // q /dP pq i /pq ple.
  apply/(leq_trans ple); rewrite complexr0 big_mkcond [X in (_ <= X)%N]big_mkcond/=.
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
    case: (dec_roots p) (uniq_dec_roots p) (mem_dec_roots p) root0 => [|x r] ru memr /allP r0.
      have /closed_rootP [x]: size p != 1 by rewrite sp.
      by move: memr; rewrite p0/= => <-.
    move: (r0 x); rewrite in_cons eqxx/= => /(_ isT) /eqP x0; rewrite x0.
    by case: r ru {memr} r0 => // y r /= /andP[+ _] /(_ y); rewrite !in_cons negb_or eqxx orbT/= x0 eq_sym => /andP[/negP y0 _] /(_ isT).
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
  rewrite mu_mulC// mu_exp -['X]subr0 mu_XsubC eqxx mul1n big_mkcond big_seq big_mkcond/=.
  have da2 : d < `|a| / 2.
    rewrite /d -muln2 natrM -mulf_div -[X in _ < X]mul1r -subr_gt0 -mulrBl.
    apply/mulr_gt0; last by apply/mulr_gt0 => //; rewrite normr_gt0.
    rewrite subr_gt0 ltr_pdivrMr ?ltr0n// mul1r.
    apply/(lt_le_trans (y:=1)); last by rewrite ler1n.
    by rewrite exprn_ilt1// ltW.
  have da : d < `|a|.
    by apply/(lt_le_trans da2); rewrite ler_pdivrMr// ler_peMr// -[1]/(1%:R) ler_nat.
  have aqn : `|a| / 2 < `|q`_n.+1|.
    move: da2 => /(lt_trans qn)/(le_lt_trans (lerB_dist _ _)).
    by rewrite -[_ - _ < _]subr_gt0 opprD opprK addrA -{2}[`|a|]mulr1 -{2}(divff (x:=2))// mulrCA mulr_natl [_ / _ *+ _]mulr2n opprD addrA subrr add0r addrC subr_gt0.
  have {sq} : size q = n.+2.
    apply/anti_leq/andP; split=> //; rewrite ltnNge; apply/negP => /leq_sizeP /( _ n.+1 (leqnn _)) q0.
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
    rewrite subr_gt0 /d -mul2n natrM invrM ?unitfE// [_ / 2]mulrC -!mulrA mulVf// mulr1 mulrA mulrC -subr_gt0 -mulrBl pmulr_lgt0 ?subr_gt0; last first.
      by rewrite divr_gt0// normr_gt0.
    by move=> /(le_lt_trans y1); rewrite expr_gt1// ?ltW// => /(lt_trans e1); rewrite ltxx.
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
    rewrite normrM !normrX [2 * _]mulrC -mulf_div mulrA -subr_gt0 -mulrBl pmulr_lgt0; last first.
      by rewrite invr_gt0 exprn_gt0// normr_gt0.
    rewrite subr_gt0 -2!mulrA ltr_pM//.
    move: aqn; rewrite ltr_pdivrMr// -ltr_pdivrMl ?normr_gt0// -ltr_pdivlMr ?normr_gt0// => aqn.
    have [->|i0] := (posnP i); first by rewrite expr0 mulr1.
    by rewrite -[X in _ < X]mulr1 ltr_pM// expr_lt1.
  rewrite /d mulrCA divff// mulr1 mulrC -!mulrA divff ?normr_eq0// mulr1 mulrC -expr_div_n expr_gt1//.
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
  by rewrite ltcR !lt_min -!ltcR (RRe_real (gtr0_real d'0)) d'0 (RRe_real (gtr0_real d''0)) (RRe_real (normr_real _)) normr_gt0 lead_coef_eq0 p0.
have [-> [_]|q0 pq] := eqVneq q 0.
  rewrite sp => /(_ ord_max); rewrite coef0 subr0 -(RRe_real (normr_real _)).
  by rewrite ltcR !lt_min lead_coefE sp -pred_Sn ltxx andbF.
have /d''P/(_ _ px) [y [qy]] : deformp d'' p q.
  apply/(deformpW _ pq).
  by rewrite -{2}(RRe_real (gtr0_real d''0)) lecR !ge_min lexx !orbT.
rewrite -(RRe_real (normr_real _)) ltcR lt_min -!ltcR (RRe_real (normr_real _)) !(RRe_real (gtr0_real _))// => /andP[] xye xyd.
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

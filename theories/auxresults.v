(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import order fintype generic_quotient ssrint.
From mathcomp.ssreflect Require Import path.
From mathcomp Require Import div tuple bigop ssralg ssrnum matrix poly polydiv.
From mathcomp Require Import interval finmap mpoly polyorder polyrcf normedtype.
From mathcomp Require Import complex classical_sets topology qe_rcf_th.
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.TotalTheory Order.POrderTheory Num.Theory.

Ltac mp := 
  match goal with
  | |- (?x -> _) -> _ => have /[swap]/[apply]: x
  end.

Section MoreLogic.

Fact aux_equivb (P : Prop) (b c : bool) : reflect P b -> b = c -> reflect P c.
Proof. by move => reflect_P_b b_eq_c ; rewrite b_eq_c in reflect_P_b. Qed.

Variables (A B C : Prop).

Lemma if_iff_compat_l : B <-> C -> (A -> B) <-> (A -> C).
Proof. by move=> h; split => h1 h2; apply/h/h1. Qed.

Lemma if_iff_compat_r : B <-> C -> (B -> A) <-> (C -> A).
Proof. by move=> h; split => h1 h2; apply/h1/h. Qed.

Lemma bool_eq_arrow {b b' : bool} : b = b' -> b -> b'.
Proof. by case: b' => // /negP. Qed.

Lemma forallb_all [n : nat] (a : pred 'I_n) :
  [forall i, a i] = all a (enum 'I_n).
Proof.
apply/forallP/allP => /= aT i //.
by apply/aT; rewrite mem_enum.
Qed.

Lemma forall_ord0 (P : pred 'I_0) : [forall i, P i] = true.
Proof. by apply/forallP; case. Qed.

Lemma forall_ord1 (p : pred 'I_1) :
  [forall i : 'I_1, p i] = p ord0.
Proof. by rewrite forallb_all enum_ordSl enum_ord0/= andbT. Qed.
(* Alternative proof:
apply/forallP/idP => [/(_ ord0) //|p0].
by case; case=> // ilt; move: p0; congr p; apply/val_inj.
 *)

Lemma forall_ord2 (P : 'I_2 -> bool) :
  [forall i, P i] = (P ord0 && P ord_max).
Proof.
rewrite forallb_all !enum_ordSl enum_ord0/= andbT.
by congr (_ && P _); apply/val_inj.
Qed.
(* Alternative proof:
apply/forallP/andP => [p //|[] p0 p1 /=].
case; case=> [ilt|[ilt|//]].
  by move: p0; congr P; apply/val_inj.
by move: p1; congr P; apply/val_inj.
 *)

Lemma eq_mem_sym (T : Type) (p1 p2 :mem_pred T) : p1 =i p2 -> p2 =i p1.
Proof. by move=> h x; rewrite h. Qed.

End MoreLogic.

Section MoreNatTheory.

Lemma lt_predn n : (n.-1 < n) = (n != 0).
Proof. by case: n => [//|n]; rewrite ltnSn. Qed.

Lemma ltn_neq (n m : nat) : (n < m)%N -> n != m.
Proof. by rewrite ltn_neqAle => /andP[]. Qed.

Fact n_eq1 n : n != 0 -> n < 2 -> n = 1.
Proof. by case: n => [?|[?|[]]]. Qed.

Fact leq_npred m n : m > 0 -> (m <= n.-1) = (m < n).
Proof. by move: m n => [|m] [|n]. Qed.

Lemma leq_predn n m : (n <= m)%N -> (n.-1 <= m.-1)%N.
Proof.
case: n => [//|n]; case: m => [//|m].
by rewrite !succnK ltnS.
Qed.

Fact predn_sub m n : (m - n).-1 = (m.-1 - n).
Proof. by case: m => //= m; rewrite subSKn. Qed.

Lemma geq_subn m n : m <= n -> m - n = 0.
Proof. by rewrite -subn_eq0 => /eqP. Qed.

Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. by case: p => // p _; rewrite addnS !ltnS leq_subLR. Qed.

Lemma leq_subRL m n p : 0 < n -> (n <= p - m) = (m + n <= p).
Proof. by case: n => // n _; rewrite addnS ltn_subRL. Qed.

Fact ltpredn a b c : a != 0 -> ((a + b).-1 < c + b) = (a.-1 < c).
Proof. by rewrite -lt0n => a_gt0; rewrite !prednK ?ltn_addr // leq_add2r. Qed.

Lemma leq_leq_subRL m n p : m <= p -> (n <= p - m) = (m + n <= p).
Proof. by move=> ?; case: n => [|n]; rewrite ?leq0n ?addn0 ?leq_subRL. Qed.

Lemma leq_ltn_subLR m n p : n <= m -> (m - n < p) = (m < n + p).
Proof.
move=> le_nm; case: p => [|p]; last by rewrite ltn_subLR.
by rewrite addn0 ltn0 ltnNge le_nm.
Qed.

Lemma ltnpredn m n : (m < n.-1) = (m.+1 < n).
Proof. by case: n => [//|n]; rewrite succnK. Qed.

Lemma ltn_subCl m n p : 0 < p -> 0 < n -> (m - n < p) = (m - p < n).
Proof. by move=> ??; rewrite !ltn_subLR // addnC. Qed.

Lemma leq_ltn_subCl m n p : n <= m -> p <= m -> (m - n < p) = (m - p < n).
Proof. by move=> ??; rewrite !leq_ltn_subLR // addnC. Qed.

Lemma ltn_subCr m n p : (p < m - n) = (n < m - p).
Proof. by rewrite !ltn_subRL // addnC. Qed.

Lemma leq_subCr m n p : 0 < p -> 0 < n -> (p <= m - n) = (n <= m - p).
Proof. by move=> ??; rewrite !leq_subRL // addnC. Qed.

Lemma leq_leq_subCr m n p : n <= m -> p <= m -> (p <= m - n) = (n <= m - p).
Proof. by move=> ??; rewrite !leq_leq_subRL // addnC. Qed.

Lemma leq_subCl m n p : (m - n <= p) = (m - p <= n).
Proof. by rewrite !leq_subLR // addnC. Qed.

Lemma cross_leq_add m n p q :
(m <= n)%N -> (n + p <= m + q)%N -> (p <= q)%N.
Proof.
move=> leq_mn; rewrite addnC -leq_subLR => h.
by rewrite (leq_trans _ h) // -addnBA // leq_addr.
Qed.

Lemma lift_inord (n : nat) (i : 'I_n) :
  lift ord0 i = inord i.+1.
Proof. by apply/val_inj; rewrite /= inordK ?ltnS. Qed.

Lemma subn_prednn n m : (0 < m)%N -> (n.-1 - m.-1)%N = (n - m)%N.
Proof. by case: m => [//|m _]; rewrite succnK -predn_sub subnS. Qed.

Lemma subn_pred n m : (0 < m)%N -> (m <= n)%N -> (n - m.-1)%N = (n - m).+1.
Proof. by move=> m0 mn; rewrite -{1}[n]succnK subn_prednn// subSn. Qed.

End MoreNatTheory.

Section MoreSeq.

Section GeneralBaseType.
Variable (T : Type).

Lemma nseqS (n : nat) (x : T) : nseq n.+1 x = rcons (nseq n x) x.
Proof. by elim: n => //= n <-. Qed.

Definition nrcons (n : nat) (x : T) := iter n (fun s => rcons s x).

Lemma nseq_cat (n : nat) (x : T) (s : seq T) : s ++ nseq n x = nrcons n x s.
Proof.
elim: n => [|n ih]; first by rewrite cats0. 
by rewrite nseqS -rcons_cat ih.
Qed.

Lemma addn_nseq (m n : nat) (x : T) : (nseq m x) ++ (nseq n x) = nseq (m + n) x. 
Proof. by elim: m => // m ih; rewrite /= ih. Qed.

Lemma nrcons_cons (n : nat) (x : T) (s : seq T) (z : T) : 
  nrcons n z (x :: s) = x :: nrcons n z s.
Proof.
move: x s z; elim: n => // n ih x s z /=.
by rewrite ih rcons_cons.
Qed.

Lemma rcons_nrcons (n : nat) (x : T) (s : seq T) : 
  rcons (nrcons n x s) x = nrcons n.+1 x s.
Proof. by []. Qed. 

Fact head_rev (s : seq T) (x : T) : head x (rev s) = last x s.
Proof. by case/lastP: s => [//= |t y]; rewrite rev_rcons last_rcons //=. Qed.

Fact last_rev (s : seq T) (x : T) : last x (rev s) = head x s.
Proof. case: s => [//= |t y /=]; rewrite rev_cons last_rcons //=. Qed.

Lemma rev_nseq (n : nat) (x : T) : rev (nseq n x) = nseq n x.
Proof. by elim: n => // n; rewrite {1}nseqS rev_rcons => ->. Qed.

Lemma rev_ncons (n : nat) (x : T) (s : seq T) :
  rev (ncons n x s) = rev s ++ nseq n x.
Proof. by rewrite -cat_nseq rev_cat rev_nseq. Qed.

Lemma set_nth_rcons (d : T) (i : nat) (e : seq T) (x y : T) :
  (i < size e)%N -> set_nth d (rcons e y) i x = rcons (set_nth d e i x) y.
Proof.
move: i x y; elim: e => //.
move=> a e ihe i; elim: i => //.
move=> i ihi x y /=.
by rewrite ltnS => lt_ie; rewrite ihe.
Qed.

Lemma rcons_set_nth (x y : T) (s : seq T) :
  (set_nth y s (size s) x) = rcons s x.
Proof. by elim: s => //= a s <-. Qed.

Fact set_nthS (e : seq T) (i : nat) (x y : T) :
  (size e <= i)%N -> set_nth x e i y = set_nth x (rcons e x) i y.
Proof.
move: {2}(i - size e)%N (erefl (i - size e))%N x y => n.
move: e i; elim: n.
  move=> e i.
  move/eqP; rewrite subn_eq0 => leq_ie x y leq_ei.
  have -> : i = size e by apply/eqP; rewrite eqn_leq; apply/andP.
  move=> {leq_ie} {leq_ei} {i}; move: x y.
  elim: e => // a e ihe x y /=.
  by rewrite ihe.
move=> n ihn e.
elim: e.
  move=> i /=. rewrite subn0 => -> x y _ //=.
  by rewrite set_nth_nil.
move=> a e ihe i h x y ltaei.
move: h ltaei.
case: i => //= i.
rewrite subSS => h.
rewrite ltnS=> ltaei.
congr cons.
by rewrite ihe.
Qed.

(* to be replaced by set_nth_over *)
Lemma set_nth_nrcons (e : seq T) (i : nat) (x y : T) :
  (size e <= i)%N -> (set_nth x e i y) = rcons (nrcons (i - (size e)) x e) y.
Proof.
move: {2}(i - size e)%N (erefl (i - size e))%N x y => n.
move: e i; elim: n => [e i|n ihn e].
  move/eqP; rewrite subn_eq0 => h x y leq_ei.
  have -> : i = size e by apply/eqP; rewrite eqn_leq; apply/andP.
  rewrite subnn /=.
  by move=> {h} {leq_ei}; elim: e => //= a e ->.
elim: e => [i|a e ihe i h x y ltaei].
  rewrite subn0 => -> x y _.
  by rewrite set_nth_nil -cat_nseq cats1 -nseq_cat cat0s.
move: h ltaei; case: i => //= i.
rewrite subSS => h; rewrite ltnS => ltaei.
by rewrite ihe // -rcons_cons nrcons_cons.
Qed.

Lemma set_nth_over (e : seq T) (i : nat) (x y : T) : 
  (size e <= i)%N -> (set_nth x e i y) =
                     rcons (e ++ (nseq (i - (size e))%N x)) y.
Proof. 
by move=> h; rewrite set_nth_nrcons //; congr rcons; rewrite nseq_cat.
Qed.

Lemma set_nth_nseq (i j : nat) (x y z : T) : (i <= j)%N ->
  set_nth x (nseq j y) i z = (rcons (nseq i y) z) ++ (nseq (j - i).-1 y).
Proof.
move: i x y z; elim: j => [|j ih] i x y z; first by rewrite leqn0 => /eqP ->.
case: i => [_|i leq_ij] //=.
by rewrite ih.
Qed.

(* Fact fv_nquantify (m n i : nat) (f : formula F) :  *)
(* (m <= i < m+n)%N -> i \notin formula_fv (nquantify m n Exists f). *)
(* Proof. *)
(* rewrite formula_vf_nquantify. *)
(* by rewrite formula_vf_mnquantify -mnfsetE in_fsetD negb_and negbK => ->. *)
(* Qed. *)

Lemma set_nth_catr (i : nat) (e1 e2 : seq T) (x y : T) : 
    (size e1 <= i)%N -> 
    set_nth x (e1 ++ e2) i y = e1 ++ (set_nth x e2 (i - (size e1)) y).
Proof.
move: i e2 y; elim/last_ind: e1 => [i e2 y _ |e1 b ih i e2 y].
  by rewrite subn0.
rewrite size_rcons=> h; rewrite cat_rcons.
rewrite ih; last by rewrite ltnW.
by rewrite cat_rcons -[(i - size e1)%N]prednK ?subn_gt0 // subnS. 
Qed.

Lemma set_nth_catl (i : nat) (e1 e2 : seq T) (x y : T) : 
  (i < size e1)%N -> set_nth x (e1 ++ e2) i y = set_nth x e1 i y ++ e2.
Proof.
move: i e1 y; elim/last_ind : e2 => [i e1| e2 z ih i e1] y h; rewrite ?cats0 //.
rewrite -rcons_cat set_nth_rcons ?size_cat ?(leq_trans h) // ?leq_addr //.
by rewrite ih // rcons_cat //.
Qed.

Lemma set_nth_cat (i : nat) (e1 e2 : seq T) (x y : T) :
  set_nth x (e1 ++ e2) i y = if (i < size e1)%N then set_nth x e1 i y ++ e2
                             else e1 ++ (set_nth x e2 (i - (size e1)) y).
Proof.
have [leq_e1i|lt_ie1] := leqP (size e1) i; first by rewrite set_nth_catr.
by rewrite set_nth_catl.
Qed.

Lemma rcons_is_cat (e : seq T) (x : T) : rcons e x = e ++ [::x].
Proof. by rewrite -cat_rcons cats0. Qed.

Lemma take_rcons (i : nat) (e : seq T) (x : T) :
  take i (rcons e x) = if (i <= size e)%N then take i e 
                       else rcons (take i e) x.
Proof.
have [leq_ie|lt_ei] := leqP i (size e); last first.
  by rewrite take_oversize ?size_rcons // take_oversize // ltnW.
rewrite rcons_is_cat take_cat.
rewrite leq_eqVlt in leq_ie.
move/orP : leq_ie => [/eqP eq_ie | ->] => //.
by rewrite eq_ie ltnn subnn take_size cats0.
Qed.

Lemma set_nth_takeC (i : nat) (e : seq T) (j : nat) (x y : T) : 
  (j < i)%N -> set_nth y (take i e) j x = take i (set_nth y e j x).
Proof.
move=> lt_ji.
have [leq_ei|lt_ie] := leqP (size e) i.
by rewrite ?take_oversize // ; 
        last by rewrite size_set_nth geq_max; apply/andP; split.
move: i j lt_ji lt_ie; elim: e => // a e ihe i.
elim: i => // i ihi j; elim: j => // j ihj.
rewrite ltnS => lt_ji.
by rewrite /= ltnS => lt_ie; rewrite ihe.
Qed.

Lemma set_nth_take (i : nat) (e : seq T) (j : nat) (x y : T) : (i <= j)%N -> 
  set_nth x (take i e) j y  
                    = rcons ((take i (set_nth x e j y)) ++ (nseq (j - i) x)) y.
Proof.
move: i j; elim: e => // [i j leq_ij | a e ihe i].
- rewrite //= !set_nth_nil -cat_nseq take_cat size_nseq.
  rewrite leq_eqVlt in leq_ij.
  move/orP : leq_ij => [/eqP eq_ij|lt_ij].
    by rewrite -eq_ij ltnn subnn /= !cats0 -rcons_is_cat.
  rewrite lt_ij -rcons_is_cat -{2}[j](@subnKC i); last by rewrite ltnW.
  rewrite -addn_nseq take_size_cat ?size_nseq // addn_nseq.
  by rewrite subnKC; last by rewrite ltnW.
- elim: i => [j _| i ihi j].
    by rewrite subn0 !take0 /= set_nth_nil rcons_is_cat cat_nseq.
  elim: j => // j ihj. 
  by rewrite ltnS => lt_iSj /=; rewrite ihe.
Qed.

Lemma eq_iotar (a c b d : nat) : iota a b =i iota c d -> b = d.
Proof.
move=> eq_ab_cd; rewrite -(size_iota a b) -(size_iota c d).
by apply/eqP; rewrite -uniq_size_uniq ?iota_uniq.
Qed.

Lemma eq_mem_nil (U : eqType) (s : seq U) : reflect (s =i [::]) (s == [::]).
Proof.
apply: (iffP idP); first by move/eqP ->.
move=> h; apply/eqP/nilP; rewrite /nilp -all_pred0.
by apply/allP => /= x; rewrite h.
Qed.

Lemma eq_iotal (b d a c : nat) : b != O -> iota a b =i iota c d -> a = c.
Proof.
case: b => // b _; case: d => [/eq_mem_nil//|d eq_ab_cd].
wlog suff hwlog : b d a c eq_ab_cd / (a <= c)%N.
  by apply/eqP; rewrite eqn_leq (hwlog b d) ?(hwlog d b).
have := eq_ab_cd c; rewrite !in_cons eqxx /= mem_iota.
by case: ltngtP => [| /ltnW leq_ac|->].
Qed.

Arguments eq_iotal {_} _ {_ _} _ _.

Lemma iotanS (n m : nat) :
  iota n m.+1 = rcons (iota n m) (n + m)%N.
Proof.
elim: m n => /= [|m IHm] n; first by rewrite addn0.
by rewrite IHm addSn addnS.
Qed.

Lemma nth_enum_ord (n : nat) (i j : 'I_n) : nth i (enum 'I_n) j = j.
Proof. by apply/val_inj => /=; rewrite nth_enum_ord. Qed.

Lemma enum_ordD (n m : nat) :
  enum 'I_(n+m) =
    map (@lshift n m) (enum 'I_n) ++ map (@rshift n m) (enum 'I_m).
Proof.
elim: n => [|n IHn].
  rewrite enum_ord0/=.
  elim: m => [|m IHm]; first by rewrite enum_ord0.
  rewrite enum_ordSl IHm/=; congr (_ :: _); first exact/val_inj.
  rewrite -[LHS]map_id.
  by apply/eq_map => i; apply/val_inj.
rewrite !enum_ordSl IHn/=; congr (_ :: _); first exact/val_inj.
by rewrite map_cat -!map_comp; congr (_ ++ _); apply/eq_map => i; apply/val_inj.
Qed.

Lemma iotaE0 (i n : nat) : iota i n = [seq i+j | j <- iota 0 n].
Proof. by elim: n => // n IHn; rewrite -addn1 !iotaD/= map_cat IHn/= add0n. Qed.

Lemma map_ord_iota (f : nat -> T) (n : nat) :
  [seq f i | i : 'I_n] = [seq f i | i <- iota 0 n].
Proof.
by rewrite [LHS](eq_map (g:=f \o (val : 'I_n -> nat)))// map_comp val_enum_ord.
Qed.

Lemma nth_map_ord (x : T) n (f : 'I_n -> T) (i : 'I_n) :
  nth x [seq f i | i <- enum 'I_n] i = f i.
Proof. by rewrite (nth_map i) ?nth_enum_ord// size_enum_ord. Qed.

Lemma index_iota n m i :
  index i (iota n m) = if (i < n)%N then m else minn (i - n)%N m.
Proof.
elim: m i n => /= [|m IHm] i n; first by rewrite minn0 if_same.
have [->|/negPf ni] := eqVneq n i; first by rewrite ltnn subnn min0n.
rewrite IHm ltnS leq_eqVlt eq_sym ni/=.
case: (ltnP i n) => [//|] ni'.
by rewrite -minnSS subnS prednK// subn_gt0 ltn_neqAle ni.
Qed.

Lemma nth_catr (x0 : T) (s1 s2 : seq T) (p n : nat) :
  p = size s1 ->
  nth x0 (s1 ++ s2) (p + n) = nth x0 s2 n.
Proof.
move=> ->.
by rewrite nth_cat -[X in (_ < X)%N]addn0 ltn_add2l ltn0 subDnCA// subnn addn0.
Qed.

(* Why does size_take not use minn? *)
Lemma size_take (n0 : nat) (s : seq T) :
  size (take n0 s) = minn n0 (size s).
Proof. by rewrite size_take. Qed.

Lemma mktupleE (n : nat) (T' : Type) (f : 'I_n -> T') :
  tval (mktuple f) = [seq f i | i <- enum 'I_n].
Proof.
case: n f => [|n] f.
  by rewrite enum_ord0/=; apply/size0nil; rewrite size_tuple card_ord.
by apply/(@eq_from_nth _ (f ord0)) => [|i]; rewrite size_tuple.
Qed.

Definition resize (x : T) (u : seq T) (n : nat) :=
  take n (u ++ [seq x | i <- iota 0 (n - size u)]).

Lemma size_resize (x : T) (u : seq T) (n : nat) :
  size (resize x u n) = n.
Proof.
rewrite size_take size_cat size_map size_iota.
case: (ltnP n (size u)) => [/ltnW|] nu.
  by rewrite geq_subn// addn0; apply/minn_idPl.
by rewrite -subDnCA// subDnAC// subnn minnn.
Qed.

Lemma nth_resize (x : T) (u : seq T) (n i : nat) :
  (i < n)%N -> nth x (resize x u n) i = nth x u i.
Proof.
rewrite /resize => ilt.
rewrite nth_take// nth_cat.
case: ifP => [//|] /negP/negP; rewrite -leqNgt => ui.
rewrite [RHS]nth_default//.
rewrite nth_map// size_iota; apply/ltn_sub2r => //.
exact/(leq_ltn_trans ui ilt).
Qed.

Lemma resize_id (x : T) (u : seq T) : resize x u (size u) = u.
Proof.
apply/(@eq_from_nth _ x); first exact/size_resize.
move=> i; rewrite size_resize => iu.
by rewrite nth_resize.
Qed.

End GeneralBaseType.

Section WithEqType.

Variables (T : eqType) (a1 a2 : pred T) (s : seq T).

Lemma resize_idE (x : T) (u : seq T) n :
  (resize x u n == u) = (n == size u).
Proof.
have [->|/eqP nu] := eqVneq n (size u); first exact/eqP/resize_id.
by apply/negP => /eqP/(congr1 size); rewrite size_resize.
Qed.

Lemma sub_filter : 
    subpred a1 a2 -> {subset [seq x <- s | a1 x] <= [seq x <- s | a2 x]}.
Proof.
move=> sub_a1_a2 x ; rewrite !mem_filter.
by move/andP => [a1x ->] ; rewrite andbT sub_a1_a2.
Qed.

Lemma sub_map_filter (U : eqType) (f : T -> U) : subpred a1 a2 ->
  {subset [seq f x | x <- s & a1 x] <= [seq f x | x <- s & a2 x]}.
Proof.
move=> sub_a1_a2 x.
move/mapP => [y hy] eq_x_fy ; apply/mapP ; exists y => //.
exact: sub_filter.
Qed.

Lemma eq_map_seq [U : Type] [f g : T -> U] (r : seq T) :
  {in r, forall x, f x = g x} -> map f r = map g r.
Proof.
elim: r => //= x r IHr fg; congr cons; first exact/fg/mem_head.
by apply/IHr => y yr; apply/fg; rewrite in_cons yr orbT.
Qed.

Lemma subseq_drop_index (x : T) (s1 s2 : seq T) :
  subseq (x :: s1) s2 = subseq (x :: s1) (drop (index x s2) s2).
Proof.
move nE: (index _ _) => n.
elim: n s2 nE => [|n IHn] s2 nE; first by rewrite drop0.
case: s2 nE => [//|y s2].
have [->|/negPf /=] := eqVneq y x; first by rewrite /= eqxx.
by rewrite eq_sym => -> /succn_inj; apply/IHn.
Qed.

End WithEqType.

Lemma subseq_nth_iota (T : eqType) (x : T) (s1 s2 : seq T) :
  reflect
    (exists t, subseq t (iota 0 (size s2)) /\ s1 = [seq nth x s2 i | i <- t])
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

End MoreSeq.

Section MoreSeqEqType.

Variable (T : eqType).

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma perm_eq_nil (s : seq T) : (s =p [::]) = (s == [::]).
Proof.
by apply/idP/eqP => /perm_nilP.
Qed.

Lemma rem_cons (s : seq T) (a : T) : rem a (a :: s) = s.
Proof. by rewrite /= eqxx. Qed.

Lemma rcons_nil (a : T) : rcons [::] a = [:: a].
Proof. by rewrite -cats1 cat0s. Qed.

Fact cat_nil (s1 s2 : seq T) :
  s1 ++ s2 == [::] = ((s1 == [::]) && (s2 == [::])).
Proof. by case: s1 => //= ->. Qed.

Lemma rem_is_nil (x : T) (s : seq T) : rem x s == [::] ->
  ((s == [::]) || (s == [:: x])).
Proof. by case: s => //= y s; rewrite eqseq_cons; case: (y == x). Qed.

Lemma undup_catl (s1 s2 : seq T) : 
  undup ((undup s1) ++ s2) = undup (s1 ++ s2).
Proof.
elim: s1 => // x s /= ih.
have [x_in_s | /negbTE x_notin_s] := boolP (x \in s).
  by rewrite mem_cat x_in_s.  
rewrite mem_cat x_notin_s /= !ih mem_cat.
have [x_in_s2 | /negbTE x_notin_s2] := boolP (x \in s2).
  by rewrite orbT.
by rewrite orbF mem_undup x_notin_s.
Qed.

Lemma in_rcons (s : seq T) (x y : T) : 
  (x \in rcons s y) = (x == y) || (x \in s).
Proof. by elim: s => // z s ih; rewrite rcons_cons !in_cons ih orbCA. Qed.

(* not used *)
(* Lemma undup_rlast (s : seq T) (x : T) : *)
(*   undup (rcons s x) = rcons (rem x (undup s)) x. *)
(* Proof. *)
(* elim: s => // y s ih. *)
(* rewrite rcons_cons /= in_rcons ih. *)
(* have [ <- | neq_xy] := eqVneq x y. *)
(*   rewrite eqxx fun_if /= eqxx. *)
(*   have [x_in_s | x_notin_s] := boolP (x \in s) => //. *)
(*   by rewrite rem_id // mem_undup. *)
(* rewrite eq_sym. *)
(* move/negbTE : neq_xy => neq_xy ; rewrite neq_xy. *)
(* have [y_in_s | y_notin_s] := boolP (y \in s) => //. *)
(* by rewrite /= eq_sym neq_xy rcons_cons. *)
(* Qed. *)

Lemma undup_catr (s1 s2 : seq T) : 
  undup (s1 ++ (undup s2)) = undup (s1 ++ s2).
Proof.
elim: s1 => // [| x s ih]; first by rewrite !cat0s //undup_id // undup_uniq.
by rewrite /= ih !mem_cat mem_undup.
Qed.

Lemma subset_cons (x : T) (s1 s2 : seq T) : 
  {subset x :: s1 <= s2} <-> (x \in s2) /\ {subset s1 <= s2}.
Proof.
split => [subx12 | [x_in_s2 sub12] y].
  split; first by rewrite subx12 // mem_head.
  move=> y y_in_s1.
  by rewrite subx12 // in_cons y_in_s1 orbT.
rewrite in_cons => /orP [/eqP -> | y_in_s1] //.
by rewrite sub12.
Qed.

Lemma undup_cat (s1 s2 : seq T) : 
  sub_mem (mem s1) (mem s2) -> undup (s1 ++ s2) = undup s2.
Proof.
elim: s1 => // x s1 ih /=.
move/subset_cons => [x_in_s2 sub12].
by rewrite ih // mem_cat x_in_s2 orbT.
Qed.

Example undup_cat_ss (s : seq T) : undup (s ++ s) = undup s.
Proof. exact: undup_cat. Qed.

(* Fact undup_uniq (x : R) (s : seq T) :  *)
(* undup (s ++ (x :: s2)) = if x \in s then . *)
(* x \in s => undup s = rem x s. *)

Fact undup_cat_1312 (s1 s2 s3 : seq T) : 
  undup ((s1 ++ s3) ++ s2 ++ s3) = undup (s1 ++ s2 ++ s3).
Proof.
elim: s1 => // [|x s1 /= ->].
  rewrite !cat0s undup_cat // => x.
  by rewrite mem_cat => ->; rewrite orbT.
by rewrite !mem_cat orbACA orbb !orbA.
Qed.

Lemma rem_undup (x : T) (s : seq T) : 
  rem x (undup s) = undup (seq.filter (predC1 x) s).
Proof.
by rewrite rem_filter ?undup_uniq// filter_undup.
Qed.

Local Open Scope ring_scope. 

Lemma set_nth_id (e : seq T) (i : nat) (a x : T)
  : (i < size e)%N -> (set_nth x e i (nth a e i)) = e.
Proof.
move: e x; elim: i => [| i ih] e x; first by rewrite lt0n size_eq0; case: e.
by case: e => //= b e; rewrite ltnS => h; rewrite ih.
Qed.

Lemma set_nth_nth (e : seq T) (i : nat) (a : T) :
  set_nth a e i (nth a e i) = e ++ (nseq (i.+1 - (size e) ) a).
Proof.
have [lt_ie|leq_ei] := ltnP i (size e).
  rewrite set_nth_id //; move: lt_ie; rewrite -subn_eq0=> /eqP ->.
  by rewrite cats0.
by rewrite set_nth_over // rcons_cat subSn // nseqS nth_default //.
Qed.

End MoreSeqEqType.

Lemma in_itv' (disp : unit) (T : porderType disp) (x : T) (i : interval T) :
    (x \in i) = let 'Interval l u := i in
      ((l <= (BLeft x)) && ((BRight x) <= u))%O.
Proof.
case: i => l u; rewrite in_itv; congr andb.
by case: l => //=; case.
Qed.

Section MoreFinmap.

Local Open Scope fset_scope.

Lemma finSet_ind (T : choiceType) (P : {fset T} -> Prop) : 
  P fset0 -> (forall s x, P s -> P (x |` s)) -> forall s, P s.
Proof.
move=> Hfset0 HfsetU s.
move: {2}(#|`s|) (erefl #|`s|) => r.
move: s; elim: r => [s| r ih s hs]; first by move/cardfs0_eq ->. 
have s_neq0 : s != fset0 by rewrite -cardfs_gt0 hs.
move: s_neq0 hs => /fset0Pn [x x_in_s].
rewrite -(fsetD1K x_in_s) cardfsU1 in_fsetD1 x_in_s eqxx [in LHS]/= add1n.
move/eqP; rewrite eqSS; move/eqP => hs.
by apply: HfsetU; apply: ih.
Qed.

Lemma neq_fset10 (i : nat) : ([fset i] == fset0) = false.
Proof.
apply/negbTE; rewrite -fproper0 fproperEcard cardfs0 cardfs1 andbT.
by apply/fsubsetP => j; rewrite in_fset0.
Qed.

Lemma imfset1 (T U : choiceType) (f : T -> U) (x : T) :
  [fset f x | x in [fset x]] = [fset f x].
Proof.
apply/fsetP => y; rewrite inE; apply/imfsetP/eqP => [[z]|yE].
  by rewrite inE => /eqP ->.
by exists x; rewrite // inE.
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

Lemma fsubset_trans (T : choiceType) (B A C : {fset T}) :
  A `<=` B -> B `<=` C -> A `<=` C.
Proof. by move=> /fsubsetP AB /fsubsetP BC; apply/fsubsetP => x /AB /BC. Qed.

Lemma seq_fset_sub (d : unit) (T : choiceType) (s1 s2 : seq T) :
  reflect {subset s1 <= s2} (seq_fset d s1 `<=` seq_fset d s2).
Proof.
apply: (@equivP _ _ _ (@fsubsetP _ _ _)).
by split => h x; move/(_ x) : h; rewrite !seq_fsetE.
Qed.

Lemma seq_fset_nil (K : choiceType) (k : unit) : seq_fset k [::] = (@fset0 K).
Proof. by apply/eqP; rewrite -cardfs_eq0 size_seq_fset. Qed.

Lemma seq_fset_cons (K : choiceType) (k : unit) (a : K) (s : seq K) :
  seq_fset k (a :: s) = a |` (seq_fset k s).
Proof. by apply/fsetP => x; rewrite !in_fsetE !seq_fsetE inE. Qed.

Lemma seq_fset_cat (K : choiceType) (k : unit) (s1 s2 : seq K) :
  seq_fset k (s1 ++ s2) = (seq_fset k s1) `|` (seq_fset k s2).
Proof.
elim: s1 s2 => [s1|a s1 ih s2]; first by rewrite seq_fset_nil fset0U.
by rewrite /= !seq_fset_cons ih fsetUA.
Qed.

Lemma eq_fsetD (K : choiceType) (A B C : finSet K) :
  (A `\` B == C) = fdisjoint C B && ((C `<=` A) && (A `<=` B `|` C)).
Proof. by rewrite eqEfsubset fsubDset fsubsetD andbCA andbA andbC. Qed.

Lemma fset1D1 (K : choiceType) (a' a : K) :
  [fset a] `\ a' = if (a' == a) then fset0 else [fset a].
Proof.
apply/fsetP=> b; rewrite 2!fun_if !in_fsetE; have [->|] := altP (a' =P a).
  exact/andNb.
by have [//->|]// := altP (b =P a); rewrite ?andbF // eq_sym => ->.
Qed.

End MoreFinmap.

Section MoreRelation.

Variables (T : eqType) (P : pred T) (sT : subType P) (r : equiv_rel T).

Definition sub_r (x y : sT) := r (val x) (val y).

Lemma sub_r_refl : reflexive sub_r.
Proof. by rewrite /sub_r. Qed.

Lemma sub_r_sym : ssrbool.symmetric sub_r.
Proof. by move=> x y; rewrite /sub_r equiv_sym. Qed.

Lemma sub_r_trans : transitive sub_r.
Proof. by move=> x y z hyx; apply: equiv_trans. Qed.

Fail Check [equiv_rel of sub_r].

Canonical sub_r_equiv := EquivRel sub_r sub_r_refl sub_r_sym sub_r_trans.

Check [equiv_rel of sub_r].

End MoreRelation.

Section TestMoreRelation.

Variables (T : eqType) (P : pred T) (sT : subType P) (r : equiv_rel T).
Definition r2 := @sub_r _ _ sT r.
Check [equiv_rel of r].
Check [equiv_rel of r2].

End TestMoreRelation.

Section MoreBigop.

Lemma big_morph_in (R1 R2 : Type)
  (f : R2 -> R1) (id1 : R1) (op1 : R1 -> R1 -> R1)
  (id2 : R2) (op2 : R2 -> R2 -> R2) (D : pred R2) :
  (forall x y, x \in D -> y \in D -> op2 x y \in D) ->
  id2 \in D ->
  {in D &, {morph f : x y / op2 x y >-> op1 x y}} ->
  f id2 = id1 ->
  forall  (I : Type) (r : seq I) (P : pred I) (F : I -> R2),
  all D [seq F x | x <- r & P x] ->
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof.
move=> Dop2 Did2 f_morph f_id I r P F.
elim: r => [|x r ihr /= DrP]; rewrite ?(big_nil, big_cons) //.
set b2 := \big[_/_]_(_ <- _ | _) _; set b1 := \big[_/_]_(_ <- _ | _) _.
have fb2 : f b2 = b1 by rewrite ihr; move: (P x) DrP => [/andP[]|].
case: (boolP (P x)) DrP => //= Px /andP[Dx allD].
rewrite f_morph ?fb2 // /b2 {b2 fb2 ihr b1 x Px Dx f_morph f_id}.
elim: r allD => [|x r ihr /=]; rewrite ?(big_nil, big_cons) //.
by case: (P x) => //= /andP [??]; rewrite Dop2 // ihr.
Qed.

Variables (R : Type) (idx : R).

Fact big_ord_exchange_cond {op : Monoid.law idx} {a b : nat}
   (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < a | P i && (i < b)) F i =
  \big[op/idx]_(i < b | P i && (i < a)) F i.
Proof.
wlog le_b_a : a b / b <= a => [hwlog|].
  have /orP [le_a_b|le_b_a] := leq_total a b; last exact: hwlog.
  by symmetry; apply: hwlog.
rewrite big_ord_narrow_cond /=; apply: eq_big => // i.
by rewrite (leq_trans _ le_b_a) ?andbT.
Qed.

Fact big_ord_exchange {op : Monoid.law idx} {a b : nat} (F : nat -> R) :
  \big[op/idx]_(i < a | i < b) F i =
  \big[op/idx]_(i < b | i < a) F i.
Proof. exact: (big_ord_exchange_cond xpredT). Qed.

Fact big_ord1 (op : Monoid.law idx) (F : nat -> R) :
  \big[op/idx]_(i < 1) F i = F 0.
Proof. by rewrite big_ord_recl big_ord0 Monoid.mulm1. Qed.

Lemma big_nat_widen_l (op : Monoid.law idx)
     (m1 m2 n : nat) (P : pred nat) (F : nat -> R) :
   m2 <= m1 ->
   \big[op/idx]_(m1 <= i < n | P i) F i =
   \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> le_m2m1; have [ltn_m1n|geq_m1n] := ltnP m1 n; last first.
  rewrite big_geq // big_nat_cond big_pred0 // => i.
  by apply/negP => /and3P[/andP [_ /leq_trans]]; rewrite leqNgt => ->.
rewrite [RHS](@big_cat_nat _ _ _ m1) // 1?ltnW //.
rewrite [X in op X]big_nat_cond [X in op X]big_pred0; last first.
  by move=> i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
rewrite Monoid.mul1m [LHS]big_nat_cond [RHS]big_nat_cond.
by apply/eq_bigl => i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
Qed.

Lemma big_mknat  (op : Monoid.law idx)  (a b : nat) (F : nat -> R) :
  \big[op/idx]_(i < b | a <= i) F i = \big[op/idx]_(a <= i < b) F i.
Proof.
rewrite -(big_mkord (fun i => a <= i) F).
by rewrite -(big_nat_widen_l _ _ predT) ?leq0n.
Qed.

Lemma sum1_ord (n : nat) :
  (\sum_(i < n) 1)%N = n.
Proof. by rewrite big_const_ord iter_addn_0 mul1n. Qed.

Lemma big_ord_iota (op : Monoid.law idx) (n : nat)
    (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < n | P i) F i = \big[op/idx]_(i <- iota 0 n | P i) F i.
Proof.
elim: n P F => [|n IHn] P F; first by rewrite big_ord0 big_nil.
rewrite [LHS]big_mkcond big_ord_recr iotanS.
rewrite -cats1 big_cat big_cons big_nil add0n Monoid.mulm1/=; congr (op _ _).
by rewrite -big_mkcond IHn.
Qed.

Lemma prodr_const_seq (F : semiRingType) (I : Type) (r : seq I) (x : F) :
  (\prod_(i <- r) x = x ^+ (size r))%R.
Proof.
elim: r => [|y r IHr].
  by rewrite big_nil expr0. 
by rewrite big_cons IHr/= exprS.
Qed.

Lemma bigmin_le {disp : unit} {T : orderType disp} (I : Type) (r : seq I)
    (x : T) (P : pred I) (F : I -> T) (y : T) :
  (\big[Order.min/x]_(i <- r | P i) F i <= y)%O =
      (x <= y)%O || has (fun i => P i && (F i <= y)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
by rewrite ge_min IHr !orbA; congr (_ || _); apply/orbC.
Qed.

Lemma bigmin_lt {disp : unit} {T : orderType disp} (I : Type) (r : seq I)
    (x : T) (P : pred I) (F : I -> T) (y : T) :
  (\big[Order.min/x]_(i <- r | P i) F i < y)%O =
      (x < y)%O || has (fun i => P i && (F i < y)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
by rewrite gt_min IHr !orbA; congr (_ || _); apply/orbC.
Qed.

Lemma le_bigmin {disp : unit} {T : orderType disp} (I : Type) (r : seq I)
    (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y <= \big[Order.min/x]_(i <- r | P i) F i)%O =
      (y <= x)%O && all (fun i => P i ==> (y <= F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil andbT.
rewrite big_cons/=; case: (P i) => //=.
by rewrite le_min IHr !andbA; congr (_ && _); apply/andbC.
Qed.

Lemma lt_bigmin {disp : unit} {T : orderType disp} (I : Type) (r : seq I)
    (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y < \big[Order.min/x]_(i <- r | P i) F i)%O =
      (y < x)%O && all (fun i => P i ==> (y < F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil andbT.
rewrite big_cons/=; case: (P i) => //=.
by rewrite lt_min IHr !andbA; congr (_ && _); apply/andbC.
Qed.

Lemma le_bigmax {disp : unit} {T : orderType disp} (I : Type) (r : seq I)
    (x : T) (P : pred I) (F : I -> T) (y : T) :
  (y <= \big[Order.max/x]_(i <- r | P i) F i)%O =
      (y <= x)%O || has (fun i => P i && (y <= F i)%O) r.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil orbF.
rewrite big_cons/=; case: (P i) => //=.
rewrite le_max IHr !orbA; congr (_ || _); exact/orbC.
Qed.

Lemma big_hasE (I J : Type) (op : Monoid.com_law idx)
    (r : seq I) (P : pred I) (F : I -> R) (s : seq J) (a : I -> pred J) :
  (forall i, P i -> (count (a i) s <= 1)%N) ->
  \big[op/idx]_(i <- r | P i && has (a i) s) F i =
      \big[op/idx]_(j <- s) \big[op/idx]_(i <- r | P i && a i j) F i.
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

Lemma big_pred1_seq (op : Monoid.law idx) 
    [I : eqType] (r : seq I) (i : I) (F : I -> R) :
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

Lemma ltn_sum (I : Type) (r : seq I) (P : pred I) (E1 E2 : I -> nat) :
       (forall i : I, P i -> (E1 i <= E2 i)%N) ->
       has (fun i => P i && (E1 i < E2 i)%N) r ->
       (\sum_(i <- r | P i) E1 i < \sum_(i <- r | P i) E2 i)%N.
Proof.
elim: r => [//|i r IHr] E12 /=.
rewrite !big_cons; case /boolP: (P i) => /= [Pi /orP|_ /(IHr E12)//].
case=> [E12i|/(IHr E12) {}IHr].
  by rewrite -addSn; apply/leq_add => //; apply/leq_sum.
by rewrite -addnS; apply/leq_add => //; apply/E12.
Qed.

Lemma big_ordD (op : Monoid.law idx) (n m : nat)
    (P : pred 'I_(n + m)) (F : 'I_(n + m) -> R) :
  \big[op/idx]_(i < n + m | P i) F i =
      op (\big[op/idx]_(i < n | P (lshift m i)) F (lshift m i))
         (\big[op/idx]_(i < m | P (rshift n i)) F (rshift n i)).
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

(* TODO: find a suitable name *)
Lemma big_neq_0 [S : Type] [idx' : S] [op : Monoid.law idx']
    [I : eqType] (r : seq I) [P : pred I] [F : I -> S] (i : I):
    uniq r ->
    (forall j, P j -> j != i -> F j = idx') ->
    \big[op/idx']_(j <- r | P j) F j = if P i && (i \in r) then F i else idx'.
Proof.
move=> + iP; elim: r => [|j r IHr].
  by rewrite in_nil big_nil andbF.
rewrite big_cons; move: (iP j).
have [-> _ /= /andP[] ir ru {j}|ji] := eqVneq j i.
  rewrite mem_head andbT big_mkcond big_seq -big_mkcondl.
  under eq_bigr => j /andP[] Pj jr.
    have ->: F j = idx'.
      move: jr; have [->|/(iP j Pj) -> _ //] := eqVneq j i.
      by rewrite (negPf ir).
    over.
  rewrite big_const_idem ?Monoid.mulm1//.
  exact/Monoid.mulm1.
rewrite in_cons eq_sym (negPf ji)/= => /[swap] /andP[_] /IHr ->.
case: (P j) => [/(_ isT isT) ->|_ //].
by rewrite Monoid.mul1m.
Qed.

End MoreBigop.

Section MoreCoef.

Open Scope ring_scope.

Lemma coefMD_wid (R : ringType) (p q : {poly R}) (m n i : nat) :
  (i < m)%N -> (i < n)%N ->
  (p * q)`_i = \sum_(j1 < m) \sum_(j2 < n | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
move=> m_big n_big; rewrite pair_big_dep.
pose tom := widen_ord m_big; pose ton := widen_ord n_big.
rewrite (reindex (fun j : 'I_i.+1 => (tom j, ton (rev_ord j)))) /=.
  rewrite coefM; apply: eq_big => //= j.
  by rewrite -maxnE (maxn_idPr _) ?eqxx ?leq_ord.
exists (fun k : 'I__ * 'I__ => insubd ord0 k.1) => /=.
  by move=> j _; apply/val_inj; rewrite val_insubd ltn_ord.
move=> [k1 k2] /=; rewrite inE /= {}/ton eq_sym => /eqP i_def.
apply/eqP; rewrite xpair_eqE -!val_eqE /= ?val_insubd i_def !ltnS.
by rewrite leq_addr eqxx /= subSS addKn.
Qed.

Lemma coefMD (R : ringType) (p q : {poly R}) (i : nat) :
 (p * q)`_i = \sum_(j1 < size p)
              \sum_(j2 < size q | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
rewrite (@coefMD_wid _ _ _ i.+1 i.+1) //=.
rewrite (bigID (fun j1 :'I__ => j1 < size p)%N) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j1; rewrite -ltnNge => j1_big.
  by rewrite big1 // => j2 _; rewrite nth_default ?mul0r.
rewrite (big_ord_exchange
 (fun j1 => \sum_(j2 < i.+1 | (j1 + j2)%N == i) p`_j1 * q`_j2)) /=.
rewrite big_mkcond /=; apply: eq_bigr => j1 _; rewrite ltnS.
have [j1_small|j1_big] := leqP; last first.
  rewrite big1 // => j2; rewrite eq_sym => /eqP i_def.
  by rewrite i_def -ltn_subRL subnn ltn0 in j1_big.
rewrite (bigID (fun j2 :'I__ => j2 < size q)%N) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j2; rewrite -ltnNge => /andP[_ j2_big].
  by rewrite [q`__]nth_default ?mulr0.
rewrite (big_ord_exchange_cond
 (fun j2 => (j1 + j2)%N == i) (fun j2 => p`_j1 * q`_j2)) /=.
rewrite big_mkcondr /=; apply: eq_bigr => k; rewrite ltnS.
have [//|j2_big] := leqP; rewrite eq_sym=> /eqP i_def.
by rewrite i_def addnC -ltn_subRL subnn ltn0 in j2_big.
Qed.

Lemma lead_coef_prod (R : idomainType) (I : Type) (r : seq I)
    (P : pred I) (F : I -> {poly R}) :
  lead_coef (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) lead_coef (F i).
Proof.
elim: r => [|i r IHr]; first by rewrite !big_nil lead_coef1.
rewrite !big_cons; case: (P i) => //.
by rewrite lead_coefM IHr.
Qed.

Lemma gt_size (R : semiRingType) (p : {poly R}) (n : nat) :
  p`_n != 0 -> (n < size p)%N.
Proof.
by rewrite ltnNge => /eqP pn; apply/negP => /leq_sizeP/(_ n (leqnn _)).
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

Lemma lead_coef_deriv (R : idomainType) (p : {poly R}) :
  [char R] =i pred0 ->
  lead_coef p^`() = lead_coef p *+ (size p).-1.
Proof.
move=> R0.
rewrite !lead_coefE coef_deriv (size_deriv p R0).
case: (ltnP 1 (size p)) => [|p1]; first by case: (size p) => [//|]; case.
move/leq_predn: (p1); rewrite leqn0 => /eqP ->.
by rewrite mulr0n/= nth_default.
Qed.

End MoreCoef.

Section MorePolyDvd.

Lemma dvdp_prod (A : idomainType) (I : Type) (r : seq I)
    (P : pred I) (F G : I -> {poly A}) :
  (forall i, P i -> F i %| G i)%R ->
  (\prod_(i <- r | P i) F i %| \prod_(i <- r | P i) G i)%R.
Proof.
move=> FG; elim: r => [|i r IHr]; first by rewrite !big_nil dvd1p.
rewrite !big_cons; case/boolP: (P i) => [Pi|//].
by apply/dvdp_mul => //; apply/FG.
Qed.

Lemma divp_prod_dvdp (A : fieldType) (I : Type) (r : seq I)
    (P : pred I) (F G : I -> {poly A}) :
  (forall i, P i -> G i %| F i)%R ->
  (\prod_(i <- r | P i) F i %/ \prod_(i <- r | P i) G i =
      \prod_(i <- r | P i) (F i %/ G i))%R.
Proof.
move=> FG; elim: r => [|i r IHr]; first by rewrite !big_nil divp1.
rewrite !big_cons; case/boolP: (P i) => [Pi|//].
rewrite -divp_divl mulrC -divp_mulA ?FG// mulrC -divp_mulA ?IHr//.
exact/dvdp_prod.
Qed.

End MorePolyDvd.

Section MoreRoot.

Local Open Scope ring_scope.

Lemma mu_XsubC (R : idomainType) (x y : R) :
  \mu_x ('X - y%:P) = (x == y).
Proof.
have [->|xy] := eqVneq x y; first exact: mu_XsubC.
by rewrite muNroot// root_XsubC.
Qed.

Lemma mu_prod [R : idomainType] (I : Type) (s : seq I)
    (P : pred I) (F : I -> {poly R}) (x : R) :
  \prod_(i <- s | P i) F i != 0 ->
  \mu_x (\prod_(i <- s | P i) F i) = \sum_(i <- s | P i) \mu_x (F i).
Proof.
elim: s => [|p s IHs].
  rewrite !big_nil => _; apply/muNroot/root1.
rewrite !big_cons; case: (P p) => // ps0.
rewrite mu_mul//; move: ps0; rewrite mulf_eq0 negb_or => /andP[] p0 s0.
by rewrite IHs.
Qed.

(* N.B. `multiplicity` should be generalized to `ringType`. *)
Lemma multiplicity_map (aR : fieldType) (rR : idomainType)
    (f : {rmorphism aR -> rR}) (p : {poly aR}) (x : aR) :
  \mu_(f x) (map_poly f p) = \mu_x p.
Proof.
have [->|p0] := eqVneq p 0; first by rewrite map_poly0 !mu0.
rewrite {2}/multiplicity.
case: (multiplicity_XsubC p x) => /= n [] q /implyP/(_ p0) qx pE.
rewrite (negPf p0) pE rmorphM/= mu_mul; last first.
  by rewrite -rmorphM/= -pE map_poly_eq0.
rewrite rmorphXn/= rmorphB/= map_polyX map_polyC mu_exp mu_XsubC eqxx mul1n.
rewrite muNroot//; move: qx; apply/contraNN; rewrite rootE.
by rewrite horner_map fmorph_eq0.
Qed.


(* What is the root_bigmul in mathcomp??? *)
Lemma root_bigmul [R : idomainType] [I : Type] (x : R) (s : seq I)
    (P : pred I) (F : I -> {poly R}) :
  root (\prod_(i <- s | P i) F i) x = has (fun i : I => P i && root (F i) x) s.
Proof.
elim: s => [|y s IHs]; first by rewrite big_nil (negPf (root1 _)).
by rewrite big_cons/=; case: (P y) => //; rewrite rootM IHs.
Qed.

Lemma in_rootsR (R : rcfType)
  (P : {poly R}) (x : R) :
  x \in rootsR P = (P != 0) && (root P x).
Proof.
rewrite andbC /rootsR in_roots; case/boolP: (root P x) => [|//] /= /rootP Px.
rewrite andbC; have [//|/= P0] := eqVneq P 0.
by rewrite interval.itv_boundlr/= !interval.leBSide/= -ltr_norml cauchy_boundP.
Qed.

Lemma rootsRPE (R : rcfType) d (p : {poly R}) (z : d.-tuple R) :
  (forall i, root p (tnth z i))
  -> (forall x, root p x -> x \in z)
  -> sorted <%R z
  -> (z : seq R) = rootsR p.
Proof.
have [-> _ z0P _|p0] := eqVneq p 0.
  rewrite rootsR0.
  move: z0P => /(_ (1 + \big[Order.max/0]_(x <- z) x) (root0 _)).
  move=> /tnthP-[] i ziE.
  suff: (tnth z i <= tnth z i - 1).
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

Definition dec_roots (F : decFieldType) (p : {poly F}) : seq F :=
  if p == 0 then [::] else
  [seq x <- undup (projT1 (dec_factor_theorem p)) | root p x].

Lemma uniq_dec_roots (F : decFieldType) (p : {poly F}) :
  uniq (dec_roots p).
Proof.
by rewrite /dec_roots; case: (p == 0) => //; apply/filter_uniq/undup_uniq.
Qed.

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
  exists q : {poly F},
    p = (q * \prod_(x <- dec_roots p) ('X - x%:P) ^+ (\mu_x p)) /\
    (q != 0 -> forall x : F, ~~ root q x).
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

Lemma dec_roots_closedP (F : closedFieldType) (p : {poly F}) :
  (p = p`_(size p).-1 *: \prod_(x <- dec_roots p) ('X - x%:P) ^+ (\mu_x p)).
Proof.
have [->|p0] := eqVneq p 0; first by rewrite coef0 scale0r.
move: (dec_rootsP p) => [q].
have [->|q0 [pE]/(_ isT) qr] := eqVneq q 0.
  by rewrite mul0r => [][p0']; move/eqP: p0.
have [sq|/closed_rootP [x]] := eqVneq (size q) 1; last by move/negP: (qr x).
have /size1_polyC qE : (size q <= 1)%N by rewrite sq.
rewrite {1}pE qE mul_polyC; congr (_ *: _).
move/(congr1 lead_coef): pE.
rewrite lead_coefM lead_coef_prod.
under eq_bigr do rewrite lead_coef_exp lead_coefXsubC expr1n.
by rewrite big_const_idem/= ?mulr1// qE lead_coefC lead_coefE coefC/=.
Qed.

Lemma dec_roots0 (F : decFieldType) : (@dec_roots F 0) = [::].
Proof.
case rE: (dec_roots 0) => [//|x r].
by move: (mem_head x r); rewrite -rE mem_dec_roots eqxx.
Qed.

  
End MoreRoot.

Local Open Scope ring_scope.

Lemma subrBB (S : zmodType) (a b c : S) :
  (b - a) - (c - a) = b - c.
Proof. by rewrite opprB addrC addrCA addrAC subrr add0r. Qed.

Lemma rowPE (R : eqType) (n : nat) (u v : 'rV[R]_n) :
  (u == v) = [forall i, u ord0 i == v ord0 i].
Proof.
apply/eqP/forallP => [/rowP uv i| uv]; first by apply/eqP.
by apply/rowP => i; apply/eqP.
Qed.

Lemma cat_ffun_id (T : Type) (n m : nat) (f : 'rV[T]_(n + m)) :
  row_mx (\row_(i < n) (f ord0 (lshift _ i)))
         (\row_(j < m) (f ord0 (rshift _ j))) = f.
Proof.
apply/rowP => i; rewrite mxE.
case: fintype.splitP=> [] j /esym eq_i; rewrite mxE;
by congr (f _); apply/val_inj/eq_i.
Qed.

Section MoreComUnitRingTheory.
Variable (R : comUnitRingType).

Lemma eq_divr (a b c d : R) : b \is a GRing.unit -> d \is a GRing.unit ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> b_unit d_unit; pose canM := (can2_eq (mulrVK _) (mulrK _)).
by rewrite canM // mulrAC -canM ?unitrV ?invrK.
Qed.

Lemma mulr_div (x1 y1 x2 y2 : R) :
  (y1 \is a GRing.unit) ->
  (y2 \is a GRing.unit) -> x1 / y1 * (x2 / y2) = x1 * x2 / (y1 * y2).
Proof. by move=> y1_unit y2_unit; rewrite mulrACA -invrM ?[y2 * _]mulrC. Qed.

Lemma addr_div (x1 y1 x2 y2 : R) :
  y1 \is a GRing.unit -> y2 \is a GRing.unit ->
  x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof.
move => y1_unit y2_unit.
by rewrite mulrDl [X in (_ * y1) / X]mulrC -!mulr_div ?divrr // !mulr1.
Qed.

End MoreComUnitRingTheory.

Lemma sgz_invr (F : numFieldType) (x : F) :
  sgz x^-1 = sgz x.
Proof. by rewrite /sgz invr_eq0 invr_lt0. Qed.

Section MoreFieldTheory.

Variable (K : fieldType).

Lemma eq_divf (a b c d : K) : b != 0 -> d != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof. by move=> b_neq0 d_neq0; rewrite eq_divr ?unitfE. Qed.

Lemma eq_divfC (a b c d : K) : a != 0 -> c != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> ??; rewrite -invf_div -[c / d]invf_div (inj_eq (can_inj (@invrK _))).
by rewrite eq_divf // eq_sym [a * d]mulrC [b * c]mulrC.
Qed.

Lemma eq_divf_mul (a b c d : K) : a / b != 0 -> a / b = c / d -> a * d = c * b.
Proof.
have [->| d_neq0 ab0 /eqP] := eqVneq d 0.
  by rewrite !invr0 !mulr0 => /negPf ab0 /eqP; rewrite ab0.
rewrite eq_divf //; first by move/eqP.
by apply: contraNneq ab0 => ->; rewrite invr0 mulr0.
Qed.

End MoreFieldTheory.

Local Notation "p ^ f" := (map_poly f p).

Section AuxiliaryResults.

Variable (R : ringType).
Implicit Types (p : {poly R}).

Lemma map_poly_mul (c : R) p : p ^ ( *%R c) = c *: p.
Proof. by apply/polyP => i; rewrite coefZ coef_map_id0 ?mulr0. Qed.

Lemma lead_coefMXn p (n : nat) : lead_coef (p * 'X^n) = lead_coef p.
Proof. by rewrite lead_coef_Mmonic ?monicXn //. Qed.

Lemma size_polyMXn p (n : nat) : p != 0 -> size (p * 'X^n) = (size p + n)%N.
Proof. by move=> ?; rewrite size_Mmonic ?monicXn // size_polyXn addnS. Qed.

Lemma widen_poly (E : nat -> R) (a b : nat) : (a <= b)%N ->
  (forall j, (a <= j < b)%N -> E j = 0) ->
  \poly_(i < a) E i = \poly_(i < b) E i.
Proof.
move=> leq_a_b E_eq0; apply/polyP => k; rewrite !coef_poly.
have [lt_ka|le_ak] := ltnP k a; first by rewrite (leq_trans lt_ka).
by have [lt_kb|//] := ifPn; rewrite E_eq0 // le_ak lt_kb.
Qed.

Lemma deriv_sum (T : Type) (s : seq T) (F : T -> {poly R}) (P : pred T):
  deriv (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) deriv (F i).
Proof. by apply: big_morph; [exact: derivD|exact: deriv0]. Qed.

Lemma poly_rcons (s : seq R) : Poly (rcons s 0) = Poly s.
Proof.
elim: s => [|a l ihs].
+ rewrite rcons_nil; apply/val_inj => /=.
  by rewrite polyseq_cons nil_poly polyC0 eqxx.
+ rewrite rcons_cons; apply/val_inj => /=.
  by rewrite ihs.
Qed.

Lemma poly_cat_nseq (s : seq R) (n : nat) : Poly (s ++ (nseq n 0)) = Poly s.
Proof.
elim: n => [|n ihn] ; first by rewrite cats0.
by rewrite nseqS -rcons_cat poly_rcons ihn.
Qed.

Lemma coef0M (p q : {poly R}) : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed.

Variable (K : fieldType).

(* p : {poly K} can be generalize ? *)
Fact modp_sumn (I : Type) (r : seq I) (P : pred I)
               (F : I -> {poly K}) (p : {poly K}) :
               (\sum_(i <- r | P i) F i) %% p = \sum_(i <- r | P i) (F i %% p).
Proof. by rewrite (big_morph ((@modp _)^~ p) (modpD _) (mod0p _) _). Qed.

Fact modp_mul2 (p q m : {poly K}): ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

End AuxiliaryResults.

Lemma raddf_inj (R S : zmodType) (f : {additive R -> S}) :
   (forall x, f x = 0 -> x = 0) -> injective f.
Proof.
move=> f_inj x y /eqP; rewrite -subr_eq0 -raddfB => /eqP /f_inj /eqP.
by rewrite subr_eq0 => /eqP.
Qed.

(* Section InjectiveTheory.

Variable (R S : ringType) (f : {injmorphism R -> S}).

Lemma rmorph_inj : injective f. Proof. by case: f => [? []]. Qed.

Lemma rmorph_eq (x y : R) : (f x == f y) = (x == y).
Proof. by rewrite (inj_eq (rmorph_inj)). Qed.

Lemma rmorph_eq0 (x : R) : (f x == 0) = (x == 0).
Proof. by rewrite -(rmorph0 f) (inj_eq (rmorph_inj)). Qed.

Definition map_poly_injective : injective (map_poly f).
Proof.
move=> p q /polyP eq_pq; apply/polyP=> i; have := eq_pq i.
by rewrite !coef_map => /rmorph_inj.
Qed.

Canonical map_poly_is_injective := InjMorphism map_poly_injective.

End InjectiveTheory.
Hint Resolve rmorph_inj. 

Canonical polyC_is_injective (R : ringType) := InjMorphism (@polyC_inj R).

Canonical comp_is_injmorphism (R S T : ringType)
  (f : {injmorphism R -> S}) (g : {injmorphism S -> T}) :=
  InjMorphism (inj_comp (@rmorph_inj _ _ g) (@rmorph_inj _ _ f)).

(* Hack to go around a bug in canonical structure resolution *)
Definition fmorph (F R : Type) (f : F -> R) := f.
Canonical fmorph_is_injmorphism (F : fieldType) (R : ringType)
  (f : {rmorphism F -> R}) :=
   InjMorphism (fmorph_inj f : injective (fmorph f)). *)

Section MoreNumDomainTheory.

Lemma ler_p1X (R : numDomainType) (x y : R) (n m : nat) :
  1 <= x -> x <= y -> (n <= m)%N -> x ^+ n <= y ^+ m.
Proof.
move=> x1 xy nm; apply/(le_trans (y:=x ^+ m)).
  rewrite -(subnK nm) exprD ler_peMl// ?exprn_ege1//.
  by rewrite exprn_ge0// (le_trans ler01 x1).
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
rewrite big_cons; case/boolP: (P i) => // Pi; apply/(lt_le_trans IHr).
by rewrite lerDr F0.
Qed.

Lemma psumr_gt0 (R : numDomainType) (I : Type) (r : seq I) 
         (P : pred I) (F : I -> R):
  (forall i : I, P i -> 0 < F i)
  -> has P r
  -> 0 < \sum_(i <- r | P i) F i.
Proof.
move=> F0 Pr; apply/sumr_gt0 => [i /F0 /ltW //|].
elim: r Pr => [//|] i r IHr /= /orP; case=> [Pi|/IHr -> //].
  by rewrite Pi F0.
by rewrite orbT.
Qed.

End MoreNumDomainTheory.

Lemma sgz_prod (R : realDomainType) (I : Type)
    (r : seq I) (P : pred I) (F : I -> R) :
  sgz (\prod_(x <- r | P x) F x) = \prod_(x <- r | P x) sgz (F x).
Proof.
elim: r => [|x r IHr]; first by rewrite !big_nil sgz1.
rewrite !big_cons; case: (P x) => //.
by rewrite sgzM IHr.
Qed.

Lemma sgz_horner (F : rcfType) (p : {poly F}) (x : F) :
  sgz p.[x] =
    sgz (lead_coef p) * (x \notin rootsR p) *
      (-1) ^+ \sum_(y <- rootsR p | x < y) (\mu_y p)%R.
Proof.
have [->|p0] := eqVneq p 0; first by rewrite horner0 lead_coef0 !sgz0 mul0r.
move: (dec_roots_closedP (map_poly (real_complex _) p)).
move=> /(congr1 (fun p => p.[x%:C%C])).
rewrite -lead_coefE lead_coef_map/= hornerZ horner_prod horner_map/=.
rewrite (bigID (fun x => complex.Im x == 0))/=.
rewrite -big_filter; move rE: (seq.filter _ _) => r.
have {}rE: perm_eq r [seq x%:C%C | x <- rootsR p].
  apply/uniq_perm.
  - by rewrite -rE; apply/filter_uniq/uniq_dec_roots.
  - by rewrite map_inj_uniq ?uniq_roots//; apply/complexI.
  move=> y.
  rewrite -rE mem_filter mem_dec_roots/= map_poly_eq0 p0/=.
  apply/idP/mapP; last first.
    move=> [] z; rewrite in_rootsR rootE => /andP[] _ pz0 ->.
    by rewrite eqxx rootE horner_map/= (inj_eq (@complexI _)).
  move=> /andP[] /eqP y0.
  rewrite [y]complexE y0 mulr0 addr0 rootE horner_map/=.
  rewrite (inj_eq (@complexI _)) => py0.
  by exists (complex.Re y) => //; rewrite in_rootsR p0.
rewrite (perm_big _ rE)/= big_map. 
under eq_bigr => y _.
  rewrite -(map_polyX (real_complex F)) -map_polyC -rmorphB -rmorphXn.
  rewrite horner_map multiplicity_map !hornerE.
  over.
rewrite -rmorph_prod.
rewrite [\prod_(_ <- dec_roots _ | _) _](bigID (fun x => 0 < complex.Im x))/=.
have im_conj: forall (z : F[i]), complex.Im z^* = - complex.Im z by case.
have pE: map_poly Num.conj_op (map_poly (real_complex F) p)
    = (map_poly (real_complex F) p).
  by rewrite -map_poly_comp; apply/eq_map_poly => z/=; rewrite oppr0.
rewrite -[\prod_(_ <- _ | _ && ~~ _) _]big_filter.
have iE: perm_eq
    [seq i <- dec_roots (map_poly (real_complex F) p) |
        complex.Im i != 0 & ~~ (0 < complex.Im i)]
    [seq x^* |
        x <- [seq i <- dec_roots (map_poly (real_complex F) p) |
                complex.Im i != 0 & (0 < complex.Im i)]].
  apply/uniq_perm.
  - exact/filter_uniq/uniq_dec_roots.
  - rewrite map_inj_uniq; last exact/(inv_inj conjCK).
    exact/filter_uniq/uniq_dec_roots.
  move=> y.
  rewrite -{2}[y]conjCK mem_map; last exact/(inv_inj conjCK).
  rewrite !mem_filter/= im_conj oppr_eq0 oppr_gt0 -leNgt.
  case/boolP: (_ == _) => [//|] /negPf yi0 /=.
  rewrite le_eqVlt yi0/= !mem_dec_roots.
  by rewrite -(fmorph_root Num.conj_op) pE.
rewrite (perm_big _ iE) big_map big_filter/= -big_split/=.
under [\prod_(_ <- _ | _ && _) _]eq_bigr => y _.
  rewrite -hornerM -{2}pE multiplicity_map -exprMn horner_exp !hornerE.
  rewrite -{2}conjc_real -rmorphB/= -normCK -exprM -(RRe_real (normr_real _)).
  rewrite -rmorphXn/=.
  over.
rewrite -rmorph_prod/= -!rmorphM/= => /complexI ->; rewrite !sgzM.
rewrite mulrA -[RHS]mulrA -[RHS]mulr1; congr (_ * _ * _); last first.
  apply/gtr0_sgz/prodr_gt0 => y /andP[] y0 _.
  apply/exprn_gt0; rewrite -ltcR (@normr_gt0 _ F[i]) subr_eq0.
  apply/eqP => /(congr1 (@complex.Im _))/=.
  by move: y0 => /[swap] <-; rewrite eqxx.
case /boolP: (x \in rootsR p) => xr /=.
  apply/eqP; rewrite mul0r sgz_eq0 prodf_seq_eq0.
  apply/hasP; exists x => //=.
  rewrite subrr expr0n mu_eq0//.
  by move: xr; rewrite in_rootsR => /andP[_] ->.
rewrite mul1r sgz_prod.
under eq_bigr do rewrite sgzX.
rewrite (bigID (fun y => x < y))/=.
under eq_bigr => y xy.
  have ->: sgz (x - y) = -1 by apply/ltr0_sgz; rewrite subr_lt0.
  over.
rewrite prodrXr -[RHS]mulr1; congr (_ * _). 
rewrite big_mkcond big_seq -big_mkcondl/=.
under eq_bigr => y /andP[] yx yr.
  have ->: sgz (x - y) = 1.
    move: yx; rewrite -leNgt le_eqVlt => /orP[/eqP|] yx.
      by move/negP: xr; rewrite -yx.
    by apply/gtr0_sgz; rewrite subr_gt0.
  rewrite expr1n.
  over.
by rewrite big_const_seq iter_mulr_1 expr1n.
Qed.

Section MoreAnalysis.

Lemma mem_preimage (T U : Type) (f : T -> U) (s : set U) (x : T) :
  x \in (f @^-1` s)%classic = (f x \in s).
Proof. by []. Qed.

Lemma open_subspace_setT (T : topologicalType) (A : set T) :
  open (A : set (subspace setT)) = open A.
Proof.
rewrite !openE/=; congr (A `<=` _)%classic.
by apply/seteqP; split; apply/subsetP => x;
  rewrite /interior !inE nbhs_subspaceT.
Qed.

Lemma open_bigcap (T : topologicalType) (I : Type) (r : seq I) (P : pred I)
  (F : I -> set T) :
  (forall i, P i -> open (F i)) -> open (\big[setI/setT]_(i <- r | P i) F i).
Proof.
move=> Fopen; elim: r => [|i r IHr].
  rewrite big_nil; exact/openT.
rewrite big_cons; case/boolP: (P i) => // Pi; apply/openI => //.
exact/Fopen.
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

Lemma continuousX [K : numFieldType] [T : topologicalType]
    (s : T -> K) (n : nat) (x : T) :
  {for x, continuous s} -> {for x, continuous (fun x => s x ^+ n)}.
Proof. by move=> f_cont; apply: cvgX. Qed.

(* N.B. I do not need a numFieldType. *)
Lemma cvg_big {K : topologicalType} {T : Type} [F : set_system T] [I : Type]
    (r : seq I) (P : pred I) (Ff : I -> T -> K) (Fa : I -> K)
    (op : K -> K -> K) (x0 : K):
  Filter F ->
  (forall (f g : T -> K) (a b : K),
    cvg_to (nbhs (fmap f (nbhs F))) (nbhs a) ->
    cvg_to (nbhs (fmap g (nbhs F))) (nbhs b) ->
    cvg_to (nbhs (fmap (fun x => op (f x) (g x)) (nbhs F))) (nbhs (op a b))) ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \big[op/x0]_(i <- r | P i) (Ff i x))) (nbhs F)))
         (nbhs (\big[op/x0]_(i <- r | P i) Fa i)).
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

Lemma continuous_big [K T : topologicalType] [I : Type] (r : seq I)
    (P : pred I) (F : I -> T -> K) (op : K -> K -> K) (x0 : K) (x : T) :
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

Lemma cvg_sum {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}
    [F : set_system T] [I : Type] (r : seq I) (P : pred I)
    (Ff : I -> T -> V) (Fa : I -> V):
  Filter F ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \sum_(i <- r | P i) (Ff i x))) (nbhs F)))
         (nbhs (\sum_(i <- r | P i) Fa i)).
Proof.
move=> FF fa.
apply/(cvg_big FF) => // f g a b {}fa gb.
exact: cvgD.
Qed.

Lemma continuous_sum {K : numFieldType} {V : pseudoMetricNormedZmodType K}
    [T : topologicalType] [I : Type] (r : seq I)
    (P : pred I) (F : I -> T -> V) (x : T) :
  (forall i, P i -> {for x, continuous (F i)}) ->
  {for x, continuous (fun x => \sum_(i <- r | P i) F i x)}.
Proof.
move=> f_cont.
apply: continuous_big => //=.
exact: add_continuous.
Qed.

Lemma cvg_prod {K : numFieldType} {T : Type} [F : set_system T] [I : Type]
    (r : seq I) (P : pred I) (Ff : I -> T -> K) (Fa : I -> K):
  Filter F ->
  (forall i, P i -> cvg_to (nbhs (fmap (Ff i) (nbhs F))) (nbhs (Fa i))) ->
  cvg_to (nbhs (fmap ((fun x => \prod_(i <- r | P i) (Ff i x))) (nbhs F)))
         (nbhs (\prod_(i <- r | P i) Fa i)).
Proof.
move=> FF fa.
apply/(cvg_big FF) => // f g a b {}fa gb.
exact: cvgM.
Qed.

Lemma continuous_prod {K : numFieldType} [T : topologicalType] [I : Type]
    (r : seq I) (P : pred I) (F : I -> T -> K) (x : T) :
  (forall i, P i -> {for x, continuous (F i)}) ->
  {for x, continuous (fun x => \prod_(i <- r | P i) F i x)}.
Proof.
move=> f_cont.
apply: continuous_big => //=.
exact: mul_continuous.
Qed.

Lemma id_continuous {T : topologicalType} : continuous (@id T).
Proof. by apply/continuousP => A; rewrite preimage_id. Qed.

Lemma horner_continuous {K : numFieldType} (p : {poly K}) :
  continuous (horner p)%R.
Proof.
apply/(eq_continuous (f:=fun x : K => \sum_(i < size p) p`_i * x ^+ i)) => x.
  by rewrite -[p in RHS]coefK horner_poly.
apply/(@continuous_sum _ K^o).
move=> /= i _.
apply/continuousM; first exact/cst_continuous.
exact/continuousX/id_continuous.
Qed.

Lemma meval_continuous n {K : numFieldType} (p : {mpoly K[n]}) :
  continuous (fun x : 'rV[K]_n => p.@[x ord0])%R.
Proof.
apply/(eq_continuous
    (f:=fun x : 'rV[K]_n =>
      \sum_(m <- msupp p) p@_m * \prod_i x ord0 i ^+ m i)) => x.
  exact/mevalE.
apply/(@continuous_sum K K^o).
move=> /= i _.
apply/continuousM; first exact/cst_continuous.
apply/continuous_prod => j _.
exact/continuousX/coord_continuous.
Qed.

Lemma mx_continuous (T : topologicalType) (K : realFieldType) m n
    (f : T -> 'M[K]_(m.+1, n.+1)) :
  (forall i j, continuous (fun x => f x i j)) ->
  continuous f.
Proof.
move=> fc x; apply/cvg_ballP => e e0.
near=> y.
rewrite -[X in X (f x)]ball_normE/= [X in X < _]mx_normrE bigmax_lt//=.
move=> -[] i j _; rewrite !mxE/=.
suff: ball (f x i j) e (f y i j).
  by rewrite -(@ball_normE _ K^o).
move: i j.
near: y.
apply: filter_forall => i.
apply: filter_forall => j.
move: (fc i j x) => /cvg_ballP-/(_ e e0).
exact/filterS.
Unshelve. all: end_near.
Qed.

End MoreAnalysis.

Section MoreMultinomials.
Variable (n : nat) (R : comRingType).

Lemma mevalXn (k : nat) (x : 'I_n -> R) (p : {mpoly R[n]}) :
  (p ^+ k).@[x] = p.@[x] ^+ k.
Proof.
elim: k => [|k IHk]; first by rewrite !expr0 meval1.
by rewrite !exprS mevalM IHk.
Qed.

Lemma meval_mwiden (v : 'I_n.+1 -> R) (P : {mpoly R[n]}) :
  (mwiden P).@[v] = P.@[fun i => v (widen_ord (leqnSn n) i)].
Proof.
rewrite (mpolyE P) !rmorph_sum/= -mpolyE.
apply/eq_bigr => i _; rewrite rmorphM/= mevalZ mevalC mevalX; congr (_ * _)%R.
rewrite /mmap1 rmorph_prod/=; apply/eq_bigr => j _.
by rewrite rmorphXn/= mevalXU.
Qed.

Lemma meval_mmulti (v : 'I_n.+1 -> R) (P : {poly {mpoly R[n]}}) :
  (mmulti P).@[v] =
    P.[(v ord_max)%:MP_[n]].@[fun i => v (widen_ord (leqnSn n) i)].
Proof.
rewrite -[in RHS](coefK P) horner_poly !rmorph_sum/=.
apply/eq_bigr => i _.
by rewrite !rmorphM/= !rmorphXn/= mevalXU mevalC meval_mwiden.
Qed.

Lemma meval_sum [I : Type] {K : ringType} (v : 'I_n -> K) (r : seq I)
    (F : I -> {mpoly K[n]}) (P : pred I) :
  (\sum_(i <- r | P i) F i).@[v] = \sum_(i <- r | P i) (F i).@[v].
Proof. by rewrite raddf_sum. Qed.

Lemma mnmwidenE (m : 'X_{1.. n}) (i : 'I_n.+1) :
  mnmwiden m i =
  match ltnP i n with
  | LtnNotGeq ilt => m (Ordinal ilt)
  | _ => 0%N
  end.
Proof.
case: (ltnP i n) => ilt.
  by rewrite -[RHS]mnmwiden_widen; congr (mnmwiden _ _); apply/val_inj.
rewrite -[RHS](mnmwiden_ordmax m); congr (mnmwiden _ _); apply/val_inj.
apply/anti_leq/andP; split=> //.
by move: (ltn_ord i); rewrite ltnS.
Qed.

Lemma mmulti_is_additive [S : ringType] :
  additive (@mmulti n S).
Proof.
move=> /= p q; rewrite /mmulti.
rewrite (big_ord_widen
    (maxn (size p) (size q))
    (fun i => mwiden (p - q)`_i * 'X_ord_max ^+ i)%R); last first.
  by apply/(leq_trans (size_add _ _)); rewrite size_opp.
rewrite (big_ord_widen
    (maxn (size p) (size q))
    (fun i => mwiden p`_i * 'X_ord_max ^+ i)%R); last first.
  exact/leq_maxl.
rewrite (big_ord_widen
    (maxn (size p) (size q))
    (fun i => mwiden q`_i * 'X_ord_max ^+ i)%R); last first.
  exact/leq_maxr.
rewrite big_mkcond/= [in RHS]big_mkcond/= [X in _ = _ - X]big_mkcond/=.
rewrite -sumrB; apply/eq_bigr => i _.
have <-: (mwiden 0 * 'X_ord_max ^+ i)%R = 0 :> {mpoly S[n.+1]}.
  by rewrite mwiden0 mul0r.
rewrite -3!(fun_if (fun x => mwiden x * 'X_ord_max ^+ i)%R).
have ifE (x : {poly {mpoly S[n]}}): (if (i < size x)%N then x`_i else 0) = x`_i.
  by case: (ltnP i (size x)) => // ix; rewrite nth_default.
by rewrite 3!ifE coefB mwidenB mulrBl.
Qed.

HB.instance Definition _ (S : ringType) :=
  GRing.isAdditive.Build _ _ (@mmulti n S) (@mmulti_is_additive S).

Lemma mnmPE m (u v : 'X_{1.. m}) : (u == v) = [forall i : 'I_m, u i == v i].
Proof.
apply/eqP/forallP => /= [-> i|uv]; first exact: eqxx.
apply/val_inj/eq_from_tnth => i.
by move: (uv i) => /eqP; rewrite !mnm_tnth.
Qed.

Lemma forall_ordS (m : nat) (p : pred 'I_m.+1) :
  [forall i, p i] = (p ord_max && [forall i : 'I_m, p (widen_ord (leqnSn m) i)]).
Proof.
apply/forallP/andP => /= [pP|[] pm /forallP pP i].
  split; first exact/pP.
  by apply/forallP => i; apply/pP.
case: (ltnP i m) => im.
  by move: (pP (Ordinal im)); congr p; apply/val_inj.
move: pm; congr p; apply/val_inj/le_anti/andP; split; first exact im.
by move: (ltn_ord i); rewrite ltnS.
Qed.

Lemma mcoeff_muni (A : ringType) (p : {mpoly A[n.+1]})
    (i : nat) (m : 'X_{1.. n}) :
  (muni p)`_i@_m = p@_(Multinom (rcons_tuple m i)).
Proof.
rewrite (mpolyE p) !raddf_sum/= coef_sum raddf_sum/=.
apply/eq_bigr => u _.
rewrite muniZ coefZ mul_mpolyC !mcoeffZ; congr (_ * _).
rewrite muniE msuppX big_seq1 !mcoeffX eqxx scale1r coefZ coefXn.
rewrite mulr_natr raddfMn/= mcoeffX -[LHS]mulr_natr -natrM mulnb; congr ((_ _)%:R).
rewrite !mnmPE forall_ordS multinomE /tnth/= nth_rcons size_tuple ltnn eqxx.
rewrite eq_sym andbC; congr (_ && _).
apply/eq_forallb => /= j.
rewrite !multinomE tnth_map /tnth/= nth_rcons size_tuple ltn_ord nth_enum_ord.
rewrite [X in _ == X]mnm_tnth /tnth/=; congr (_ == _).
by apply/set_nth_default; rewrite size_tuple.
Qed.

Lemma mcoeff_mwiden (A : ringType) (p : {mpoly A[n]}) (m : 'X_{1.. n.+1}) :
  (mwiden p)@_m
  = p@_(Multinom (mktuple (fun i => m (widen_ord (leqnSn n) i))))
    *+ (m ord_max == 0).
Proof.
rewrite (mpolyE p).
rewrite !raddf_sum/= -(mpolyE p) -sumrMnl.
apply/eq_bigr => u _.
rewrite mul_mpolyC !mcoeffZ -mulrnAr; congr (_ * _).
set x := mmap1 _ _.
have ->: x = 'X_[Multinom (rcons_tuple u 0)].
  rewrite [RHS]mpolyXE_id big_ord_recr/= multinomE (tnth_nth 0)/= -cats1.
  rewrite nth_cat size_tuple ltnn subnn/= expr0 mulr1.
  apply/eq_bigr => i _.
  rewrite multinomE (tnth_nth 0)/= -cats1 nth_cat size_tuple.
  by rewrite (ltn_ord i) mnm_tnth (tnth_nth 0).
rewrite !mcoeffX -[RHS]mulr_natr -natrM mulnb; congr ((_ _)%:R).
rewrite !mnmPE forall_ordS multinomE /tnth/= nth_rcons size_tuple ltnn eqxx.
rewrite eq_sym andbC; congr (_ && _).
apply/eq_forallb => /= i.
rewrite !multinomE tnth_map tnth_ord_tuple /tnth/= nth_rcons size_tuple.
rewrite (ltn_ord i) [u i]mnm_tnth /tnth/=; congr (_ == _).
by apply/set_nth_default; rewrite size_tuple.
Qed.

Lemma mcoeff_mmulti (A : ringType) (p : {poly {mpoly A[n]}})
    (m : 'X_{1.. n.+1}) :
  (mmulti p)@_m
  = p`_(m ord_max)@_(Multinom (mktuple (fun i => m (widen_ord (leqnSn n) i)))).
Proof.
rewrite -(coefK p) poly_def coef_sum !raddf_sum/= -poly_def (coefK p).
apply/eq_bigr => i _.
rewrite coefZ coefXn mpolyXn mulr_natr raddfMn/=.
case: (ltnP (m ord_max) i) => [mi|im].
  rewrite (negPf (ltn_neq mi)) mulr0n.
  move xE: _@_m => x; rewrite -[RHS](mulr0 x) -xE mcoeffM mulr_suml => {x xE}.
  apply/eq_bigr => -[] /= u v /eqP mE.
  rewrite mulr0 mcoeffX mcoeff_mwiden.
  move: mi; rewrite {1}mE mnmDE.
  have [-> vi|_ _] := eqVneq (u ord_max) 0; last by rewrite mulr0n mul0r.
  rewrite mnmPE forall_ordS mulmnE mnm1E eqxx eq_sym mul1n (negPf (ltn_neq vi)).
  exact/mulr0.
move uE: (Multinom _) => u.
have /eqP ->:
    m == (U_(ord_max) *+ i + [multinom (rcons_tuple u (m ord_max - i)%N)])%MM.
  rewrite mnmPE; apply/forallP => /= j; apply/eqP.
  rewrite mnmDE mulmnE mnm1E multinomE /tnth/= nth_rcons size_tuple.
  case: (ltnP j n) => jn.
    rewrite -(inj_eq val_inj)/= [n == j]eq_sym (negPf (ltn_neq jn)) -uE.
    rewrite -(tnth_nth _ _ (Ordinal jn)) -mnm_tnth multinomE tnth_mktuple.
    by congr (_ _); apply/val_inj.
  rewrite eq_sym/= -(inj_eq val_inj); suff ->: j = ord_max.
    by rewrite eqxx/= mul1n subnKC.
  apply/val_inj/le_anti/andP; split=> //.
  by move: (ltn_ord j); rewrite ltnS.
rewrite mcoeffMX mcoeff_mwiden mnmDE mulmnE mnm1E eqxx mul1n.
rewrite -[X in (_ + _)%N == X]addn0 eqn_add2l.
under eq_mktuple => j.
  rewrite multinomE /tnth/= nth_rcons size_tuple ltn_ord -tnth_nth -uE.
  rewrite -mnm_tnth multinomE.
  over.
under eq_mktuple do rewrite tnth_mktuple.
by rewrite uE.
Qed.

Lemma muniK (A : ringType) : cancel (@muni n A) (@mmulti n A).
Proof.
move=> p; apply/mpolyP => m.
rewrite mcoeff_mmulti mcoeff_muni; congr mcoeff.
apply/mnmP => i.
rewrite multinomE (tnth_nth 0)/= -cats1 nth_cat size_map size_enum_ord.
case: (ltnP i n) => ilt.
  rewrite -/(nat_of_ord (Ordinal ilt)) nth_map_ord.
  by congr (m _); apply/val_inj.
suff ->: i = ord_max by rewrite subnn.
apply/val_inj/anti_leq/andP; split=> //.
by move: (ltn_ord i); rewrite ltnS.
Qed.

Lemma mmultiK (A : ringType) : cancel (@mmulti n A) (@muni n A).
Proof.
move=> p; apply/polyP => i; apply/mpolyP => m.
rewrite mcoeff_muni mcoeff_mmulti.
rewrite multinomE (tnth_nth 0)/= -cats1 nth_cat size_tuple ltnn subnn/=.
congr mcoeff; apply/mnmP => j.
rewrite mnmE multinomE (tnth_nth 0)/= -cats1 nth_cat size_tuple (ltn_ord j).
by rewrite -mnm_nth.
Qed.

End MoreMultinomials.

Section MoreRealClosed.
Variables (R : rcfType).

Lemma normcR (z : R) : `|z%:C%C| = `|z|%:C%C.
Proof. by rewrite normc_def/= expr0n/= addr0 sqrtr_sqr. Qed.

Lemma jump_derivp (p : {poly R}) (x : R) :
  jump p^`() p x = (root p x && (p != 0))%:R.
Proof.
rewrite /jump.
have [->|p0] := eqVneq p 0.
  by rewrite deriv0 mulr0 sgp_right0 ltxx expr0 eqxx andbF.
rewrite andbT; move: (size_deriv p (char_num R)).
have [-> /eqP|p'0 _] := eqVneq p^`() 0.
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

(* mu_eq0 is stated with rcfType in real_closed.qe_rcf_th *)
Lemma mu_eq0 (F : idomainType) (p : {poly F}) (x : F) :
  p != 0 -> (\mu_x p == 0%N) = ~~ root p x.
Proof. by move=> /mu_gt0 <-; rewrite lt0n negbK. Qed.

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

Lemma cindexR_mulCp (c : R) (p q : {poly R}) :
  cindexR (c *: p) q = sgz c * cindexR p q.
Proof.
rewrite /cindexR mulr_sumr.
by under eq_bigr do rewrite jump_mulCp.
Qed.

Lemma changes_rcons (x : R) (s : seq R) :
  changes (rcons s x) = ((last 0 s * x < 0)%R + changes s)%N.
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

Lemma changesE (s : seq R) :
  changes s = \sum_(i < (size s).-1) ((s`_i * s`_i.+1 < 0)%R : nat).
Proof.
elim: s => /= [|x + ->]; first by rewrite big_ord0.
case=> /= [|y s]; first by rewrite !big_ord0 mulr0 ltxx.
by rewrite big_ord_recl/=.
Qed.

Lemma gcdp_mul (F : closedFieldType) (p q : {poly F}) :
  p != 0 -> q != 0 ->
  gcdp p q %=
    \prod_(x <- dec_roots p) ('X - x%:P) ^+ (minn (\mu_x p) (\mu_x q)).
Proof.
move=> p0 q0.
have pq0 : gcdp p q != 0 by rewrite gcdp_eq0 (negPf p0).
have pq0' :
    \prod_(x <- dec_roots p) ('X - x%:P) ^+ minn (\mu_x p) (\mu_x q) != 0.
  rewrite prodf_seq_neq0; apply/allP => x _ /=.
  by rewrite expf_eq0 polyXsubC_eq0 andbF.
by apply/andP; split; rewrite dvdp_mu//; apply/allP => x _;
  rewrite mu_gcdp// mu_prod//;
  under eq_bigr do rewrite mu_exp mu_XsubC mulnbl eq_sym;
  rewrite -big_mkcond/= big_pred1_seq// ?uniq_dec_roots//;
  case: ifP => //; rewrite mem_dec_roots p0 => /= /negP/negP /muNroot ->;
  rewrite min0n.
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

End MoreRealClosed.

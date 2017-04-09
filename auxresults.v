(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype generic_quotient.
From mathcomp Require Import div tuple bigop ssralg poly polydiv finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section MoreLogic.

Fact aux_equivb (P : Prop) (b c : bool) : reflect P b -> b = c -> reflect P c.
Proof. by move => reflect_P_b b_eq_c ; rewrite b_eq_c in reflect_P_b. Qed.

Variables (A B C : Prop).

Lemma if_iff_compat_l : B <-> C -> (A -> B) <-> (A -> C).
Proof. by move=> h; split => h1 h2; apply/h/h1. Qed.

Lemma if_iff_compat_r : B <-> C -> (B -> A) <-> (C -> A).
Proof. by move=> h; split => h1 h2; apply/h1/h. Qed.

End MoreLogic.

Section MoreNatTheory.

Lemma lt_predn n : (n.-1 < n) = (n != 0).
Proof. by case: n => [//|n]; rewrite ltnSn. Qed.

Fact n_eq1 n : n != 0 -> n < 2 -> n = 1.
Proof. by case: n => [?|[?|[]]]. Qed.

Fact leq_npred m n : m > 0 -> (m <= n.-1) = (m < n).
Proof. by move: m n => [|m] [|n]. Qed.

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

(* Lemma nth_nrcons (x0 : T) (n : nat) (s : seq T) (x : T) (i : nat) : *)
(*  nth x0 (nrcons n x s) i = if (i < (size s) then nth x0 s i) else *)
(*  if ( < i) *)

(* nth_rcons *)
(*    forall (T : Type) (x0 : T) (s : seq T) (x : T) (n : nat), *)
(*    nth x0 (rcons s x) n = *)
(*    (if (n < size s)%N then nth x0 s n else if n == size s then x *)
(*    else x0) *)

Lemma rcons_set_nth (x y : T) (s : seq T) : (set_nth y s (size s) x) = rcons s x.
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

Lemma set_nth_nseq (i j : nat) (x y z : T) : 
  (i <= j)%N -> set_nth x (nseq j y) i z = (rcons (nseq i y) z) ++ (nseq (j - i).-1 y).
Proof.
move: i x y z; elim: j => [|j ih] i x y z; first by rewrite leqn0 => /eqP ->.
case: i => [_|i leq_ij] //=.
by rewrite ih.
Qed.

Lemma set_nth_rcons (i : nat) (e : seq T) (a x y : T) : 
  (i < size e)%N -> set_nth a (rcons e y) i x = rcons (set_nth a e i x) y.
Proof.
move: i x y; elim: e => //.
move=> b e ih i; elim: i => //.
move=> i ih2 x y /=.
by rewrite ltnS => lt_ie ; rewrite ih.
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
move: i e2 y; elim/last_ind: e1 => [i e2 y _ |e1 b ih i e2 y]; rewrite ?subn0 //.
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

Lemma set_nth_take (i : nat) (e : seq T) (j : nat) (x y : T) :(i <= j)%N -> 
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

End GeneralBaseType.

Section WithEqType.

Variables (T : eqType) (a1 a2 : pred T) (s : seq T).

Lemma sub_filter : 
    subpred a1 a2 -> {subset [seq x <- s | a1 x] <= [seq x <- s | a2 x]}.
Proof.
move=> sub_a1_a2 x ; rewrite !mem_filter.
by move/andP => [a1x ->] ; rewrite andbT sub_a1_a2.
Qed.

Lemma sub_map_filter (U : eqType) (f : T -> U) : 
subpred a1 a2 -> {subset [seq f x | x <- s & a1 x] <= [seq f x | x <- s & a2 x]}.
Proof.
move=> sub_a1_a2 x.
move/mapP => [y hy] eq_x_fy ; apply/mapP ; exists y => //.
exact: sub_filter.
Qed.

End WithEqType.

End MoreSeq.

Section MoreSeqEqType.

Variable (T : eqType).

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma perm_eq_nil (s : seq T) : (s =p [::]) = (s == [::]).
Proof.
apply/idP/idP ; last by move/eqP ->.
move => H ; apply/eqP.
by apply: perm_eq_small.
Qed.

Lemma rem_cons (s : seq T) (a : T) : rem a (a :: s) = s.
Proof. by rewrite /= eqxx. Qed.

Lemma rcons_nil (a : T) : rcons [::] a = [:: a].
Proof. by rewrite -cats1 cat0s. Qed.

Fact cat_nil (s1 s2 : seq T) : s1 ++ s2 == [::] = ((s1 == [::]) && (s2 == [::])).
Proof. by case: s1 => //= ->. Qed.

Lemma rem_is_nil (x : T) (s : seq T) : rem x s == [::] -> ((s == [::]) || (s == [:: x])).
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
  rem x (undup s) = undup (filter (predC1 x) s).
Proof.
elim: s => // y s /=.
have [<- | neq_xy] := eqVneq x y.
  rewrite eqxx fun_if /= eqxx => <-.  
  have [x_in_s | x_notin_s] := boolP (x \in s) => //.
  by rewrite rem_id // mem_undup.
rewrite eq_sym neq_xy /=.
have [y_in_s | /negbTE y_notin_s] := boolP (y \in s); rewrite mem_filter.
  by rewrite y_in_s andbT /= eq_sym neq_xy.
rewrite /= eq_sym ; move/negbTE : neq_xy => ->.
by rewrite y_notin_s andbF => ->.
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
by rewrite set_nth_id //; move: lt_ie; rewrite -subn_eq0=> /eqP->; rewrite cats0.
by rewrite set_nth_over // rcons_cat subSn // nseqS nth_default //.
Qed.

End MoreSeqEqType.

Section MoreFinmap.

Open Local Scope fset_scope.

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

End MoreFinmap.

Section MoreRelation.

Variables (T : eqType) (P : pred T) (sT : subType P) (r : equiv_rel T).

Definition sub_r (x y : sT) := r (val x) (val y).

Lemma sub_r_refl : reflexive sub_r.
Proof. by rewrite /sub_r. Qed.

Lemma sub_r_sym : symmetric sub_r.
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

End MoreBigop.

Section MoreCoef.

Open Scope ring_scope.

Lemma coefMD_wid (R : ringType) (p q : {poly R}) (m n i : nat) :
  i < m -> i < n ->
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
rewrite (bigID (fun j1 :'I__ => j1 < size p)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j1; rewrite -ltnNge => j1_big.
  by rewrite big1 // => j2 _; rewrite nth_default ?mul0r.
rewrite (big_ord_exchange
 (fun j1 => \sum_(j2 < i.+1 | (j1 + j2)%N == i) p`_j1 * q`_j2)) /=.
rewrite big_mkcond /=; apply: eq_bigr => j1 _; rewrite ltnS.
have [j1_small|j1_big] := leqP; last first.
  rewrite big1 // => j2; rewrite eq_sym => /eqP i_def.
  by rewrite i_def -ltn_subRL subnn ltn0 in j1_big.
rewrite (bigID (fun j2 :'I__ => j2 < size q)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j2; rewrite -ltnNge => /andP[_ j2_big].
  by rewrite [q`__]nth_default ?mulr0.
rewrite (big_ord_exchange_cond
 (fun j2 => (j1 + j2)%N == i) (fun j2 => p`_j1 * q`_j2)) /=.
rewrite big_mkcondr /=; apply: eq_bigr => k; rewrite ltnS.
have [//|j2_big] := leqP; rewrite eq_sym=> /eqP i_def.
by rewrite i_def addnC -ltn_subRL subnn ltn0 in j2_big.
Qed.

End MoreCoef.

Local Open Scope ring_scope.

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

Lemma widen_poly (E : nat -> R) (a b : nat) : a <= b ->
  (forall j, a <= j < b -> E j = 0) ->
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
Proof. by rewrite (big_morph ((@modp _)^~ p) (modp_add _) (mod0p _) _). Qed.

Fact modp_mul2 (p q m : {poly K}): ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

End AuxiliaryResults.

Module InjMorphism.

Section ClassDef.

Variables (R S : ringType).

Record class_of (f : R -> S) : Type :=
  Class {base : rmorphism f; mixin : injective f}.
Local Coercion base : class_of >-> rmorphism.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : injective f) :=
  fun (bF : GRing.RMorphism.map phRS) fA & phant_id (GRing.RMorphism.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical additive := GRing.Additive.Pack phRS class.
Canonical rmorphism := GRing.RMorphism.Pack phRS class.

End ClassDef.

Module Exports.
Notation injmorphism f := (class_of f).
Coercion base : injmorphism >-> GRing.RMorphism.class_of.
Coercion mixin : injmorphism >-> injective.
Coercion apply : map >-> Funclass.
Notation InjMorphism fM := (pack fM id).
Notation "{ 'injmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'injmorphism'  fRS }") : ring_scope.
Notation "[ 'injmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'injmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'injmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'injmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion rmorphism : map >-> GRing.RMorphism.map.
Canonical rmorphism.
End Exports.

End InjMorphism.
Include InjMorphism.Exports.

Section InjectiveTheory.

Lemma raddf_inj (R S : zmodType) (f : {additive R -> S}) :
   (forall x, f x = 0 -> x = 0) -> injective f.
Proof.
move=> f_inj x y /eqP; rewrite -subr_eq0 -raddfB => /eqP /f_inj /eqP.
by rewrite subr_eq0 => /eqP.
Qed.

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
  InjMorphism (fmorph_inj f : injective (fmorph f)).

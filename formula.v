Require Import ZArith Init.

From HB Require Import structures.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun generic_quotient bigop finset perm.
From mathcomp Require Import ssralg poly polydiv ssrnum mxpoly binomial finalg.
From mathcomp Require Import zmodp mxpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order finset.

From SemiAlgebraic Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope quotient_scope.
Local Open Scope type_scope.

Reserved Notation "'{formula_' n F }"
  (n at level 0, format "'{formula_' n  F }").

Fact mnfset_key : unit. Proof. exact tt. Qed.
Notation mnfset i j := (seq_fset mnfset_key (iota i j)).
Notation "f <==> g" := ((f ==> g) /\ (g ==> f))%oT (at level 0) : oterm_scope.

Section SeqFset.

Lemma fsubset_trans (T : choiceType) (B A C : {fset T}) :
  A `<=` B -> B `<=` C -> A `<=` C.
Proof. by move=> /fsubsetP AB /fsubsetP BC; apply/fsubsetP => x /AB /BC. Qed.

Lemma seq_fset_sub (d : unit) (T : choiceType) (s1 s2 : seq T) :
  reflect {subset s1 <= s2} (seq_fset d s1 `<=` seq_fset d s2).
Proof.
apply: (@equivP _ _ _ (@fsubsetP _ _ _)).
by split => h x; move/(_ x) : h; rewrite !seq_fsetE.
Qed.

Lemma nfsetE (i j : nat) : (i \in mnfset O j) = (i < j)%N.
Proof.
move: i; elim: j => [|j ih] i; first by rewrite ltn0 seq_fsetE.
case: i => [|i]; first by rewrite ltnS seq_fsetE inE leq0n.
by rewrite seq_fsetE inE mem_iota.
Qed.

Lemma mnfsetE (k i j : nat) : (k \in mnfset i j) = (i <= k < i + j)%N.
Proof. by rewrite seq_fsetE mem_iota. Qed.

Lemma card_mnfset (i j : nat) : #|` (mnfset i j)| = j.
Proof. by rewrite size_seq_fset undup_id ?iota_uniq // size_iota. Qed.

Lemma mnfset_triangle (i j k : nat) :
  mnfset i (j + k) = mnfset i j `|` mnfset (i + j) k.
Proof.
by apply/eqP/fset_eqP => x; rewrite in_fsetU !seq_fsetE iotaD mem_cat.
Qed.

Lemma mnfset_nSn (i j : nat) : mnfset i j.+1 = mnfset i j `|` [fset (i + j)%N].
Proof.
apply/eqP/fset_eqP => x; rewrite in_fsetU !seq_fsetE -addn1 iotaD mem_cat.
by rewrite in_fset1 mem_seq1.
Qed.

Lemma mnfsetU (i j k l : nat) :
let a := minn i k in
(i <= k + l -> k <= i + j ->
            mnfset i j `|` mnfset k l = mnfset a ((maxn (i + j) (k + l)) - a))%N.
Proof.
move=> a h1 h2.
apply/eqP/fset_eqP => x.
rewrite in_fsetU !seq_fsetE !mem_iota subnKC; last first.
  by rewrite leq_max (leq_trans (geq_minr _ _)).
rewrite geq_min leq_max orb_andl.
have [lt_xi|leq_ix] := ltnP x i => //=.
  by rewrite (leq_trans lt_xi) //; case (_ <= _)%N.
have [small_x|big_x] := ltnP x (i+j) => //=.
by rewrite (leq_trans h2).
Qed.

Lemma mnfset_bigop (a b : nat) :
  \bigcup_(i in 'I_b) ([fset (a + (nat_of_ord i))%N]) = mnfset a b.
Proof.
apply/eqP/fset_eqP => i; rewrite seq_fsetE /= mem_iota; apply/bigfcupP/idP.
  move=> [j hj]; rewrite in_fset1 => /eqP ->.
  by rewrite leq_addr /= ltn_add2l.
rewrite addnC; move/andP => [leq_ai].
rewrite -{1}(@subnK a i) // ltn_add2r => h; exists (Ordinal h).
  by rewrite mem_index_enum.
by rewrite in_fset1 addnC subnK.
Qed.

Lemma eq_mem_nil (T : eqType) (s : seq T) : reflect (s =i [::]) (s == [::]).
Proof.
apply: (iffP idP); first by move/eqP ->.
move=> h; apply/eqP/nilP; rewrite /nilp -all_pred0.
by apply/allP => /= x; rewrite h.
Qed.

Lemma eq_mem_sym (T : Type) (p1 p2 :mem_pred T) : p1 =i p2 -> p2 =i p1.
Proof. by move=> h x; rewrite h. Qed.

Lemma eq_iotar (a c b d : nat) : iota a b =i iota c d -> b = d.
Proof.
move=> eq_ab_cd; rewrite -(size_iota a b) -(size_iota c d).
by apply/eqP; rewrite -uniq_size_uniq ?iota_uniq.
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

Lemma eq_mnfsetr (a c b d : nat) : mnfset a b = mnfset c d -> b = d.
Proof.
move=> eq_ab_cd; apply: (@eq_iotar a c) => i.
by have /fsetP /(_ i) := eq_ab_cd; rewrite !seq_fsetE.
Qed.

Lemma eq_mnfsetl (b d a c: nat) : b != O -> mnfset a b = mnfset c d -> a = c.
Proof.
move=> b_neq0 eq_ab_cd; apply: (@eq_iotal b d) => // i.
by have /fsetP /(_ i) := eq_ab_cd; rewrite !seq_fsetE.
Qed.

Lemma mnfset_sub (a b c d : nat) :
  b != O -> (mnfset a b `<=` mnfset c d) = ((c <= a) && (a + b <= c + d))%N.
Proof.
case: b => // b _; case: d.
- rewrite addn0; apply/idP/idP.
  + by move/fsubsetP/(_ a); rewrite !seq_fsetE in_fset0 inE eqxx; move/implyP.
  + move=> /andP [leq_ca leq__c].
    by move: (leq_trans leq__c leq_ca); rewrite leqNgt addnS ltnS /= leq_addr.
- move=> d; apply/fsubsetP/idP; last first.
  + move/andP=> [leq_ca leq_bd] x; rewrite !mnfsetE; move/andP => [leq_ax lt_xb].
    by rewrite (leq_trans leq_ca) // (leq_trans lt_xb).
  + move=> h.
    apply/andP; split;
                     [move/(_ a) : h | move/(_ (a + b)%N) : h]; rewrite !mnfsetE.
    - rewrite leqnn addnS ltnS leq_addr; move/implyP.
      by rewrite implyTb => /andP [].
    - rewrite /= addnS ltnS leq_addr leqnn.
      by move/implyP; rewrite andbT => /andP [].
Qed.

Lemma m0fset (m : nat) : mnfset m 0 = fset0.
Proof. by apply/fsetP=> i; rewrite seq_fsetE in_fset0. Qed.

Lemma mnfset_eq (a b c d : nat) :
  b != O -> (mnfset a b == mnfset c d) = ((a == c) && (b == d)).
Proof.
move: b d => [|b] [|d] // _.
  by rewrite andbF; apply/eqP=>/fsetP/(_ a); rewrite !seq_fsetE !inE eqxx.
rewrite eqEfsubset !mnfset_sub // andbACA -!eqn_leq eq_sym.
by have [->|//] := altP (a =P c); rewrite eqn_add2l.
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

Lemma set_nth_rcons (T : Type) (d : T) (i : nat) (e : seq T) (x y : T) :
  (i < size e)%N -> set_nth d (rcons e y) i x = rcons (set_nth d e i x) y.
Proof.
move: i x y; elim: e => //.
move=> a e ihe i; elim: i => //.
move=> i ihi x y /=.
by rewrite ltnS => lt_ie; rewrite ihe.
Qed.

Lemma cat_ffun_id (T : Type) (n m : nat) (f : 'rV[T]_(n + m)) :
  row_mx (\row_(i < n) (f ord0 (lshift _ i)))
         (\row_(j < m) (f ord0 (rshift _ j))) = f.
Proof.
apply/rowP => i; rewrite mxE.
case: splitP=> [] j /esym eq_i; rewrite mxE;
by congr (f _); apply/val_inj/eq_i.
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

Definition same_row_env (T : Type) (d : T) (n : nat) (e1 e2 : seq T) :=
  \row_(i < n) (nth d e1 (val i)) =2 (\row_(i < n) (nth d e2 (val i)) : 'rV[T]_n).

Lemma set_nth_size (T : Type) (d : T) (n : nat) (x : n.-tuple T) (i : 'I_n) (y : T) :
  size (set_nth d x i y) == n.
Proof. by rewrite size_set_nth size_tuple; apply/eqP/maxn_idPr. Qed.

Canonical set_nth_tuple (T : Type) (d : T) (n : nat) (x : n.-tuple T) (i : 'I_n) (y : T) :=
    Tuple (set_nth_size d x i y).

End SeqFset.

Section EquivFormula.

Variable T : Type.

Definition eq_vec (v1 v2 : seq nat) : formula T :=
  if size v1 == size v2 then
  (\big[And/True]_(i < size v1) ('X_(nth 0%N v1 i) == 'X_(nth 0%N v2 i)))%oT
  else False%oT.

Fixpoint term_fv (t : GRing.term T) : {fset nat} :=
  match t with
  | 'X_i => [fset i]
  | t1 + t2 | t1 * t2 => term_fv t1 `|` term_fv t2
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => term_fv t1
  | _ => fset0
  end%T.

Fixpoint formula_fv (f : formula T) : {fset nat} :=
  match f with
  | Bool _ => fset0
  | t1 == t2 | t1 <% t2 | t1 <=% t2 => term_fv t1 `|` term_fv t2
  | Unit t1 => term_fv t1
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => formula_fv f1 `|` formula_fv f2
  | ~ f1 => formula_fv f1
  | ('exists 'X_i, g) | ('forall 'X_i, g) => formula_fv g `\ i
end%oT.

Fixpoint gen_var_seq (s : seq nat) (f : formula T) := match s with
  | [::] => f
  | i::l => ('forall 'X_i, gen_var_seq l f)
end%oT.

Definition equiv_formula (f g : formula T) :=
    gen_var_seq (enum_fset ((formula_fv f) `|` (formula_fv g))) (f <==> g)%oT.

Definition nvar n := fun f :
  formula T => (formula_fv f `<=` mnfset O n).

Record formulan n := MkFormulan
{
  underlying_formula :> formula T;
  underlying_formula_fv : nvar n underlying_formula
}.

HB.instance Definition formulan_subType n :=
  [isSub for @underlying_formula n].

Lemma fsubset_formulan_fv n (f : formulan n) :
  formula_fv f `<=` mnfset O n.
Proof. by move: f => [f hf]. Qed.

Lemma formula_fv0 (f : formulan 0) : formula_fv f = fset0.
Proof.
by apply/eqP; move: (fsubset_formulan_fv f); rewrite -fsubset0 seq_fset_nil.
Qed.

Lemma in_fv_formulan (n : nat) (f : formulan n) (i : nat) :
  i \in formula_fv f -> (i < n)%N.
Proof.
by rewrite -nfsetE; move/fsubsetP => -> //; rewrite fsubset_formulan_fv.
Qed.

Lemma nvar_formulan (n : nat) (f : formulan n) : nvar n f.
Proof. by move: f => [f hf]. Qed.

End EquivFormula.

Notation "'{formula_' n T }" := (formulan T n).

Section Nquantify.
Variable (R : Type).

Fact nquantify_key : unit. Proof. exact: tt. Qed.
Definition nquantify (n k : nat) (Q : nat -> formula R -> formula R)
                                                               (f : formula R) :=
    locked_with nquantify_key (iteri k (fun i f => (Q (n + k - i.+1)%N f)) f).

Lemma nquantSout (n k : nat) Q (f : formula R) :
    nquantify n k.+1 Q f = Q n (nquantify n.+1 k Q f).
Proof.
rewrite /nquantify !unlock /= addnK; congr (Q _ _); apply: eq_iteri => i g.
by rewrite addnS addSn.
Qed.

Lemma nquantify0 (n : nat) Q (f : formula R) : nquantify n 0 Q f = f.
Proof. by rewrite /nquantify !unlock. Qed.

Lemma nquantify1 (n : nat) Q (f : formula R) : nquantify n 1 Q f = Q n f.
Proof. by rewrite nquantSout nquantify0. Qed.

Lemma nquantify_add (m n k : nat) Q (f : formula R) :
    nquantify m (n + k) Q f = nquantify m n Q (nquantify (m + n) k Q f).
Proof.
elim: n => [|n IHn] in k m *;
  rewrite ?(nquantify0, nquantSout, addn0, addSn) //=.
by rewrite IHn addnS addSn.
Qed.

Lemma nquantSin (n k : nat) Q (f : formula R) :
    nquantify n k.+1 Q f = (nquantify n k Q (Q (n + k)%N f)).
Proof. by rewrite -addn1 nquantify_add nquantify1. Qed.

Lemma formula_fv_nforall (n k : nat) (f : formula R) :
  (formula_fv (nquantify n k Forall f)) = (formula_fv f) `\` (mnfset n k).
Proof.
elim: k => [|k h] in f *.
by rewrite nquantify0 seq_fset_nil fsetD0.
rewrite nquantSin h fsetDDl fsetUC -addn1 iotaD seq_fset_cat.
by rewrite seq_fset_cons seq_fset_nil fsetU0.
Qed.

Lemma formula_fv_nexists (n k : nat) (f : formula R) :
  (formula_fv (nquantify n k Exists f)) = (formula_fv f) `\` (mnfset n k).
Proof.
elim: k => [|k h] in f *.
by rewrite nquantify0 seq_fset_nil fsetD0.
rewrite nquantSin h fsetDDl fsetUC -addn1 iotaD seq_fset_cat.
by rewrite seq_fset_cons seq_fset_nil fsetU0.
Qed.

Fact fv_nforall (m n i : nat) (f : formula R) :
  (m <= i < m+n)%N -> i \notin formula_fv (nquantify m n Forall f).
Proof.
move=> Hi.
rewrite formula_fv_nforall in_fsetD negb_and negbK mnfsetE.
by apply/orP; left.
Qed.

Fact fv_nexists (m n i : nat) (f : formula R) :
  (m <= i < m+n)%N -> i \notin formula_fv (nquantify m n Exists f).
Proof.
move=> Hi.
rewrite formula_fv_nexists in_fsetD negb_and negbK mnfsetE.
by apply/orP; left.
Qed.

End Nquantify.

Section EncodeFormula.

Variable T : Type.

Fixpoint encode_term (t : GRing.term T) := match t with
  | 'X_i => GenTree.Node (2 * i) [::]
  | x %:T => GenTree.Leaf x
  | i%:R => GenTree.Node ((2 * i).+1) [::]
  | t1 + t2 => GenTree.Node O ((encode_term t1)::(encode_term t2)::nil)
  | - t => GenTree.Node O ((encode_term t)::nil)
  | x *+ i => GenTree.Node ((2 * i).+2) ((encode_term x)::nil)
  | t1 * t2 => GenTree.Node 1 ((encode_term t1)::(encode_term t2)::nil)
  | t ^-1 => GenTree.Node 1 ((encode_term t)::nil)
  | x ^+ i => GenTree.Node ((2 * i).+3) ((encode_term x)::nil)
end%T.

Fixpoint decode_term (t : GenTree.tree T) := match t with
  | GenTree.Leaf x => x%:T
  | GenTree.Node i s => match s with
    | [::] => if (i %% 2)%N == O then GRing.Var T (i %/ 2) else ((i.-1) %/ 2)%:R
    | e1::e2::l => if i == O then (decode_term e1) + (decode_term e2)
                             else (decode_term e1) * (decode_term e2)
    | e::l => if i == O then - (decode_term e) else
              if i == 1%N then (decode_term e)^-1 else
              if (i %% 2)%N == O then (decode_term e) *+ ((i.-2) %/ 2)
                                 else (decode_term e) ^+ ((i - 3) %/ 2)
    end
end%T.

Lemma encode_termK : cancel encode_term decode_term.
Proof.
move=> t; elim: t.
+ by move=> n /=; rewrite modnMr eqxx mulKn.
+ by move=> r.
+ by move=> n /=; rewrite {1}mulnC -addn1 modnMDl mulKn.
+ by move=> t1 h1 t2 h2 /=; rewrite h1 h2.
+ by move=> t h /=; rewrite h.
+ by move=> t h n /=; rewrite -addn2 {1}mulnC modnMDl h mulKn.
+ by move=> t1 h1 t2 h2 /=; rewrite h1 h2.
+ by move=> t h /=; rewrite h.
+ by move=> t h n /=; rewrite -addn3 {1}mulnC modnMDl h addnK mulKn.
Qed.


Fixpoint encode_formula (f : formula T) := match f with
  | Bool b => GenTree.Node b [::]
  | t1 == t2 => GenTree.Node O [:: encode_term t1; encode_term t2]
  | t1 <% t2 => GenTree.Node 1 ((encode_term t1)::(encode_term t2)::nil)
  | t1 <=% t2 => GenTree.Node 2 ((encode_term t1)::(encode_term t2)::nil)
  | Unit t => GenTree.Node O ((encode_term t)::nil)
  | f1 /\ f2 => GenTree.Node 3 ((encode_formula f1)::(encode_formula f2)::nil)
  | f1 \/ f2 => GenTree.Node 4 ((encode_formula f1)::(encode_formula f2)::nil)
  | f1 ==> f2 => GenTree.Node 5 ((encode_formula f1)::(encode_formula f2)::nil)
  | ~ f => GenTree.Node 1 ((encode_formula f)::nil)
  | ('exists 'X_i, f) => GenTree.Node (2 * i).+2 ((encode_formula f)::nil)
  | ('forall 'X_i, f) => GenTree.Node (2 * i).+3 ((encode_formula f)::nil)
end%oT.

Fixpoint decode_formula (t : GenTree.tree T) := match t with
  | GenTree.Leaf x => Unit (Const x)
  | GenTree.Node i s => match s with
    | [::] => if i == O then Bool false else Bool true
    | e1::e2::l => match i with
      | O => (decode_term e1) == (decode_term e2)
      | 1%N => (decode_term e1) <% (decode_term e2)
      | 2 => (decode_term e1) <=% (decode_term e2)
      | 3 => (decode_formula e1) /\ (decode_formula e2)
      | 4 => (decode_formula e1) \/ (decode_formula e2)
      | _ => (decode_formula e1) ==> (decode_formula e2)
      end
    | e::l => if i == O then Unit (decode_term e) else
              if i == 1%N then Not (decode_formula e) else
              if (i %% 2)%N == O
                  then ('exists 'X_((i.-2) %/ 2), decode_formula e)
                  else ('forall 'X_((i - 3) %/ 2), decode_formula e)
    end
end%oT.

Lemma encode_formulaK : cancel encode_formula decode_formula.
Proof.
move=> f; elim: f.
+ by move=> b /=; case: b.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t /=; rewrite !encode_termK.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f /= ->.
+ by move=> i f hf /=; rewrite hf -addn2 {1}mulnC modnMDl mulKn /=.
+ by move=> i f hf /=; rewrite hf -addn3 {1}mulnC modnMDl /= addnK mulKn.
Qed.

End EncodeFormula.

HB.instance Definition formula_eqType (T : eqType) :=
  Equality.copy (formula T) (can_type (@encode_formulaK T)).
HB.instance Definition formulan_eqType (T : eqType) n :=
  [Equality of {formula_n T} by <:].

HB.instance Definition formula_choiceMixin (T : choiceType) :=
  Choice.copy (formula T) (can_type (@encode_formulaK T)).
HB.instance Definition formulan_choiceType (T : choiceType) n :=
  [Choice of {formula_n T} by <:].

Section FormulaSubst.

Variable T : Type.

Lemma tsubst_id (t1 t2 : GRing.term T) (i : nat) :
  i \notin (term_fv t1) -> GRing.tsubst t1 (i, t2)%oT = t1.
Proof.
move: t2; elim: t1.
- by move=> j t2 /=; rewrite in_fset1 eq_sym => /negbTE ->.
- by move=> x t2.
- by move=> j t2 h.
- move=> t1 h1 t2 h2 t3 /=.
  rewrite in_fsetU negb_or => /andP [hi1 hi2].
  by rewrite h1 // h2.
- by move=> t1 h1 t2 /= hi; rewrite h1.
- by move=> t1 h1 j hj /= hi; rewrite h1.
- move=> t1 h1 t2 h2 t3 /=.
  rewrite in_fsetU negb_or => /andP [hi1 hi2].
  by rewrite h1 // h2.
- by move=> t1 h1 t2 /= h2; rewrite h1.
- by move=> t1 h1 j t2 /= hi; rewrite h1.
Qed.

Lemma fsubst_id (f : formula T) (t : GRing.term T) (i : nat) :
  i \notin (formula_fv f) -> fsubst f (i, t)%oT = f.
Proof.
move: t; elim: f.
- by move=> b t.
- move=> t1 t2 t3 /=.
  rewrite in_fsetU negb_or => /andP [hi1 hi2].
  by rewrite !tsubst_id.
- move=> t1 t2 t3 /=.
  rewrite in_fsetU negb_or => /andP [hi1 hi2].
  by rewrite !tsubst_id.
- move=> t1 t2 t3 /=.
  rewrite in_fsetU negb_or => /andP [hi1 hi2].
  by rewrite !tsubst_id.
- by move=> t1 t2 hi /=; rewrite tsubst_id.
- move=> f1 h1 f2 h2 t.
  rewrite in_fsetU negb_or => /andP [hi1 hi2] /=.
  by rewrite h1 // h2.
- move=> f1 h1 f2 h2 t.
  rewrite in_fsetU negb_or => /andP [hi1 hi2] /=.
  by rewrite h1 // h2.
- move=> f1 h1 f2 h2 t.
  rewrite in_fsetU negb_or => /andP [hi1 hi2] /=.
  by rewrite h1 // h2.
- by move=> f hf t /= hi; rewrite hf.
- move=> j f hf t /=.
  have [<- | /negbTE neq_ij h] := eqVneq i j; rewrite ?eqxx //.
  rewrite hf//; move: h; apply: contra.
  by rewrite in_fsetD1 neq_ij.
- move=> j f hf t /=.
  have [<- | /negbTE neq_ij h] := eqVneq i j; rewrite ?eqxx //.
  rewrite hf//; move: h; apply: contra.
  by rewrite in_fsetD1 neq_ij.
Qed.

Lemma term_fv_tsubst (i : nat) (x : T) (t : GRing.term T) :
  term_fv (GRing.tsubst t (i, (x%:T)%oT)) = (term_fv t) `\ i.
Proof.
elim: t => //=; rewrite ?fset0D //;
  do ?by move=> t1 h1 t2 h2; rewrite fsetDUl ![in LHS](h1, h2).
move=> j; have [->| /negbTE neq_ij] := eqVneq j i.
  by rewrite fsetDv.
by rewrite fset1D1 eq_sym neq_ij.
Qed.

Lemma formula_fv_fsubst (i : nat) (x : T) (f : formula T) :
    formula_fv (fsubst f (i, (x%:T)%oT)) = (formula_fv f) `\ i.
Proof.
elim: f.
+ by move=> b; rewrite fset0D.
+ by move=> t1 t2 /=; rewrite !term_fv_tsubst fsetDUl.
+ by move=> t1 t2 /=; rewrite !term_fv_tsubst fsetDUl.
+ by move=> t1 t2 /=; rewrite !term_fv_tsubst fsetDUl.
+ by move=> t /=; rewrite !term_fv_tsubst.
+ by move=> f1 h1 f2 h2 /=; rewrite fsetDUl h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite fsetDUl h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite fsetDUl h1 h2.
+ by move=> f hf.
+ move=> j f /= hf; rewrite fun_if hf.
  have [->| /negbTE neq_ij] := eqVneq j i.
    by rewrite fsetDDl //= fsetUid.
  by rewrite !fsetDDl fsetUC.
+ move=> j f h /=.
  rewrite fun_if h.
  have [->| /negbTE neq_ij] := eqVneq j i.
    by rewrite fsetDDl //= fsetUid.
  by rewrite !fsetDDl fsetUC.
Qed.

End FormulaSubst.

Section RealDomainFormula.

Variable R : realDomainType.

Lemma eval_fv (t : GRing.term R) (e : seq R):
  term_fv t = fset0 -> GRing.eval e t = GRing.eval [::] t.
Proof.
move/eqP; move=> h; elim/last_ind: e => //.
move=> s x <-; move: h; elim: t => //=.
- by move=> i; rewrite neq_fset10.
- move=> t1 h1 t2 h2.
  rewrite /= fsetU_eq0 => /andP [ht1 ht2].
  by rewrite h1 // h2.
- by move=> t /= ih h; rewrite ih.
- by move=> t1 h1 t2 h2; rewrite h1.
- move=> t1 h1 t2 h2.
  rewrite fsetU_eq0 => /andP [ht1 ht2].
  by rewrite h1 // h2.
- by move=> t ih h; rewrite ih.
- by move=> t ih i h; rewrite ih.
Qed.

Lemma nn_formula (e : seq R) (f : formula R) : holds e (~ f) <-> ~ (holds e f).
Proof. by case: f. Qed.

Lemma holds_take (n : nat) (f : {formula_n R}) (e : seq R) :
  holds (take n e) f <-> holds e f.
Proof.
move: n f; elim/last_ind : e => // e x iHe n' f.
rewrite -{2}(@rcons_set_nth _ _ 0) take_rcons.
have [lt_en'|leq_n'e] := ltnP (size e) n'.
  by rewrite take_oversize ?rcons_set_nth // ltnW.
apply: (iff_trans _ (@holds_fsubst _ _ _ _ _)).
apply: (iff_trans (@iHe _ _)) => /=.
by rewrite fsubst_id // (contra (@in_fv_formulan _ _ _ _)) // -leqNgt .
Qed.

Lemma eqn_holds (n : nat) (e1 e2 : seq R) (f : {formula_n R}) :
  same_row_env 0 n e1 e2 -> holds e1 f -> holds e2 f.
Proof.
rewrite /same_row_env => h; move/holds_take => h'.
apply/holds_take; apply: (eq_holds _ h') => i.
have [lt_in | leq_ni] := ltnP i n; last first.
  by rewrite ? nth_default ?size_take // ?(leq_trans (geq_minl _ _)).
rewrite !nth_take //.
by move/(_ ord0 (Ordinal lt_in)) : h; rewrite !mxE.
Qed.

Definition is_equiv (f g : formula R) := holds [::] (equiv_formula f g).

Lemma holds_rcons_zero (e : seq R) (f : formula R) :
    holds (rcons e 0%:R) f <-> holds e f.
Proof.
split; apply: eq_holds=> // i; rewrite nth_rcons;
by have [| /ltnW h|->] := ltngtP _ (size _)=> //; rewrite ?nth_default.
Qed.

Lemma holds_cat_nseq (i : nat) (e : seq R) (f : formula R) :
    holds (e ++ (nseq i 0)) f <-> holds e f.
Proof.
rewrite nseq_cat; move: e f; elim: i => // i ih e f.
by apply: (iff_trans _ (ih e f)); apply: holds_rcons_zero.
Qed.

Lemma holds_Nfv_ex (e : seq R) (i : nat) (f : formula R) :
  i \notin formula_fv f -> (holds e ('exists 'X_i, f) <-> holds e f).
Proof.
move=> hi; split => [[x /holds_fsubst holds_ef]| h].
  by move: holds_ef; rewrite fsubst_id.
by exists 0; apply/holds_fsubst; rewrite fsubst_id.
Qed.

Lemma holds_Nfv_all (e : seq R) (i : nat) (f : formula R) :
  i \notin formula_fv f -> (holds e ('forall 'X_i, f) <-> holds e f).
Proof.
move=> hi; split => [|holds_ef x].
  by move/(_ 0)/holds_fsubst; rewrite fsubst_id.
by apply/holds_fsubst; rewrite fsubst_id.
Qed.

Fact holds_Exists (e : seq R) (i : nat) (f : formula R) :
  holds e f -> holds e ('exists 'X_i, f).
Proof.
move => holds_ef.
have [lt_ie|le_ei] := ltnP i (size e); first by exists e`_i; rewrite set_nth_id.
by exists 0; rewrite set_nth_over //; apply/holds_rcons_zero/holds_cat_nseq.
Qed.

Lemma fv0_holds (e : seq R) f :
    formula_fv f = fset0 -> (holds e f <-> holds [::] f).
Proof.
move/eqP; move=> h; elim/last_ind: e => //.
move=> e x <-; move: h; elim: f => //.
- move=> t1 t2 /=; rewrite fsetU_eq0 => /andP [/eqP ht1 /eqP ht2].
  by rewrite !eval_fv.
- move=> t1 t2 /=; rewrite fsetU_eq0 => /andP [/eqP ht1 /eqP ht2].
  by rewrite !eval_fv.
- move=> t1 t2 /=; rewrite fsetU_eq0 => /andP [/eqP ht1 /eqP ht2].
  by rewrite !eval_fv.
- by move=> t /eqP h /=; rewrite !eval_fv.
- move=> f1 h1 f2 h2.
  rewrite fsetU_eq0 => /andP [ht1 ht2].
  move: (h1 ht1) => {h1} h1; move: (h2 ht2) => {h2} h2.
  by apply: (iff_trans (and_iff_compat_r _ _) (and_iff_compat_l _ _)).
- move=> f1 h1 f2 h2.
  rewrite fsetU_eq0 => /andP [ht1 ht2].
  move: (h1 ht1) => {h1} h1; move: (h2 ht2) => {h2} h2.
  by apply: (iff_trans (or_iff_compat_r _ _) (or_iff_compat_l _ _)).
- move=> f1 h1 f2 h2 /=.
  rewrite fsetU_eq0 => /andP [ht1 ht2].
  move: (h1 ht1) => {h1} h1; move: (h2 ht2) => {h2} h2.
  by apply: (iff_trans (if_iff_compat_r _ _) (if_iff_compat_l _ _)).
- by move=> f holds_ex_f fv_f; split => ?; apply/(holds_ex_f fv_f).
- move=> i f h.
  (* the following line causes a problem in PB if I remove /= *)
  rewrite [X in X -> _]/= fsetD_eq0 fsubset1 => /orP [h1 | fv0]; last first.
  + move/(_ fv0) : h => h.
    have hi : i \notin formula_fv f by move/eqP : fv0 ->. (* PB problem here *)
    split; move/holds_Nfv_ex => h';apply/holds_Nfv_ex => //;
    by apply/h; apply: h'.
  + rewrite -(rcons_set_nth x 0); split => [|h'].
    - move/holds_fsubst.
      by rewrite fsubst_id //=; move/eqP : h1 ->; rewrite fsetDv in_fset0.
    - apply/holds_fsubst.
      by rewrite fsubst_id //=; move/eqP : h1 ->; rewrite fsetDv in_fset0.
- move=> i f h.
  rewrite [X in X -> _]/= fsetD_eq0 fsubset1 => /orP [h1 | fv0]; last first.
  + move/(_ fv0) : h => h.
    have hi : i \notin formula_fv f by move/eqP : fv0 ->.
    split; move/holds_Nfv_all=> h'; apply/holds_Nfv_all =>//;
    by apply/h; apply: h'.
  + rewrite -(rcons_set_nth x 0); split => [|h'].
    - move/holds_fsubst.
      by rewrite fsubst_id //=; move/eqP : h1 ->; rewrite fsetDv in_fset0.
    - apply/holds_fsubst.
      by rewrite fsubst_id //=; move/eqP : h1 ->; rewrite fsetDv in_fset0.
Qed.

Lemma nforallP (k : nat) (e : seq R) (f : formula R) :
    (forall v : k.-tuple R, holds (e ++ v) f)
    <-> (holds e (nquantify (size e) k Forall f)).
Proof.
elim: k => [|k IHk] /= in e *.
  rewrite nquantify0; split.
    by move=> /(_ [tuple of [::]]); rewrite cats0.
  by move=> hef v; rewrite tuple0 cats0.
rewrite nquantSout /=; split => holdsf; last first.
  move=> v; case: (tupleP v) => x {v} v /=.
  rewrite -cat_rcons -(rcons_set_nth _ 0%:R).
  by move: v; apply/IHk; rewrite ?size_set_nth (maxn_idPl _).
move=> x; set e' := set_nth _ _ _ _.
have -> : (size e).+1 = size e' by rewrite size_set_nth (maxn_idPl _).
apply/IHk => v; suff -> : e' ++ v = e ++ [tuple of x :: v] by apply: holdsf.
by rewrite /e' /= rcons_set_nth cat_rcons.
Qed.

Lemma nexistsP (k : nat) (e : seq R) (f : formula R) :
    (exists v : k.-tuple R, holds (e ++ v) f)
    <-> (holds e (nquantify (size e) k Exists f)).
Proof.
elim: k => [|k IHk] /= in e *.
- rewrite nquantify0; split; first by move=> [v]; rewrite tuple0 cats0.
  by exists [tuple of [::]]; rewrite cats0.
- rewrite nquantSout /=; split => [[v holdsf]|[x holdsf]].
  + case: (tupleP v) => x {v} v /= in holdsf *.
    exists x; set e' := set_nth _ _ _ _.
    have -> : (size e).+1 = size e' by rewrite size_set_nth (maxn_idPl _).
    by apply/IHk; exists v; rewrite /e' /= rcons_set_nth cat_rcons.
  + move: holdsf;  set e' := set_nth _ _ _ _.
    have -> : (size e).+1 = size e' by rewrite size_set_nth (maxn_idPl _).
    move/IHk => [v]; rewrite  /e' /= rcons_set_nth cat_rcons.
    by exists [tuple of x :: v].
Qed.

Lemma nforall_is_true (f : formula R) :
    (forall (e : seq R), holds e f) ->
    forall (n i : nat) (e : seq R), holds e (nquantify n i Forall f).
Proof.
move=> h n i; elim: i => [|i IHi] in n *;
by rewrite ?(nquantify0, nquantSout) /=.
Qed.

Lemma monotonic_forall_if (i : nat) (e : seq R) (f g : formula R) :
(forall (e' : seq R), holds e' f -> holds e' g) ->
holds e ('forall 'X_i, f) -> holds e ('forall 'X_i, g).
Proof. by move=> h /= fholds x; apply/h. Qed.

Lemma monotonic_exists_if (i : nat) (e : seq R) (f g : formula R) :
(forall (e' : seq R), holds e' f -> holds e' g) ->
holds e ('exists 'X_i, f) -> holds e ('exists 'X_i, g).
Proof. by move=> h /= [x fx]; exists x; apply/h. Qed.

Lemma monotonic_nforall (n k : nat) (e : seq R) (f g : formula R) :
    (forall (e' : seq R), holds e' f -> holds e' g) ->
    holds e (nquantify n k Forall f) -> holds e (nquantify n k Forall g).
Proof.
move: n e f g; elim: k => [k e f g | k ih n e f g h].
  by rewrite !nquantify0; move/(_ e).
rewrite !nquantSin => hf.
apply: (ih n e ('forall 'X_(n + k), f)%oT) => // e'.
exact/monotonic_forall_if.
Qed.

Lemma monotonic_nexist (n k : nat) (e : seq R) (f g : formula R) :
    (forall (e' : seq R), holds e' f -> holds e' g) ->
    holds e (nquantify n k Exists f) -> holds e (nquantify n k Exists g).
Proof.
move: n e f g; elim: k => [k e f g | k ih n e f g h].
  by rewrite !nquantify0; move/(_ e).
rewrite !nquantSin => hf.
apply: (ih n e ('exists 'X_(n + k), f)%oT) => // e'.
exact/monotonic_exists_if.
Qed.

Fact monotonic_forall_iff (i : nat) (e : seq R) (f g : formula R) :
(forall (e' : seq R), holds e' f <-> holds e' g) ->
holds e ('forall 'X_i, f) <-> holds e ('forall 'X_i, g).
Proof. by move=> h; split; apply: monotonic_forall_if=> e'; move/(h e'). Qed.

Fact holds_forall (i : nat) (e : seq R) (f : formula R) :
    holds e ('forall 'X_i, f) -> holds e f.
Proof. by move=> /= /(_ e`_i); rewrite set_nth_nth; move/holds_cat_nseq. Qed.

Lemma holds_nforall (n k : nat) (e : seq R) (f : formula R) :
    holds e (nquantify n k Forall f) -> holds e f.
Proof.
move: e f; elim: k => [e f|k iHk e f h]; first by rewrite nquantify0.
apply: iHk; move: h; rewrite nquantSin; apply/monotonic_nforall => e'.
exact/holds_forall.
Qed.

Fact closed_nforall_formulan (n : nat) (f : {formula_n R}) :
    formula_fv (nquantify O n Forall f) == fset0.
Proof. by rewrite formula_fv_nforall fsetD_eq0 fsubset_formulan_fv. Qed.

Fact closed_nexists_formulan (n : nat) (f : {formula_n R}) :
    formula_fv (nquantify O n Exists f) == fset0.
Proof. by rewrite formula_fv_nexists fsetD_eq0 fsubset_formulan_fv. Qed.

End RealDomainFormula.

Section RealClosedFieldFormula.
Variable F : rcfType. (* is also a realDomainType *)

Fact qf_form_elim (f : formula F) :
  rformula f -> qf_form (@quantifier_elim _ (@wproj _) f).
Proof.
by move=> h; move/andP: (quantifier_elim_wf (@wf_QE_wproj _) h) => [qf_f _].
Qed.

Fact rform_elim (f : formula F) :
  rformula f -> rformula (@quantifier_elim _ (@wproj _) f).
Proof.
by move=> h; move/andP: (quantifier_elim_wf (@wf_QE_wproj _) h) => [_ rform_f].
Qed.

Fact elim_rformP (f : formula F) (e : seq F) :
rformula f -> reflect (holds e f) (qf_eval e (@quantifier_elim _ (@wproj _) f)).
Proof.
move=> rform_f; apply: quantifier_elim_rformP => //.
- move=> i bc /= h.
  by apply: wf_QE_wproj.
- move=> i bc /= e' h.
  by apply: valid_QE_wproj.
Qed.

Fact rcf_sat_Bool (e : seq F) (b : bool) : rcf_sat e (Bool b) = b.
Proof. by []. Qed.

Fact rcf_sat_Equal (e : seq F) (t1 t2 : GRing.term F) :
  rcf_sat e (t1 == t2) = (GRing.eval e t1 == GRing.eval e t2).
Proof. by apply/rcf_satP/idP => h; apply/eqP. Qed.

Fact rcf_sat_Lt (e : seq F) (t1 t2 : GRing.term F) :
  rcf_sat e (t1 <% t2) = (GRing.eval e t1 < GRing.eval e t2).
Proof. by apply/rcf_satP/idP. Qed.

Fact rcf_sat_Le (e : seq F) (t1 t2 : GRing.term F) :
  rcf_sat e (t1 <=% t2) = (GRing.eval e t1 <= GRing.eval e t2).
Proof. by apply/rcf_satP/idP. Qed.

Fact rcf_sat_Unit (e : seq F) (t : GRing.term F) :
  rcf_sat e (Unit t) = (GRing.eval e t \is a GRing.unit).
Proof. by apply/rcf_satP/idP. Qed.

Fact rcf_sat_And (e : seq F) (f g : formula F) :
  rcf_sat e (f /\ g) = (rcf_sat e f) && (rcf_sat e g).
Proof. by []. Qed.

Fact rcf_sat_Or (e : seq F) (f g : formula F) :
  rcf_sat e (f \/ g) = (rcf_sat e f) || (rcf_sat e g).
Proof. by []. Qed.

Fact rcf_sat_Implies (e : seq F) (f g : formula F) :
  rcf_sat e (f ==> g) = ((rcf_sat e f) ==> (rcf_sat e g)).
Proof.
by apply/rcf_satP/implyP=> /= hfg; move/rcf_satP=> h; apply/rcf_satP; apply: hfg.
Qed.

Fact rcf_sat_Not (e : seq F) (f : formula F): rcf_sat e (~ f) = ~~ (rcf_sat e f).
Proof. by []. Qed.

Lemma n_forall_formula (e : seq F) (f : formula F) (i : nat) :
    holds e (~ ('forall 'X_i, f)) <-> holds e  ('exists 'X_i, ~ f).
Proof.
split; last by move=> [x hx] h2; apply/hx/h2.
move=> /nn_formula/rcf_satP Nallf.
apply/rcf_satP; apply: contraNT Nallf => /rcf_satP NexNf.
apply/rcf_satP => /= x; apply/rcf_satP.
rewrite -[rcf_sat _ _]negbK -!rcf_sat_Not.
by apply/rcf_satP => /= Nf_holds; apply: NexNf; exists x.
Qed.

Lemma n_nforall_formula (e : seq F) (f : formula F) (a b : nat) :
  holds e (~ (nquantify a b Forall f)) <-> holds e  (nquantify a b Exists (~ f)).
Proof.
move: f; elim: b => [f|b ih f]; first by rewrite !nquantify0.
rewrite !nquantSin; split.
+ move/ih; apply: monotonic_nexist => e'.
  exact: (iffLR (n_forall_formula _ _ _)).
+ move=> h; apply/ih; move: h.
  apply: monotonic_nexist=> e'.
  exact: (iffRL (n_forall_formula _ _ _)).
Qed.

Definition simp_rcf_sat := (rcf_sat_Bool, rcf_sat_Equal, rcf_sat_Lt, rcf_sat_Le,
                            rcf_sat_Unit, rcf_sat_And, rcf_sat_Or,
                            rcf_sat_Implies, rcf_sat_Not).

Lemma rcf_sat_cat_nseq (i : nat) (e : seq F) (f : formula F) :
   rcf_sat (e ++ nseq i 0) f = rcf_sat e f.
Proof.
apply/rcf_satP/rcf_satP; first by move/holds_cat_nseq.
by move=> h; apply/holds_cat_nseq.
Qed.

Lemma rcf_sat_forall k l (E : 'I_k -> formula F) :
    rcf_sat l (\big[And/True%oT]_(i < k) E i) = [forall i, rcf_sat l (E i)].
Proof.
elim: k=> [|k Ihk] in E *.
  by rewrite big_ord0 simp_rcf_sat; symmetry; apply/forallP => -[].
rewrite -(big_andE xpredT) /= !big_ord_recl !simp_rcf_sat.
by rewrite -![qf_eval _ _]/(rcf_sat _ _) Ihk -(big_andE xpredT).
Qed.

Lemma rcf_sat_forallP k l (E : 'I_k -> formula F) :
    rcf_sat l (\big[And/True%oT]_(i < k) E i) = [forall i, rcf_sat l (E i)].
Proof.
elim: k=> [|k Ihk] in E *.
  by rewrite big_ord0; apply/rcf_satP/forallP; move=> _ // [[ ]].
rewrite big_ord_recl /=; apply/rcf_satP/forallP =>
  [[/rcf_satP E0 /rcf_satP Er] i|Eall].
  have [j->|->//] := unliftP ord0 i.
  by move: Er; rewrite Ihk; move/forallP/(_ j).
apply/rcf_satP; rewrite simp_rcf_sat Eall Ihk.
by apply/forallP=> x; apply: Eall.
Qed.

Lemma formula_fv_bigAnd (I : Type) (r : seq I) (P : pred I)
                                               (E : I -> formula F) :
formula_fv (\big[And/True%oT]_(i <- r | P i) (E i)) =
\bigcup_(i <- r | P i) (formula_fv (E i)).
Proof. exact: big_morph. Qed.

Lemma formula_fv_bigOr (I : Type) (r : seq I) (P : pred I) (E : I -> formula F) :
formula_fv (\big[Or/False%oT]_(i <- r | P i) (E i)) =
\bigcup_(i <- r | P i) (formula_fv (E i)).
Proof. exact: big_morph. Qed.

Lemma formula_fv_bigU (a : nat) (E : 'I_a -> formula F) :
formula_fv (\big[And/True%oT]_(i < a) (E i)) =
\bigcup_(i in 'I_a) (formula_fv (E i)).
Proof. exact: big_morph. Qed.

Definition is_independent (i : nat) (f : formula F) :=
forall (e : seq F), holds e ('forall 'X_i, f) <-> holds e f.

Lemma independent (f : formula F) (i : nat) :
  i \notin (formula_fv f) -> is_independent i f.
Proof. by rewrite /is_independent; case: f => *; apply: holds_Nfv_all. Qed.

Lemma fsubst_indep (i : nat) (f : formula F) (x : F) (e : seq F) :
    is_independent i f -> (holds e f) -> holds e (fsubst f (i, GRing.Const x)).
Proof. by move=> h1 h2; apply/holds_fsubst; move/h1/(_ x): h2. Qed.

Lemma is_independentP (i : nat) (f : formula F) :
  is_independent i f <->
  (forall (e : seq F) (x y : F),
     (holds (set_nth 0 e i x) f) <-> (holds (set_nth 0 e i y) f)).
Proof.
split => h e; [|split => [|h2 z]].
+ move=> x y.
  apply: (iff_trans _ (h (set_nth 0 e i y))); apply: iff_sym.
  apply: (iff_trans _ (h (set_nth 0 e i x))).
  split=> h2 u; rewrite set_set_nth eqxx;
  by move/(_ u) : h2; rewrite set_set_nth eqxx.
+ by move/(_ e`_i); rewrite set_nth_nth; move/holds_cat_nseq.
+ by apply/(h e e`_i _); rewrite set_nth_nth; apply/holds_cat_nseq.
Qed.

Lemma foldr_fsubst_indep (s : seq nat) (f : formula F) (x : F) (e : seq F) :
  (forall i : nat, i \in s -> is_independent i f) ->
  holds e (foldr (fun i : nat => (fsubst (T:=F))^~ (i, (x%R%:T)%oT)) f s) <->
  holds e f.
Proof.
move: f x e; elim: s => // a s.
move => ih f x e h.
apply: (iff_trans (holds_fsubst _ _ _ _)).
apply: (iff_trans (ih _ _ _ _)) => [j j_in_s|].
  by apply: h; rewrite inE j_in_s orbT.
have /is_independentP ha : is_independent a f by apply: h; rewrite inE eqxx.
by apply: (iff_trans (ha _ _ e`_a)); rewrite set_nth_nth; apply/holds_cat_nseq.
Qed.

Lemma indep_to_rform (f : formula F) (i : nat) :
    is_independent i (to_rform f) <-> is_independent i f.
Proof.
split=> h e.
+ apply: (iff_trans _ (to_rformP _ _)).
  apply: (iff_trans _ (h _)).
  by split; apply: monotonic_forall_if=> e2; move/to_rformP.
+ apply: iff_sym; apply: (iff_trans (to_rformP _ _)).
  apply: iff_sym; apply: (iff_trans _ (h _)).
  by split; apply: monotonic_forall_if=> e2; move/to_rformP.
Qed.

End RealClosedFieldFormula.

Section Closure.

Variable (F : Type) (n : nat).

Lemma and_formulan (f1 f2 : {formula_n F}) : nvar n (f1 /\ f2)%oT.
Proof. by rewrite /nvar fsubUset !fsubset_formulan_fv. Qed.

Canonical Structure formulan_and (f1 f2 : {formula_n F})
  := MkFormulan (and_formulan f1 f2).

Lemma implies_formulan (f1 f2 : {formula_n F}) : nvar n (f1 ==> f2)%oT.
Proof. by rewrite /nvar fsubUset !fsubset_formulan_fv. Qed.

Canonical Structure formulan_implies (f1 f2 : {formula_n F}) :=
    MkFormulan (implies_formulan f1 f2).

Lemma bool_formulan (b : bool) : @nvar F n (Bool b).
Proof. by rewrite /nvar fsub0set. Qed.

Canonical Structure formulan_bool (b : bool) := MkFormulan (bool_formulan b).

Lemma or_formulan (f1 f2 : {formula_n F}) : nvar n (f1 \/ f2)%oT.
Proof. by rewrite /nvar fsubUset !fsubset_formulan_fv. Qed.

Canonical Structure formulan_or (f1 f2 : {formula_n F}) :=
    MkFormulan (or_formulan f1 f2).

Lemma not_formulan (f : {formula_n F}) : nvar n (~ f)%oT.
Proof. by rewrite /nvar fsubset_formulan_fv. Qed.

Canonical Structure formulan_not (f : {formula_n F}) :=
  MkFormulan (not_formulan f).

Lemma exists_formulan (i : nat) (f : {formula_n F}) :
  nvar n ('exists 'X_i, f)%oT.
Proof.
by rewrite /nvar (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Canonical Structure formulan_exists (i : nat) (f : {formula_n F})
  := MkFormulan (exists_formulan i f).

Lemma forall_formulan (i : nat) (f : {formula_n F}) : nvar n ('forall 'X_i, f)%oT.
Proof.
by rewrite /nvar (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Canonical Structure formulan_forall (i : nat) (f : {formula_n F})
  := MkFormulan (forall_formulan i f).

Lemma fsubst_formulan (i : nat) (x : F) (f : {formula_n F}) :
  nvar n (fsubst f (i, (x%:T)%oT))%oT.
Proof.
rewrite /nvar formula_fv_fsubst.
by rewrite (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Canonical Structure formulan_fsubst (i : nat) (x : F) (f : {formula_n F}) :=
    MkFormulan (fsubst_formulan  i x f).

Lemma And_formulan (I : finType) (x : {formula_n F}) (r : seq I) (P : pred I) (f : I -> {formula_n F}) :
  nvar n (\big[And/x : formula F]_(i <- r | P i) f i).
Proof.
elim: r => [|i r IHr].
  rewrite big_nil; apply/fsubset_formulan_fv.
rewrite big_cons; case: (P i) => //.
exact: and_formulan (f i) (MkFormulan IHr).
Qed.

Canonical Structure formulan_And (I : finType) (x : {formula_n F}) (r : seq I) (P : pred I) (f : I -> {formula_n F}) :=
  MkFormulan (And_formulan x r P f).

Lemma Or_formulan (I : finType) (x : {formula_n F}) (r : seq I) (P : pred I) (f : I -> {formula_n F}) :
  nvar n (\big[Or/x : formula F]_(i <- r | P i) f i).
Proof.
elim: r => [|i r IHr].
  rewrite big_nil; apply/fsubset_formulan_fv.
rewrite big_cons; case: (P i) => //.
exact: or_formulan (f i) (MkFormulan IHr).
Qed.

Canonical Structure formulan_Or (I : finType) (x : {formula_n F}) (r : seq I) (P : pred I) (f : I -> {formula_n F}) :=
  MkFormulan (Or_formulan x r P f).

Lemma existsn_formulaSn (m : nat) (f : {formula_(m.+1) F}) :
  nvar m ('exists 'X_m, f)%oT.
Proof.
rewrite /nvar fsubDset (fsubset_trans (fsubset_formulan_fv _)) // => {f}.
rewrite -add1n addnC iotaD add0n seq_fset_cat fsetUC.
by rewrite seq_fset_cons seq_fset_nil fsetU0 fsubset_refl.
Qed.

Lemma existsPn_formulan (m : nat) (f : {formula_m F}) :
  nvar m.-1 ('exists 'X_m.-1, f)%oT.
Proof.
move: f; case: m => [f|k f] //=; last exact: existsn_formulaSn.
by rewrite /nvar fsubDset (fsubset_trans (fsubset_formulan_fv _)) // fsubsetUr.
Qed.

Lemma nexists_formulan m (f : {formula_m F}) :
  nvar n (nquantify n (m - n) Exists (f : formula F)).
Proof.
rewrite /nvar formula_fv_nexists fsubDset fsetUC -seq_fset_cat -iotaD.
have [/ltnW lt_mn| leq_nm] := ltnP m n; last first.
  by rewrite subnKC // fsubset_formulan_fv.
rewrite (fsubset_trans (fsubset_formulan_fv _)) //.
apply/fsubsetP=> x; rewrite !seq_fsetE !mem_iota !add0n => /andP [_ lt_xm].
by rewrite leq0n (leq_trans lt_xm) // (leq_trans lt_mn) // leq_addr.
Qed.

Canonical Structure formulan_nexists m (f : {formula_m F}) :=
    MkFormulan (nexists_formulan f).

Lemma formulaSn_proof (f : {formula_n F}) : nvar n.+1 f.
Proof.
rewrite /nvar; apply/(fsubset_trans (fsubset_formulan_fv f))/seq_fset_sub => x.
by rewrite !mem_iota => /andP[-> /=] /ltnW; rewrite !add0n ltnS.
Qed.

Definition lift_formulan (f : {formula_n F}) := MkFormulan (formulaSn_proof f).

Lemma lift_formulan_inj : injective lift_formulan.
Proof. by move=> f1 f2 /(congr1 val) h; apply: val_inj. Qed.

Lemma formuladd (p m : nat) (f : {formula_p F}) : nvar (p + m) f.
Proof.
rewrite /nvar (fsubset_trans (fsubset_formulan_fv _)) //.
apply/fsubsetP=> x; rewrite !seq_fsetE !mem_iota !add0n !leq0n.
exact: ltn_addr.
Qed.

Canonical Structure formulan_add (m p : nat) (f : {formula_m F}) :=
    MkFormulan (formuladd p f).

End Closure.

Section QuantifierElimination.
Variable (F : rcfType).

Definition subst_term s :=
 let fix sterm (t : GRing.term F) := match t with
  | 'X_i => if (i < size s)%N then 'X_(nth O s i) else 0
  | t1 + t2 => (sterm t1) + (sterm t2)
  | - t => - (sterm t)
  | t *+ i => (sterm t) *+ i
  | t1 * t2 => (sterm t1) * (sterm t2)
  | t ^-1 => (sterm t) ^-1
  | t ^+ i => (sterm t) ^+ i
  | _ => t
end%T in sterm.

Fact fv_tsubst_nil (t : GRing.term F) : term_fv (subst_term [::] t) = fset0.
Proof. by elim: t => //= t1 -> t2 ->; rewrite fsetU0. Qed.

Fact fv_tsubst (k : unit) (s : seq nat) (t : GRing.term F) :
    term_fv (subst_term s t) `<=` seq_fset k s.
Proof.
elim: t => //.
- move=> i /=.
  have [lt_is|leq_si] := ltnP i (size s); rewrite ?fsub0set //.
  by rewrite fsub1set seq_fsetE; apply/(nthP _); exists i.
- by move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
- by move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
Qed.

Fact fv_tsubst_map (k : unit) (s : seq nat) (t : GRing.term F) :
  term_fv (subst_term s t) `<=`
  seq_fset k [seq nth O s i | i <- (iota O (size s)) & (i \in term_fv t)].
Proof.
elim: t => //.
- move=> i /=.
  have [lt_is|leq_si] := ltnP i (size s); rewrite ?fsub0set //.
  rewrite fsub1set seq_fsetE; apply: map_f.
  by rewrite mem_filter in_fset1 eqxx mem_iota leq0n add0n.
- move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
  + rewrite (fsubset_trans h1) //.
    apply/seq_fset_sub; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans h2) //.
    apply/seq_fset_sub; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
  + rewrite (fsubset_trans h1) //.
    apply/seq_fset_sub; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans h2) //.
    apply/seq_fset_sub; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->; rewrite orbT.
Qed.

(* quantifier elim + evaluation of invariant variables to 0 *)
Definition qf_elim (f : formula F) : formula F :=
  let g := (quantifier_elim (@wproj _) (to_rform f)) in
  foldr (fun i h => fsubst h (i, GRing.Const 0)) g
        (enum_fset (formula_fv g `\` formula_fv f)).

Lemma fv_foldr_fsubst (f : formula F) (s : seq nat) :
  formula_fv (foldr (fun i h => fsubst h (i, GRing.Const 0)) f s) =
  (formula_fv f) `\` (seq_fset mnfset_key s).
Proof.
elim: s => [|i s ih]; first by rewrite seq_fset_nil fsetD0 // fsubset_refl.
by rewrite formula_fv_fsubst ih seq_fset_cons fsetDDl fsetUC.
Qed.

Fact qf_form_fsubst (f : formula F) (i : nat) (t : GRing.term F) :
    qf_form (fsubst f (i, t)) = (qf_form f).
Proof. by elim: f=> //=; move=> f1 -> f2 ->. Qed.

Fact qf_form_fsubstn (f : formula F) (s : seq nat) (t : GRing.term F) :
    qf_form (foldr (fun i h => fsubst h (i, t)) f s) = (qf_form f).
Proof. by elim: s => // x s ih; rewrite qf_form_fsubst ih. Qed.

Lemma qf_elim_qf (f : formula F) : qf_form (qf_elim f).
Proof. by rewrite qf_form_fsubstn qf_form_elim // to_rform_rformula. Qed.

Lemma qf_elim_fv (f : formula F) : formula_fv (qf_elim f) `<=` formula_fv f.
Proof.
rewrite fv_foldr_fsubst fsubDset; apply/fsubsetP => i.
by rewrite in_fsetU seq_fsetE in_fsetD /= => ->; rewrite andbT orNb.
Qed.

(* How to factorize both goals? *)
Lemma indep_elim (i : nat) (f : formula F) :
  rformula f ->
  (is_independent i (quantifier_elim (@wproj _) f) <-> is_independent i f).
Proof.
move=> rform_f; rewrite /is_independent.
split => h e; (split; first exact: holds_forall).
- move/(rwP (elim_rformP _ rform_f))/(rwP (qf_evalP _ (qf_form_elim rform_f))).
  move/h; apply: monotonic_forall_if=> e2 h2.
  apply/(rwP (elim_rformP _ rform_f)).
  by apply/(rwP (qf_evalP _ (qf_form_elim rform_f))).
- move/(rwP (qf_evalP _ (qf_form_elim rform_f)))/(rwP (elim_rformP _ rform_f)).
  move/h; apply: monotonic_forall_if=> e2 h2.
  apply/(rwP (qf_evalP _ (qf_form_elim rform_f))).
  by apply/(rwP (elim_rformP _ rform_f)).
Qed.

Lemma qf_elim_holdsP (f : formula F) (e : seq F) :
    reflect (holds e f) (rcf_sat e (qf_elim f)).
Proof.
apply: (equivP _ (to_rformP _ _)); apply: (equivP (rcf_satP _ _)).
apply: (iff_trans (foldr_fsubst_indep _ _ _)) => [i | ]; last first.
  apply: (iff_trans (rwP (qf_evalP _ (qf_form_elim (to_rform_rformula _))))).
  apply: iff_sym.
  by apply: (iff_trans _ (rwP (elim_rformP _ (to_rform_rformula _)))).
rewrite in_fsetD => /andP [not_fv _] e2.
apply: iff_sym.
apply: (iff_trans (rwP (qf_evalP _ (qf_form_elim (to_rform_rformula _))))).
apply: iff_sym.
apply: (iff_trans _ (rwP (elim_rformP _ (to_rform_rformula _)))).
move/(_ e2) : (independent not_fv) => h.
move: (independent not_fv) => /(indep_to_rform _ _) /(_ e2) indep.
apply: (iff_trans _ indep).
apply: monotonic_forall_iff=> e3.
apply: (iff_trans (rwP (qf_evalP _ (qf_form_elim (to_rform_rformula _))))).
apply: iff_sym.
by apply: (iff_trans _ (rwP (elim_rformP _ (to_rform_rformula _)))).
Qed.

Fixpoint qf_subst_formula s (f : formula F) := let sterm := subst_term s in
match f with
  | (t1 == t2) => (sterm t1) == (sterm t2)
  | t1 <% t2 => (sterm t1) <% (sterm t2)
  | t1 <=% t2 => (sterm t1) <=% (sterm t2)
  | Unit t => Unit (sterm t)
  | f1 /\ f2 => (qf_subst_formula s f1) /\ (qf_subst_formula s f2)
  | f1 \/ f2 => (qf_subst_formula s f1) \/ (qf_subst_formula s f2)
  | f1 ==> f2 => (qf_subst_formula s f1) ==> (qf_subst_formula s f2)
  | ~ f => ~ (qf_subst_formula s f)
  | ('forall 'X_i, _) | ('exists 'X_i, _) => False
  | _ => f
end%oT.

Definition subst_formula s (f : formula F) := qf_subst_formula s (qf_elim f).

Fact fv_subst_formula (k : unit) (s : seq nat) f :
    formula_fv (subst_formula s f) `<=` seq_fset k s.
Proof.
rewrite /subst_formula.
move: s; elim: (qf_elim f) => // {f}.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t s; rewrite fv_tsubst.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
Qed.

Fact fv_qf_subst_formula (k : unit) (s : seq nat) f :
  formula_fv (qf_subst_formula s f) `<=`
  seq_fset k [seq nth O s i | i <- (iota O (size s)) & (i \in formula_fv f)].
Proof.
move: s; elim: f => //.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map k _ _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- by move=> t s; apply: fv_tsubst_map.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/seq_fset_sub.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
Qed.

Fact fv_subst_formula_map (k : unit) (s : seq nat) f :
  formula_fv (subst_formula s f) `<=`
    seq_fset k [seq nth O s i | i <- (iota O (size s)) & (i \in formula_fv f)].
Proof.
rewrite /subst_formula.
rewrite (fsubset_trans (fv_qf_subst_formula k _ _)) //.
apply/seq_fset_sub.
apply: sub_map_filter.
move=> i.
by move/fsubsetP/(_ i): (qf_elim_fv f).
Qed.

Fact fv_subst_nil f : formula_fv (subst_formula [::] f) = fset0.
Proof.
by apply/eqP; rewrite -fsubset0 -(seq_fset_nil _ tt) fv_subst_formula.
Qed.

End QuantifierElimination.

Section SubstEnv.
Variable (F : rcfType).

Definition subst_env (s : seq nat) (e : seq F) := [seq nth 0 e i | i <- s].

Lemma subst_env_cat s1 s2 e :
    subst_env (s1 ++ s2) e = subst_env s1 e ++ subst_env s2 e.
Proof. by rewrite /subst_env map_cat. Qed.

Lemma subst_env_iota k1 k2 e1 e2 e3 : size e1 = k1 -> size e2 = k2 ->
  subst_env (iota k1 k2) (e1 ++ e2 ++ e3) = e2.
Proof.
move=> h1 h2; rewrite /subst_env; apply: (@eq_from_nth _ 0) => [ | i].
  by rewrite size_map size_iota; symmetry.
rewrite size_map size_iota => lt_ik2.
rewrite (nth_map O); last by rewrite size_iota.
by rewrite !nth_cat nth_iota // ltnNge h1 leq_addr addnC addnK h2 lt_ik2.
Qed.

Lemma subst_env_iota_catl k e1 e2 : size e1 = k ->
    subst_env (iota 0 k) (e1 ++ e2) = e1.
Proof. by move=> ?; rewrite -[e1 ++ e2]cat0s (@subst_env_iota 0). Qed.

Lemma subst_env_iota_catr k1 k2 e1 e2 : size e1 = k1 -> size e2 = k2 ->
    subst_env (iota k1 k2) (e1 ++ e2) = e2.
Proof. by move=> h1 h2; rewrite -[e1 ++ e2]cats0 -catA subst_env_iota. Qed.

Lemma subst_env_nil s : subst_env s [::] = nseq (size s) 0.
Proof.
apply: (@eq_from_nth _ 0); rewrite ?size_map ?size_nseq // => i lt_is.
by rewrite (nth_map O) // nth_nil nth_nseq if_same.
Qed.

Lemma eval_subst (e : seq F) (s : seq nat) (t : GRing.term F) :
    GRing.eval e (subst_term s t) = GRing.eval (subst_env s e) t.
Proof.
elim: t.
- move=> i //=.
  have [lt_is| leq_si] := ltnP i (size s); last first.
  + by rewrite [RHS]nth_default ?size_map // !nth_default.
  + by rewrite (nth_map i) //=; congr nth; apply: set_nth_default.
- by move=> x.
- by move=> i.
- by move=> /= t1 -> t2 ->.
- by move=> /= t ->.
- by move=> /= t -> i.
- by move=> /= t1 -> t2 ->.
- by move=> /= t ->.
- by move=> /= t -> i.
Qed.

Lemma holds_subst e s f :
    holds e (subst_formula s f) <-> holds (subst_env s e) f.
Proof.
rewrite (rwP (@qf_elim_holdsP F f _)) -(rwP (@rcf_satP _ _ _)) /subst_formula.
move: e s; elim: (qf_elim f) (qf_elim_qf f) => // {f}.
- by move=> t1 t2 ? e s /=; rewrite !eval_subst.
- by move=> t1 t2 ? e s /=; rewrite !eval_subst.
- by move=> t1 t2 ? e s /=; rewrite !eval_subst.
- by move=> t ? e s /=; rewrite eval_subst.
- by move=> f1 h1 f2 h2 /andP[??] e s /=; rewrite h1 // h2.
- by move=> f1 h1 f2 h2 /andP[??] e s /=; rewrite h1 // h2.
- by move=> f1 h1 f2 h2 /andP[??] e s /=; rewrite h1 // h2.
- by move=> f1 h1 ? e s /=; rewrite h1.
Qed.

Lemma holds_eq_vec e v1 v2 :
    holds e (eq_vec F v1 v2) <-> (subst_env v1 e) = (subst_env v2 e).
Proof.
move: v2; elim: v1 => [v2|] /=.
  by case: v2 => /=; rewrite /eq_vec ?big_ord0.
move=> a v1 ih v2 /=.
case: v2 => //= b v2.
rewrite /=.
apply: iff_sym; apply: (iff_trans (rwP (eqP ))).
rewrite eqseq_cons.
rewrite /eq_vec /= eqSS big_ord_recl /=.
split.
move=> /andP [/eqP eq_ab /eqP eq_v2].
rewrite fun_if /=; move/(ih v2) : eq_v2.
by rewrite /eq_vec; case: (_ == _).
rewrite fun_if /= => h.
apply/andP; split; first by move: h; case: (_ == _) => //; move=> [] ->.
by apply/eqP/(ih v2); move: h;rewrite /eq_vec;case: (_ == _) => //; move=> [] _.
Qed.

Lemma size_subst_env (i : nat) (t : i.-tuple nat) (e : seq F) :
  size (subst_env t e) = i.
Proof. by rewrite size_map size_tuple. Qed.

Fact subst_env_tuple_subproof (i : nat) (t : i.-tuple nat) (e : seq F) :
  size (subst_env t e) == i.
Proof. by apply/eqP/size_subst_env. Qed.

Canonical subst_env_tuple (i : nat) (t : i.-tuple nat) (e : seq F) :=
    Tuple (subst_env_tuple_subproof t e).

End SubstEnv.


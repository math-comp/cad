(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(* This file formalises semi-algebraic sets and semi-algebraic functions.    *)
(* Semi-algebraic sets are constructed by a quotient of formulae.            *)
(* The main construction is the implementation of the abstract set interface *)
(* for semi-algebraic sets and functions.                                    *)
(*                                                                           *)
(*****************************************************************************)

Require Import ZArith Init.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun generic_quotient bigop finset perm.
From mathcomp Require Import ssralg poly polydiv ssrnum mxpoly binomial finalg.
From mathcomp Require Import zmodp mxpoly mxtens qe_rcf ordered_qelim realalg.
From mathcomp Require Import matrix finmap order set polyorder polyrcf.
From SsrMultinomials Require Import mpoly.

(* Module mp := mpoly. *) 

From AuxResults Require Import auxresults.
From EllipticCurves Require Import xseq polydec.
From SubResultant Require Import subresultant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope abstract_set_scope with set.
Local Open Scope abstract_set_scope.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax Order.Def.

Local Open Scope type_scope.
Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope quotient_scope.


Reserved Notation "'{formula_' n F }"
  (n at level 0, format "'{formula_' n  F }").
Reserved Notation "{ 'SAset' F }"
  (format "{ 'SAset'  F }").
Reserved Notation "{ 'SAfun' T }"
  (format "{ 'SAfun'  T }").


Notation mnfset i j := (seq_fset (iota i j)).
Notation "f <==> g" := ((f ==> g) /\ (g ==> f))%oT (at level 0) : oterm_scope.

Section EquivFormula.

Variable T : Type.

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

Definition nvar n : pred_class := fun f :
  formula T => (formula_fv f `<=` mnfset O n).

Record formulan n := MkFormulan
{
  underlying_formula :> formula T;
  _ : nvar n underlying_formula
}.

Canonical formulan_subType n :=
  Eval hnf in [subType for @underlying_formula n].

End EquivFormula.

Notation "'{formula_' n T }" := (formulan T n).

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
+ by move=> f hf /=; rewrite hf.
+ by move=> i f hf /=; rewrite hf -addn2 {1}mulnC modnMDl mulKn /=.
+ by move=> i f hf /=; rewrite hf -addn3 {1}mulnC modnMDl /= addnK mulKn.
Qed.

End EncodeFormula.

Definition formula_eqMixin (T : eqType) := CanEqMixin (@encode_formulaK T).
Canonical formula_eqType (T : eqType) :=
  EqType (formula T) (formula_eqMixin T).
Definition formulan_eqMixin (T : eqType) n := [eqMixin of {formula_n T} by <:].
Canonical formulan_eqType (T : eqType) n :=
  EqType (formulan T n) (formulan_eqMixin T n).

Definition formula_choiceMixin (T : choiceType) :=
  CanChoiceMixin (@encode_formulaK T).
Canonical formula_choiceType (T : choiceType) :=
  ChoiceType (formula T) (formula_choiceMixin T).
Definition formulan_choiceMixin (T : choiceType) n :=
  [choiceMixin of {formula_n T} by <:].
Canonical formulan_choiceType (T : choiceType) n :=
  ChoiceType (formulan T n) (formulan_choiceMixin T n).

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
  have [<- | /negbTE neq_ij] := eqVneq i j; rewrite ?eqxx //.
  rewrite eq_sym neq_ij => h; rewrite hf //.
  move: h; apply: contra.
  by rewrite in_fsetD1 neq_ij.
- move=> j f hf t /=.
  have [<- | /negbTE neq_ij] := eqVneq i j; rewrite ?eqxx //.
  rewrite eq_sym neq_ij => h; rewrite hf //.
  move: h; apply: contra.
  by rewrite in_fsetD1 neq_ij.
Qed.

End FormulaSubst.

Section RealDomainFormula.

Variable R : realDomainType.

Definition is_equiv (f g : formula R) := holds [::] (equiv_formula f g).

Fact nquantify_key : unit. Proof. exact: tt. Qed.
Definition nquantify n k (Q : nat -> formula R -> formula R) (f : formula R) :=
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

Lemma monotonic_nforall (n k : nat) (e : seq R) (f g : formula R) :
    (forall (e' : seq R), holds e' f -> holds e' g) ->
    holds e (nquantify n k Forall f) -> holds e (nquantify n k Forall g).
Proof.
move: n e f g; elim: k => [k e f g | k ih n e f g h hf].
  by rewrite !nquantify0; move/(_ e).
rewrite nquantSin.
apply: (ih n e ('forall 'X_(n + k), f)%oT);last by move: hf;rewrite nquantSin.
move=> e' nk_f x.
by apply: h; apply: nk_f.
Qed.

Lemma monotonic_nexist (n k : nat) (e : seq R) (f g : formula R) :
    (forall (e' : seq R), holds e' f -> holds e' g) ->
    holds e (nquantify n k Exists f) -> holds e (nquantify n k Exists g).
Proof.
move: n e f g; elim: k => [k e f g|k iH n e f g h hf].
  by rewrite !nquantify0; move/(_ e).
rewrite nquantSin.
apply: (iH n e ('exists 'X_(n + k), f)%oT); last by move: hf; rewrite nquantSin.
move=> e' /= [x nk_f].
by exists x; apply: h; apply: nk_f.
Qed.

Lemma monotonic_forall_if (i : nat) (e : seq R) (f g : formula R) :
(forall (e' : seq R), holds e' f -> holds e' g) ->
holds e ('forall 'X_i, f) -> holds e ('forall 'X_i, g).
Proof.
move=> h; move: (@monotonic_nforall i 1 e f g).
by rewrite /nquantify [X in X -> _]/= !addnK !unlock => h'; apply: h'.
Qed.

Fact monotonic_forall_iff (i : nat) (e : seq R) (f g : formula R) :
(forall (e' : seq R), holds e' f <-> holds e' g) ->
holds e ('forall 'X_i, f) <-> holds e ('forall 'X_i, g).
Proof. by move=> h; split; apply: monotonic_forall_if=> e'; move/(h e'). Qed.

Lemma holds_nforall (n k : nat) (e : seq R) (f : formula R) :
    holds e (nquantify n k Forall f) -> holds e f.
Proof.
move: e f; elim: k => [e f|k iHk e f h]; first by rewrite nquantify0.
apply: iHk; move: h; rewrite nquantSin. apply: monotonic_nforall.
by move=> e'; move/(_ e'`_(n + k)); rewrite set_nth_nth; move/holds_cat_nseq.
Qed.

Fact holds_forall (i : nat) (e : seq R) (f : formula R) :
    holds e ('forall 'X_i, f) -> holds e f.
Proof.
by move=> h; apply: (@holds_nforall i 1); rewrite /nquantify /= addnK unlock.
Qed.

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

Lemma holds_Nfv_ex (e : seq F) (i : nat) (f : formula F) :
  i \notin formula_fv f -> (holds e ('exists 'X_i, f) <-> holds e f).
Proof.
move=> hi; split => [[x /holds_fsubst holds_ef]| h].
  by move: holds_ef; rewrite fsubst_id.
by exists 0; apply/holds_fsubst; rewrite fsubst_id.
Qed.

Lemma holds_Nfv_all (e : seq F) (i : nat) (f : formula F) :
  i \notin formula_fv f -> (holds e ('forall 'X_i, f) <-> holds e f).
Proof.
move=> hi; split => [|holds_ef x].
  by move/(_ 0)/holds_fsubst; rewrite fsubst_id.
by apply/holds_fsubst; rewrite fsubst_id.
Qed.

Fact holds_Exists (e : seq F) (i : nat) (f : formula F) :
  holds e f -> holds e ('exists 'X_i, f).
Proof.
move => holds_ef.
have [lt_ie|le_ei] := ltnP i (size e); first by exists e`_i; rewrite set_nth_id.
by exists 0; rewrite set_nth_over //; apply/holds_rcons_zero/holds_cat_nseq.
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

Lemma eval_fv (t : GRing.term F) (e : seq F):
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

Lemma nfsetE (i j : nat) : (i \in mnfset O j) = (i < j)%N.
Proof.
move: i; elim: j => [|j ih] i; first by rewrite ltn0 seq_fsetE.
case: i => [|i]; first by rewrite ltnS seq_fsetE inE leq0n.
by rewrite seq_fsetE inE mem_iota.
Qed.

Lemma mnfsetE (k i j : nat) : (k \in mnfset i j) = (i <= k < i + j)%N.
Proof. by rewrite seq_fsetE mem_iota. Qed.

Lemma card_mnfset (i j : nat) : #|` (mnfset i j)| = j.
Proof. by rewrite cardfsE undup_id ?iota_uniq // size_iota. Qed.

Lemma mnfset_triangle (i j k : nat) :
  mnfset i (j + k) = mnfset i j `|` mnfset (i + j) k.
Proof.
by apply/eqP/fset_eqP => x; rewrite inE !seq_fsetE iota_add mem_cat.
Qed.

Lemma mnfset_nSn (i j : nat) : mnfset i j.+1 = mnfset i j `|` [fset (i + j)%N].
Proof.
by apply/eqP/fset_eqP => x; rewrite inE !seq_fsetE -addn1 iota_add mem_cat.
Qed.

Lemma mnfsetU (i j k l : nat) :
let a := minn i k in
(i <= k + l -> k <= i + j ->
            mnfset i j `|` mnfset k l = mnfset a ((maxn (i + j) (k + l)) - a))%N.
Proof.
move=> /= h1 h2.
apply/eqP/fset_eqP => x /=.
rewrite inE !seq_fsetE !mem_iota subnKC; last first.
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
move=> [j hj]; first by rewrite in_fset1 =>/eqP ->;rewrite leq_addr /= ltn_add2l.
rewrite addnC; move/andP => [leq_ai].
rewrite -{1}(@subnK a i) // ltn_add2r => h; exists (Ordinal h) => //.
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
Proof. by apply/fsetP=> i; rewrite seq_fsetE !inE. Qed.

Lemma mnfset_eq (a b c d : nat) :
  b != O -> (mnfset a b == mnfset c d) = ((a == c) && (b == d)).
Proof.
move: b d => [|b] [|d] // _.
  by rewrite andbF; apply/eqP=>/fsetP/(_ a); rewrite !seq_fsetE !inE eqxx.
rewrite eqEfsubset !mnfset_sub // andbACA -!eqn_leq eq_sym.
by have [->|//] := altP (a =P c); rewrite eqn_add2l.
Qed.

Lemma formula_fv_nforall (n k : nat) (f : formula F) :
  (formula_fv (nquantify n k Forall f)) = (formula_fv f) `\` (mnfset n k).
Proof.
elim: k => [|k h] in f *.
by rewrite nquantify0 seq_fset_nil fsetD0.
by rewrite nquantSin h fsetDDl fsetUC -addn1 iota_add seq_fset_cat.
Qed.

Lemma formula_fv_nexists (n k : nat) (f : formula F) :
  (formula_fv (nquantify n k Exists f)) = (formula_fv f) `\` (mnfset n k).
Proof.
elim: k => [|k h] in f *.
by rewrite nquantify0 seq_fset_nil fsetD0.
by rewrite nquantSin h fsetDDl fsetUC -addn1 iota_add seq_fset_cat.
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

Section Var_n.

Variable n : nat.

(* We define a relation in formulae *)
Definition equivf (f g : formula F) :=
rcf_sat [::] (nquantify O n Forall ((f ==> g) /\ (g ==> f))).

Lemma equivf_refl : reflexive equivf.
Proof. by move=> f; apply/rcf_satP; apply: nforall_is_true => e /=. Qed.

Lemma equivf_sym : ssrbool.symmetric equivf.
Proof.
move=> f g; rewrite /equivf; move: [::] => e.
move: O => i; move: (f ==> g)%oT (g ==> f)%oT => f' g' {f} {g}.
move: i e; elim: n=> [i e | n' iHn' i e].
by rewrite !nquantify0; apply/rcf_satP/rcf_satP => [[fg gf] | [gf fg]]; split.
rewrite !nquantSout /=.
apply/rcf_satP/rcf_satP => /= [h x | h x];
                                    move/(_ x)/rcf_satP : h => h; apply/rcf_satP.
+ by rewrite -iHn'.
+ by rewrite iHn'.
Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> f g h; rewrite /equivf; move: [::] => e.
move: e O; elim: n => [|m ih] e i.
+ rewrite !nquantify0; move/rcf_satP => [h1 h2]; move/rcf_satP => [h3 h4].
  apply/rcf_satP; split => [Hg | Hh].
  - by apply: h3; apply: h1.
  - by apply: h2; apply: h4.
+ rewrite !nquantSout.
  move/rcf_satP => fg; move/rcf_satP => hf; apply/rcf_satP => x.
  apply/rcf_satP; apply: ih; apply/rcf_satP.
  - exact: fg.
  - exact: hf.
Qed.

(* we show that equivf is an equivalence *)
Canonical equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.

(* equiv_formula *)
Definition sub_equivf :=
  (@sub_r _ _ [subType of {formula_n _}] equivf_equiv).

Definition SAtype := {eq_quot sub_equivf}.
Definition SAtype_of of phant (F ^ n) := SAtype.
Identity Coercion id_type_of : SAtype_of >-> SAtype.
Local Notation "{ 'SAset' }" := (SAtype_of (Phant (F ^ n))).

Coercion SAtype_to_form (A : SAtype) : {formula_n _} := repr A.

(* we recover some structure for the quotient *)
Canonical SAset_quotType := [quotType of SAtype].
Canonical SAset_eqType := [eqType of SAtype].
Canonical SAset_choiceType := [choiceType of SAtype].
Canonical SAset_eqQuotType := [eqQuotType sub_equivf of SAtype].

Canonical SAset_of_quotType := [quotType of {SAset}].
Canonical SAset_of_eqType := [eqType of {SAset}].
Canonical SAset_of_choiceType := [choiceType of {SAset}].
Canonical SAset_of_eqQuotType := [eqQuotType sub_equivf of {SAset}].

Lemma fsubset_formulan_fv (f : {formula_n F}) : formula_fv f `<=` mnfset O n.
Proof. by move: f => [f hf]. Qed.

End Var_n.
End RealClosedFieldFormula.

Notation "{ 'SAset' F }" := (SAtype_of (Phant F)) : type_scope.

Section SemiAlgebraicSet.

Variable F : rcfType. (* is also a realDomainType *)

Lemma formula_fv0 (f : {formula_0 F}) : formula_fv f = fset0.
Proof.
by apply/eqP; move: (fsubset_formulan_fv f); rewrite -fsubset0 seq_fset_nil.
Qed.

Lemma in_fv_formulan (n : nat) (f : {formula_n F}) (i : nat) :
  i \in formula_fv f -> (i < n)%N.
Proof.
by rewrite -nfsetE; move/fsubsetP => -> //; rewrite fsubset_formulan_fv.
Qed.

Lemma nvar_formulan (n : nat) (f : {formula_n F}) : nvar n f.
Proof. by move: f => [f hf]. Qed.

Section Interpretation.

Lemma set_nth_rcons (i : nat) (e : seq F) (x y : F) :
  (i < size e)%N -> set_nth 0 (rcons e y) i x = rcons (set_nth 0 e i x) y.
Proof.
move: i x y; elim: e => //.
move=> a e ihe i; elim: i => //.
move=> i ihi x y /=.
by rewrite ltnS => lt_ie; rewrite ihe.
Qed.

Fact fv_nforall (m n i : nat) (f : formula F) :
  (m <= i < m+n)%N -> i \notin formula_fv (nquantify m n Forall f).
Proof.
move=> Hi.
rewrite formula_fv_nforall in_fsetD negb_and negbK mnfsetE.
by apply/orP; left.
Qed.

Fact fv_nexists (m n i : nat) (f : formula F) :
  (m <= i < m+n)%N -> i \notin formula_fv (nquantify m n Exists f).
Proof.
move=> Hi.
rewrite formula_fv_nexists in_fsetD negb_and negbK mnfsetE.
by apply/orP; left.
Qed.

Variable n : nat.

Definition ngraph (x : 'rV[F]_n) := [tuple x ord0 i | i < n].

Definition interp := fun (f : {formula_n F}) =>
    [pred v : 'rV[F]_n | rcf_sat (ngraph v) f].

Definition pred_of_SAset (s : {SAset F^n}) :
   pred ('rV[F]_n) := interp (repr s).
Canonical Structure SAsetPredType := Eval hnf in mkPredType pred_of_SAset.

End Interpretation.
End SemiAlgebraicSet.

Section SemiAlgebraicSet2.

Variable F : rcfType.

Lemma cat_ffun_id (n m : nat) (f : 'rV[F]_(n + m)) :
  row_mx (\row_(i < n) (f ord0 (lshift _ i)))
         (\row_(j < m) (f ord0 (rshift _ j))) = f.
Proof.
apply/rowP => i; rewrite mxE.
by case: splitP=> [] j /esym eq_i; rewrite mxE; congr (f _); apply/val_inj/eq_i.
Qed.

Section Interpretation2.

Variable n : nat.

(* recover {formulan} structure on formula *)

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

Lemma forall_formulan i (f : {formula_n F}) : nvar n ('forall 'X_i, f)%oT.
Proof.
by rewrite /nvar (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Canonical Structure formulan_forall (i : nat) (f : {formula_n F})
  := MkFormulan (forall_formulan i f).

Lemma term_fv_tsubst (i : nat) (x : F) (t : GRing.term F) :
  term_fv (GRing.tsubst t (i, (x%:T)%oT)) = (term_fv t) `\ i.
Proof.
elim: t => //=; rewrite ?fset0D //;
  do ?by move=> t1 h1 t2 h2; rewrite fsetDUl ![in LHS](h1, h2).
move=> j; have [->| /negbTE neq_ij] := eqVneq j i.
  by rewrite eqxx //= fsetDv.
by rewrite neq_ij /= mem_fsetD1 // inE eq_sym neq_ij.
Qed.

Lemma formula_fv_fsubst (i : nat) (x : F) (f : formula F) :
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
    by rewrite eqxx // fsetDDl //= fsetUid.
  by rewrite neq_ij !fsetDDl fsetUC.
+ move=> j f h /=.
  rewrite fun_if h.
  have [->| /negbTE neq_ij] := eqVneq j i.
    by rewrite eqxx // fsetDDl //= fsetUid.
  by rewrite neq_ij !fsetDDl fsetUC.
Qed.

Lemma fsubst_formulan (i : nat) (x : F) (f : {formula_n F}) :
  nvar n (fsubst f (i, (x%:T)%oT))%oT.
Proof.
rewrite /nvar formula_fv_fsubst.
by rewrite (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Canonical Structure formulan_fsubst (i : nat) (x : F) (f : {formula_n F}) :=
  MkFormulan (fsubst_formulan  i x f).

End Interpretation2.

Lemma holds_take (n : nat) (f : {formula_n F}) (e : seq F) :
  holds (take n e) f <-> holds e f.
Proof.
move: n f; elim/last_ind : e => // e x iHe n' f.
rewrite -{2}(@rcons_set_nth _ _ 0) take_rcons.
have [lt_en'|leq_n'e] := ltnP (size e) n'.
  by rewrite take_oversize ?rcons_set_nth // ltnW.
apply: (iff_trans _ (@holds_fsubst _ _ _ _ _)).
apply: (iff_trans _ (@iHe _ _ )) => /=.
by rewrite fsubst_id // (contra (@in_fv_formulan _ _ _ _)) // -leqNgt .
Qed.

Variable n : nat.

Definition same_row_env (e1 e2 : seq F) :=
  \row_(i < n) e1`_(val i) =2 (\row_(i < n) e2`_(val i) : 'rV[F]_n).

Lemma eqn_holds e1 e2 (f : {formula_n F}) :
  same_row_env e1 e2 -> holds e1 f -> holds e2 f.
Proof.
rewrite /same_row_env => h; move/holds_take => h'.
apply/holds_take; apply: (eq_holds _ h') => i.
have [lt_in | leq_ni] := ltnP i n; last first.
  by rewrite ? nth_default ?size_take // ?(leq_trans (geq_minl _ _)).
rewrite !nth_take //.
by move/(_ ord0 (Ordinal lt_in)) : h; rewrite !mxE.
Qed.

Fact closed_nforall_formulan (f : {formula_n F}) :
  formula_fv (nquantify O n Forall f) == fset0.
Proof. by rewrite formula_fv_nforall fsetD_eq0 fsubset_formulan_fv. Qed.

Fact closed_nexists_formulan (f : {formula_n F}) :
  formula_fv (nquantify O n Exists f) == fset0.
Proof. by rewrite formula_fv_nexists fsetD_eq0 fsubset_formulan_fv. Qed.

Lemma set_nthP (x : n.-tuple F) (i : 'I_n) (y : F) :
  size (set_nth 0 x i y) == n.
Proof. by rewrite size_set_nth size_tuple; apply/eqP/maxn_idPr. Qed.

Canonical set_nth_tuple (x : n.-tuple F) (i : 'I_n) (y : F) :=
  Tuple (set_nthP x i y).

Definition ngraph_tnth k (t : k.-tuple F) :
  ngraph (\row_(i < k) (nth 0 t i)) = t.
Proof.
apply/val_inj; rewrite /= -map_tnth_enum; apply/eq_map => i.
rewrite mxE (tnth_nth 0) /=.
move: t i; case: k => [| k t i]; first by move=> [t h [i hi]].
rewrite (@nth_map 'I_k.+1 ord0 F 0
  (fun (j : 'I_k.+1) => (tnth t j)) i (enum 'I_k.+1)); last first.
  by rewrite size_enum_ord.
by rewrite (tnth_nth 0) (@nth_enum_ord k.+1 ord0 i).
Qed.

Fact rcf_sat_tuple (t : n.-tuple F) (f : {formula_n F}) :
  rcf_sat t f = ((\row_(i < n) (nth 0 t i)) \in
  [pred y : 'rV[F]_n | rcf_sat (ngraph (\row_(i < n) (nth 0 t i))) f]).
Proof. by rewrite inE ngraph_tnth. Qed.

Fact holds_tuple (t : n.-tuple F) (s : {SAset F^n}) :
  reflect (holds t s) ((\row_(i < n) (nth 0 t i)) \in s).
Proof.
apply: (iffP idP) => [h | ].
  by apply/rcf_satP; rewrite rcf_sat_tuple.
by move/rcf_satP; rewrite rcf_sat_tuple.
Qed.

Lemma holds_equivf (t : n.-tuple F) (f g : {formula_n F}) :
  sub_equivf f g -> holds t f -> holds t g.
Proof. by move/rcf_satP/nforallP; move/(_ t) => [h _]. Qed.

Lemma rcf_sat_equivf (t : n.-tuple F) (f g : {formula_n F}) :
  sub_equivf f g -> rcf_sat t f = rcf_sat t g.
Proof.
move=> h; apply/rcf_satP/rcf_satP; apply: holds_equivf => //.
by rewrite /sub_equivf /= equivf_sym.
Qed.

Fact rcf_sat_repr_pi (t : n.-tuple F) (f : {formula_n F}) :
  rcf_sat t (repr (\pi_{SAset F^n} f)) = rcf_sat t f.
Proof. by case: piP => ? /eqmodP /rcf_sat_equivf ->. Qed.

Fact holds_repr_pi (t : n.-tuple F) (f : {formula_n F}) :
  holds t (repr (\pi_{SAset F^n} f)) <-> holds t f.
Proof. by split; apply: holds_equivf; rewrite /sub_equivf -eqmodE reprK. Qed.

Lemma equivf_exists (f g : {formula_n F}) (i : nat) :
  equivf n f g -> (equivf n ('exists 'X_i, f) ('exists 'X_i, g))%oT.
Proof.
rewrite /equivf; move/rcf_satP/nforallP => h.
apply/rcf_satP/nforallP => u /=.
have [lt_in|leq_ni] := ltnP i n; last first.
+ split=> [[x]|].
  - move/holds_fsubst.
    rewrite fsubst_id; last
      by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
    move=> holds_uf; exists x; apply/holds_fsubst.
    rewrite fsubst_id; last
      by rewrite (contra (@in_fv_formulan _ _ _ _)) // -leqNgt.
    by move: holds_uf; move/(_ u) : h; rewrite cat0s /=; move => [].
  - move=> [x]; rewrite set_nth_over ?size_tuple // rcons_cat /=.
    move/holds_take; rewrite take_size_cat ?size_tuple // => holds_ug.
    exists 0; rewrite set_nth_nrcons ?size_tuple // rcons_nrcons -nseq_cat.
    by apply/holds_cat_nseq; move: holds_ug; move/(_ u) : h => [].
+ split.
  - move=> [x hxf]; exists x; move: hxf.
    move/(_ [tuple of (set_nth 0 u (Ordinal lt_in) x)]) : h.
    by rewrite cat0s /=; move=> [].
  - move=> [x hxf]; exists x; move: hxf.
    move/(_ [tuple of (set_nth 0 u (Ordinal lt_in) x)]) : h.
    by rewrite cat0s /=; move=> [].
Qed.

Lemma SAsetP (s1 s2 : {SAset F^n}) : reflect (s1 =i s2) (s1 == s2).
Proof.
move: s1 s2; apply: quotW => f1; apply: quotW => f2.
apply: (iffP idP) => [/eqP <-|] //.
rewrite eqmodE /equivf => h; apply/rcf_satP/nforallP => u.
split; move/holds_repr_pi/holds_tuple; [rewrite h | rewrite -h];
by move/holds_tuple/holds_repr_pi.
Qed.

End SemiAlgebraicSet2.

Section Projection.

Variables (F : rcfType) (n : nat) (i : 'I_n).

Fact ex_proj_proof (f : {formula_n F}) : nvar n ('exists 'X_i, f)%oT.
Proof.
by rewrite /nvar (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Definition ex_proj (f : {formula_n F}) := MkFormulan (ex_proj_proof f).

Definition SA_ex_proj := (lift_op1 {SAset F^n} ex_proj).

Lemma ex_proj_idem (s : {SAset F^n}) :
  SA_ex_proj (SA_ex_proj s) = SA_ex_proj s.
Proof.
move: s; apply: quotP => f eq_repr_pi_f.
rewrite /SA_ex_proj; unlock.
apply/eqP; rewrite eqmodE eq_repr_pi_f.
apply/rcf_satP/nforallP => u.
rewrite cat0s; split.
+ move=> [y hxy]; move/holds_repr_pi : hxy => [x hxy].
  by exists x; move: hxy; rewrite set_set_nth eqxx.
+ move=> [y hxy]; exists y; apply/holds_repr_pi.
  by exists y; rewrite set_set_nth eqxx.
Qed.

Fact all_proj_proof (f : {formula_n F}) : nvar n ('forall 'X_i, f)%oT.
Proof.
by rewrite /nvar (fsubset_trans (@fsubD1set _ _ _)) // fsubset_formulan_fv.
Qed.

Definition all_proj (f : {formula_n F}) := MkFormulan (all_proj_proof f).

Definition SA_all_proj := (lift_op1 {SAset F^n} all_proj).

Lemma all_proj_idem (s : {SAset F^n}) :
  SA_all_proj (SA_all_proj s) = (SA_all_proj s).
Proof.
move : s; apply : quotP => f hf.
rewrite /SA_all_proj; unlock.
apply/eqP; rewrite eqmodE hf.
apply/rcf_satP/nforallP => u; rewrite cat0s.
split=> h x.
+ by move/(_ x)/holds_repr_pi/(_ x) : h; rewrite set_set_nth eqxx.
+ apply/holds_repr_pi => y; rewrite set_set_nth eqxx.
  by move/(_ y) : h.
Qed.

Fact test_can_and (f g : {formula_n F}) :
  formula_fv (nquantify O n Forall (f /\ g)%oT) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

Fact test_can_imply (f g : {formula_n F}) :
  formula_fv (nquantify O n Forall (f ==> g)%oT) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

Fact test_can_imply_and (f g h : {formula_n F}) :
  formula_fv (nquantify O n Forall (f ==> (g /\ h))%oT) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

End Projection.

Section Cylinder.

Lemma nth_enum_ord2 (n m : nat) (i0 : 'I_n.+1) (j : 'I_m) (p : (m <= n.+1)%N) :
  nth i0 (enum 'I_n.+1) j = widen_ord p j.
Proof.
elim: j => l pr; apply/val_inj => /=.
by rewrite nth_enum_ord // (leq_trans pr).
Qed.

Variables (F : rcfType) (n : nat).

Fact lift_proof (f : {formula_n F}) : nvar n.+1 f.
Proof.
rewrite /nvar (fsubset_trans (fsubset_formulan_fv _)) //.
case: n => [|m]; first by rewrite seq_fset_nil fsub0set.
by rewrite mnfset_sub //= !add0n.
Qed.

Definition lift_form (f : {formula_n F}) := MkFormulan (lift_proof f).

Definition sa_lift_form (s : {SAset F^n}) : {SAset F^n.+1} := 
  \pi_{SAset F^n.+1} (lift_form (repr s)).

Definition sa_lift_point (x : 'rV[F]_n) : 'rV[F]_n.+1 :=
  \row_(i < n.+1) (match (unlift ord0 i) with
                     | None => 0
                     | Some j => (x ord0 j)
                   end).

(* Lemma holds_sa_lift_form (f : {formula_n F}) (e : seq F) : *)
(*     holds e (lift_form f) <-> holds e f. *)
(* Proof. *)
(* rewrite //=. *)

(*     holds (take n e) f <-> holds e f. *)

End Cylinder.

Section Cylinder2.

Variable (F : rcfType).

Lemma in_saset0 (s : {SAset F ^ 0}) (x : 'rV[F]_0) : x \in s = rcf_sat [::] s.
Proof.
rewrite inE; congr rcf_sat; apply: size0nil.
by rewrite size_map size_enum_ord.
Qed.

(* todo: factorize both goals *)
Lemma rcf_sat_saset0 (s : {SAset F ^ 0}) e : rcf_sat e s = rcf_sat [::] s.
Proof.
apply/rcf_satP/rcf_satP; move/holds_take; first by rewrite take0.
by move=> h; apply/holds_take; rewrite take0.
Qed.

Lemma sa_lift_pointP (n : nat) (s : {SAset F^n}) (x : 'rV[F]_n.+1) :
  (x \in (sa_lift_form s)) = (\row_(i < n) (x ord0 (lift ord_max i)) \in s).
Proof.
move: s x; case: n => [s x | n s x].
by rewrite in_saset0 inE rcf_sat_repr_pi rcf_sat_saset0.
have h : [seq (\row_i0 x ord0 (lift ord_max i0)) ord0 i | i <- enum 'I_n.+1] 
  = take n.+1 [seq x ord0 i | i <- enum 'I_n.+2].
+ apply: (@eq_from_nth _ 0) => [|i].
    by rewrite size_take size_map size_enum_ord size_map size_enum_ord ltnSn.
  rewrite size_map size_enum_ord ltnS /= => hi.
  rewrite nth_take // (nth_map ord0) ; last by rewrite size_enum_ord.
  rewrite (nth_map ord0); last by rewrite size_enum_ord ltnW.
  rewrite mxE; congr fun_of_matrix; apply/val_inj => /=.
  rewrite !(nth_enum_ord ord0) // ; last by rewrite ltnW.
  by rewrite /bump ltnNge hi.
+ rewrite /= /sa_lift_point /sa_lift_form /lift_form.
  rewrite !inE rcf_sat_repr_pi /= h.
  apply/rcf_satP/rcf_satP => /= ; first by move/holds_take.
  by move=> * ; apply/holds_take.
Qed.

End Cylinder2.

Section Next.

Variables (F : rcfType) (n : nat).

Lemma formulaSn_proof (f : {formula_n F}) : nvar n f.
Proof. by rewrite /nvar fsubset_formulan_fv. Qed.

Definition lift_formulan (f : {formula_n F}) := MkFormulan (formulaSn_proof f).

Lemma lift_formulan_inj : injective lift_formulan.
Proof. by move=> f1 f2 /(congr1 val) h; apply: val_inj. Qed.

Lemma SAset0_proof : @nvar F n (Bool false).
Proof. by rewrite /nvar fsub0set. Qed.

Definition SAset0 := \pi_{SAset F^n} (MkFormulan SAset0_proof).

Lemma pi_form (f : {formula_n F}) (x : 'rV[F]_n) :
    (x \in \pi_{SAset F^n} f) = rcf_sat (ngraph x) f.
Proof. by rewrite inE; apply/rcf_satP/rcf_satP => ?; apply/holds_repr_pi. Qed.

Lemma inSAset0 (x : 'rV[F]_n) : (x \in SAset0) = false.
Proof. by rewrite pi_form. Qed.

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

Fact nvar_True : @nvar F n True.
Proof. by rewrite /nvar fsub0set. Qed.

Lemma nvar_And (k : nat) (E : 'I_k -> formula F) :
   nvar n (\big[And/True%oT]_(i < k) (E i)) =
   (\big[andb/true%oT]_(i < k) (nvar n (E i))).
Proof.
rewrite /nvar formula_fv_bigAnd big_andE; apply/bigfcupsP/forallP => //= h i.
by rewrite h.
Qed.

Definition SAset1_formula (x : 'rV[F]_n) :=
    \big[And/True%oT]_(i < n) ('X_i == (x ord0 i)%:T)%oT.

Lemma nth_ngraph k x0 (t : 'rV[F]_k) (i : 'I_k) :
  nth x0 (ngraph t) i = t ord0 i.
Proof. by rewrite -tnth_nth tnth_map tnth_ord_tuple. Qed.

Lemma SAset1_formulaP (x y : 'rV[F]_n) :
    rcf_sat (ngraph x) (SAset1_formula y) = (x == y).
Proof.
rewrite rcf_sat_forallP; apply/forallP/eqP; last first.
  by move=> -> i; rewrite simp_rcf_sat /= nth_ngraph.
move=> h; apply/rowP => i; move/(_ i) : h.
by rewrite simp_rcf_sat /= nth_ngraph => /eqP.
Qed.

Lemma SAset1_proof (x : 'rV[F]_n) : @nvar F n (SAset1_formula x).
Proof.
rewrite /SAset1_formula; elim/big_ind: _; rewrite /nvar.
- exact: fsub0set.
- by move=> ???? /=; apply/fsubUsetP.
- by move=> i /= _; rewrite fsetU0 fsub1set mnfsetE /=.
Qed.

Definition SAset1 (x : 'rV[F]_n) : {SAset F^n} :=
    \pi_{SAset F^n} (MkFormulan (SAset1_proof x)).

Lemma inSAset1 (x y : 'rV[F]_n) : (x \in SAset1 y) = (x == y).
Proof. by rewrite pi_form SAset1_formulaP. Qed.

End Next.

Section POrder.

Variable F : rcfType.

Variable n : nat.

Definition SAsub (s1 s2 : {SAset F^n}) :=
    rcf_sat [::] (nquantify O n Forall (s1 ==> s2)).

Lemma reflexive_SAsub : reflexive SAsub.
Proof. by move=> s; apply/rcf_satP/nforallP => u; rewrite cat0s. Qed.

Lemma antisymetry_SAsub : antisymmetric SAsub.
Proof.
apply: quotP => f1 _; apply: quotP => f2 _.
move => /andP [/rcf_satP/nforallP sub1 /rcf_satP/nforallP sub2].
apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
split; move/holds_repr_pi=> hf.
+ move/(_ u) : sub1; rewrite cat0s => sub1.
  by apply/holds_repr_pi; apply: sub1.
+ by move/(_ u) : sub2 => sub2; apply/holds_repr_pi; apply: sub2.
Qed.

Lemma transitive_SAsub : transitive SAsub.
Proof.
apply: quotP => f1 _; apply: quotP => f2 _; apply: quotP => f3 _.
move/rcf_satP/nforallP => sub21; move/rcf_satP/nforallP => sub13.
apply/rcf_satP/nforallP => u.
move/holds_repr_pi => holds_uf2.
by apply: sub13; apply: sub21; apply/holds_repr_pi.
Qed.

Definition SAset_porderMixin :=
  Order.LePOrderMixin reflexive_SAsub antisymetry_SAsub transitive_SAsub.

Canonical SAtype_porderType :=
  POrderType (SET.display_set tt) (SAtype F n) SAset_porderMixin.
Canonical SAset_porderType := [porderType of {SAset F^n}].

Import SET.SetSyntax.

Fact nvar_False : @formula_fv F False `<=` mnfset 0 n.
Proof. by rewrite fsub0set. Qed.

Definition SAset_bottom := \pi_{SAset F^n} (MkFormulan nvar_False).

Lemma SAset_bottomP (s : (SAtype F n)) : (SAset_bottom <= s)%O.
Proof. by apply/rcf_satP/nforallP => u; move/holds_repr_pi. Qed.

Definition SAset_blatticeMixin := Order.BLattice.Mixin SAset_bottomP.

Definition SAset_meet (s1 s2 : {SAset F^n}) : {SAset F^n} :=
  \pi_{SAset F^n} (formulan_and s1 s2).

Definition SAset_join (s1 s2 : {SAset F^n}) : {SAset F^n} :=
  \pi_{SAset F^n} (formulan_or s1 s2).

Fact commutative_meet : commutative SAset_meet.
Proof.
move=> s1 s2; apply/eqP; rewrite eqmodE.
by apply/rcf_satP/nforallP => u; split => [[h1 h2] | [h2 h1]]; split.
Qed.

Fact commutative_join : commutative SAset_join.
Proof.
move=> s1 s2; apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
by split => h; apply/or_comm.
Qed.

Fact associative_meet : associative SAset_meet.
Proof.
move => s1 s2 s3; apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => u.
split=> [[h1 /holds_repr_pi [h2 h3]]|[/holds_repr_pi [h1 h2] h3]];
by split=> //; apply/holds_repr_pi => []; split.
Qed.

Fact associative_join : associative SAset_join.
Proof.
move=> s1 s2 s3; apply/eqP; rewrite eqmodE.
apply/rcf_satP/nforallP => u.
split => [ [ | /holds_repr_pi [|]] | [/holds_repr_pi [|] | ] ].
+ by left; apply/holds_repr_pi; left.
+ by left; apply/holds_repr_pi; right.
+ by right.
+ by left.
+ by right; apply/holds_repr_pi; left.
+ by right; apply/holds_repr_pi; right.
Qed.

Fact meet_join (s1 s2 : {SAset F^n}) : SAset_meet s2 (SAset_join s2 s1) = s2.
Proof.
apply/eqP/SAsetP => x; rewrite !inE.
rewrite !rcf_sat_repr_pi simp_rcf_sat rcf_sat_repr_pi.
by rewrite simp_rcf_sat andbC orbK.
Qed.

Fact join_meet (s1 s2 : {SAset F^n}) : SAset_join s2 (SAset_meet s2 s1) = s2.
Proof.
apply/eqP/SAsetP => x; rewrite !inE !rcf_sat_repr_pi.
by rewrite simp_rcf_sat rcf_sat_repr_pi simp_rcf_sat andbC andKb.
Qed.

Fact le_meet (s1 s2 : {SAset F^n}) : (s1 <= s2)%O = (SAset_meet s1 s2 == s1).
Proof.
apply/idP/idP=> [sub12| /SAsetP h].
+ apply/SAsetP => x; move : (ngraph x) => e.
  rewrite !inE rcf_sat_repr_pi simp_rcf_sat.
  apply : andb_idr; apply/implyP.
  move : sub12 => /rcf_satP/nforallP sub12.
  apply/implyP; move/rcf_satP => holds_e_s1.
  apply/rcf_satP; move : holds_e_s1.
  exact: sub12.
+ apply/rcf_satP/nforallP => e.
  by move/holds_tuple; rewrite -h; move/holds_tuple/holds_repr_pi => [].
Qed.

Fact left_distributive_meet_join : left_distributive SAset_meet SAset_join.
Proof.
set vw := holds_repr_pi; move=> s1 s2 s3; apply/eqP; rewrite eqmodE.
apply/rcf_satP/nforallP => t.
split=> [[/vw /= [h1|h2] h3]|[/vw [h1 h3]| /vw [h2 h3]]].
+ by left; apply/vw.
+ by right; apply/vw.
+ by split => //; apply/vw; left.
+ by split => //; apply/vw; right.
Qed.

Definition SAset_latticeMixin :=
  Order.Lattice.Mixin commutative_meet commutative_join associative_meet
        associative_join meet_join join_meet le_meet
        left_distributive_meet_join.

Canonical SAtype_latticeType := LatticeType (SAtype F n) SAset_latticeMixin.
Canonical SAtype_blatticeType := BLatticeType (SAtype F n) SAset_blatticeMixin.

Canonical SAset_latticeType := [latticeType of {SAset F^n}].
Canonical SAset_blatticeType := [blatticeType of {SAset F^n}].

Definition SAset_top : {SAset F^n} :=
  \pi_{SAset F^n} (MkFormulan (nvar_True _ _)).

Lemma SAset_topP (s : {SAset F^n}) : (s <= SAset_top)%O.
Proof. by apply/rcf_satP/nforallP => t h; apply/holds_repr_pi. Qed.

Definition SAset_tblatticeMixin := Order.TBLattice.Mixin SAset_topP.

Canonical SAset_tblatticeType :=
  TBLatticeType {SAset F^n} SAset_tblatticeMixin.

Definition SAset_sub (s1 s2 : {SAset F^n}) : {SAset F^n} :=
  \pi_{SAset F^n} (formulan_and s1 (formulan_not s2)).

Fact meet_sub (s1 s2 : {SAset F^n}) :
    SAset_meet s2 (SAset_sub s1 s2) = SAset_bottom.
Proof.
apply/eqP; rewrite eqmodE; apply/rcf_satP/nforallP => t.
by split => //; move => [? /holds_repr_pi [_ ?]].
Qed.

Fact join_meet_sub (s1 s2 : {SAset F^n}) :
  SAset_join (SAset_meet s1 s2) (SAset_sub s1 s2) = s1.
Proof.
apply/eqP/SAsetP => x; rewrite !inE.
rewrite !rcf_sat_repr_pi !simp_rcf_sat !rcf_sat_repr_pi.
by rewrite !simp_rcf_sat -andb_orr orbN andbT.
Qed.

Definition SAset_cblatticeMixin :=
  Order.CBLattice.Mixin meet_sub join_meet_sub.

Canonical SAtype_cblatticeType :=
  CBLatticeType (SAtype F n) SAset_cblatticeMixin.
Canonical SAset_cblatticeType :=
  CBLatticeType {SAset F^n} SAset_cblatticeMixin.

(* todo debug set.v [cblatticeType of _] should not rely on ctblattices *)

End POrder.

Section SAFunction.

Variable F : rcfType.

Lemma existsn_formulaSn (m : nat) (f : {formula_(m.+1) F}) :
  nvar m ('exists 'X_m, f)%oT.
Proof.
rewrite /nvar fsubDset (fsubset_trans (fsubset_formulan_fv _)) // => {f}.
rewrite -add1n addnC iota_add add0n seq_fset_cat fsetUC.
by rewrite fset_cons seq_fset_nil fsetU0 fsubset_refl.
Qed.

Lemma existsPn_formulan (m : nat) (f : {formula_m F}) :
  nvar m.-1 ('exists 'X_m.-1, f)%oT.
Proof.
move: f; case: m => [f|n f] //=; last exact: existsn_formulaSn.
by rewrite /nvar fsubDset (fsubset_trans (fsubset_formulan_fv _)) // fsubsetUr.
Qed.

Lemma nexists_formulan m n (f : {formula_m F}) :
  nvar n (nquantify n (m - n) Exists f).
Proof.
rewrite /nvar formula_fv_nexists fsubDset fsetUC -seq_fset_cat -iota_add.
have [/ltnW lt_mn| leq_nm] := ltnP m n; last first.
  by rewrite subnKC // fsubset_formulan_fv.
rewrite (fsubset_trans (fsubset_formulan_fv _)) //.
apply/fsubsetP=> x; rewrite !seq_fsetE !mem_iota !add0n => /andP [_ lt_xm].
by rewrite leq0n (leq_trans lt_xm) // (leq_trans lt_mn) // leq_addr.
Qed.

Canonical Structure formulan_nexists m n (f : {formula_m F}) :=
  MkFormulan (nexists_formulan n f).

Lemma ngraph_nil (t : 'rV[F]_0) : ngraph t = [tuple of nil].
Proof. by apply/eq_from_tnth => - []. Qed.

Fact size_ngraph (m : nat) (t : 'rV[F]_m) : size (ngraph t) = m.
Proof. by rewrite size_tuple. Qed.

Fact cat_ffunE (x0 : F) m (t : 'rV[F]_m) p (u : 'rV[F]_p) (i : 'I_(m + p)) :
(row_mx t u) ord0 i = if (i < m)%N then (ngraph t)`_i else (ngraph u)`_(i - m).
Proof.
by rewrite mxE; case: splitP => j ->; rewrite ?(addnC, addnK) nth_ngraph.
Qed.

Fact ngraph_cat (m : nat) (t : 'rV[F]_m) (p : nat) (u : 'rV[F]_p) :
  ngraph (row_mx t u) = ngraph t ++ ngraph u :> seq F.
Proof.
apply: (@eq_from_nth _ 0) => [|i]; first by rewrite size_cat ?size_ngraph.
rewrite size_ngraph=> lt_i_mp; rewrite nth_cat.
have -> : i = nat_of_ord (Ordinal lt_i_mp) by [].
by rewrite nth_ngraph (cat_ffunE 0) size_ngraph.
Qed.

Variables (n m : nat).

Definition ftotal (f : {formula_(n + m) F}) :=
  nquantify O n Forall (nquantify n m Exists f).

Lemma formuladd (p : nat) (f : {formula_p F}) : nvar (p + m) f.
Proof.
rewrite /nvar (fsubset_trans (fsubset_formulan_fv _)) //.
apply/fsubsetP=> x; rewrite !seq_fsetE !mem_iota !add0n !leq0n.
exact: ltn_addr.
Qed.

Canonical Structure formulan_add (m : nat) (f : {formula_m F}) :=
  MkFormulan (formuladd f).

Definition ex_y (f : {formula_(n + m) F}) (x : 'rV[F]_n) :=
  rcf_sat (ngraph x) (nquantify n m Exists f).

Definition SAtot : pred_class :=
   [pred s : {SAset F ^ _} | rcf_sat [::] (ftotal s)].

Fact test_can1 (f g h : {formula_(n + m) F}) :
  formula_fv (nquantify O (n + m) Forall (f /\ (g ==> h))%oT) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

Fact test_can2 (f g h : {formula_(n + m) F}) :
  formula_fv (nquantify O (n + m + m) Forall f) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

Fact extP (p : nat) (f : {formula_p F}) : nvar (p + m) f.
Proof.
rewrite /nvar (fsubset_trans (@nvar_formulan _ _ _)) //.
by rewrite mnfset_triangle fsubsetUl.
Qed.

Definition ext (p : nat) (f : {formula_p F}) := MkFormulan (extP f).

Fact test_can3 (f g h : {formula_(n + m) F}) :
  formula_fv (nquantify O (n + m + m) Forall ((ext f) /\ (ext f))) == fset0.
Proof. exact: closed_nforall_formulan. Qed.

Lemma f_is_ftotalE (f : {formula_(n + m) F}) :
  reflect
  (forall (t : n.-tuple F), exists (u : m.-tuple F), rcf_sat (t ++ u) f)
  (rcf_sat [::] (ftotal f)).
Proof.
apply: (iffP idP) => [h x | h].
+ move/rcf_satP/nforallP/(_ x) : h.
  case: x => s /= /eqP -{1}<-.
  by move/nexistsP => [t h]; exists t; apply/rcf_satP.
+ apply/rcf_satP/nforallP => x /=.
  move/(_ x) : h => [t].
  case: x => s /= /eqP -{2}<-.
  by move/rcf_satP => h; apply/nexistsP; exists t.
Qed.

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

(* quantifier elim + evaluation of invariant variables to 0 *)
Definition qf_elim (f : formula F) : formula F :=
  let g := (quantifier_elim (@wproj _) (to_rform f)) in
  foldr (fun i h => fsubst h (i, GRing.Const 0)) g
        (enum_fset (formula_fv g `\` formula_fv f)).

Lemma fv_foldr_fsubst (f : formula F) (s : seq nat) :
  formula_fv (foldr (fun i h => fsubst h (i, GRing.Const 0)) f s) =
  (formula_fv f) `\` (seq_fset s).
Proof.
elim: s => [|i s ih]; first by rewrite seq_fset_nil fsetD0 // fsubset_refl.
by rewrite formula_fv_fsubst ih fset_cons fsetDDl fsetUC.
Qed.

Fact qf_form_fsubst (f : formula F) (i : nat) (t : GRing.term F) :
  qf_form (fsubst f (i, t)) = (qf_form f).
Proof. by elim: f=> //=; move=> f1 -> f2 ->. Qed.

Fact qf_form_fsubstn (f : formula F) (s : seq nat) (t : GRing.term F) :
  qf_form (foldr (fun i h => fsubst h (i, t)) f s) = (qf_form f).
Proof. by elim: s => // x s ih; rewrite qf_form_fsubst ih. Qed.

Lemma qf_elim_qf (f : formula F) : qf_form (qf_elim f).
Proof. by rewrite qf_form_fsubstn qf_form_elim // to_rform_rformula. Qed.

(* Lemma enum_fsetE (K : choiceType) (s : {fset K}) : enum_fset s =i s. *)
(* Proof. by []. Qed. *)

Lemma qf_elim_fv (f : formula F) : formula_fv (qf_elim f) `<=` formula_fv f.
Proof.
rewrite fv_foldr_fsubst fsubDset; apply/fsubsetP => i.
by rewrite inE seq_fsetE !mem_enum_fset inE /=; move ->; rewrite orNb.
Qed.

Fact test1 (f : formula F) (e : seq F) :
  reflect (holds e (to_rform f))
          (qf_eval e (quantifier_elim (@wproj _) (to_rform f))).
Proof.
apply: quantifier_elim_rformP; last by rewrite to_rform_rformula.
- by move=> i bc /= h; apply: wf_QE_wproj.
- by move=> i bc /= e2 h; apply: valid_QE_wproj.
Qed.

Fact test2 (i : nat) (e : seq F) (f : formula F) :
  i \notin formula_fv f ->
  (holds e (fsubst f (i, GRing.Const 0)) <-> holds e f).
Proof. by move=> h; rewrite fsubst_id. Qed.

Fact test3 (f : formula F) (s : seq nat) (e : seq F) :
  [disjoint (seq_fset s) & (formula_fv f)] ->
    (holds e (foldr (fun i h => fsubst h (i, GRing.Const 0)) f s)
     <-> holds e f).
Proof.
elim: s => // i s ih.
rewrite fset_cons fdisjointU1X => /andP [hi dis] /=.
rewrite fsubst_id; first exact : ih.
move: hi; apply: contra.
by rewrite fv_foldr_fsubst inE; move/andP => [].
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

Lemma fv_foldr (f : formula F) (s : seq (formula F)) :
  formula_fv (foldr Or f s) =
  (formula_fv f) `|` \bigcup_(i <- s) (formula_fv i).
Proof.
elim: s => [|g s /= ->]; first by rewrite big_nil fsetU0.
by rewrite big_cons fsetUCA.
Qed.

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

Lemma qf_elim_holdsP (f : formula F) (e : seq F) :
  reflect (holds e f) (rcf_sat e (qf_elim f)).
Proof.
apply: (equivP _ (to_rformP _ _)); apply: (equivP (rcf_satP _ _)).
apply: (iff_trans (foldr_fsubst_indep _ _ _)) => [i | ]; last first.
  apply: (iff_trans (rwP (qf_evalP _ (qf_form_elim (to_rform_rformula _))))).
  apply: iff_sym.
  by apply: (iff_trans _ (rwP (elim_rformP _ (to_rform_rformula _)))).
rewrite inE => /andP [_ not_fv] e2.
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

Definition eq_vec (v1 v2 : seq nat) : formula F :=
  if size v1 == size v2 then
  (\big[And/True]_(i < size v1) ('X_(nth 0%N v1 i) == 'X_(nth 0%N v2 i)))%oT
  else False%oT.

Definition functional (f : {formula_(n+m) F}) :=
  (nquantify O (n + m + m) Forall (
  ((subst_formula (iota 0 n ++ iota n m) f)
  /\ (subst_formula (iota 0 n ++ iota (n + m) m) f))
  ==> (eq_vec (iota n m) (iota (n + m) m)))).

Definition SAfunc : pred_class :=
  [pred s : {SAset F ^ _} | rcf_sat [::] (functional s)].

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
rewrite (rwP (@qf_elim_holdsP f _)) -(rwP (@rcf_satP _ _ _)) /subst_formula.
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

Lemma fv0_holds (e : seq F) f :
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

Fact fv_tsubst_nil (t : GRing.term F) : term_fv (subst_term [::] t) = fset0.
Proof. by elim: t => //= t1 -> t2 ->; rewrite fsetU0. Qed.

Fact fv_tsubst (s : seq nat) (t : GRing.term F) :
    term_fv (subst_term s t) `<=` seq_fset s.
Proof.
elim: t => //.
- move=> i /=.
  have [lt_is|leq_si] := ltnP i (size s); rewrite ?fsub0set //.
  by rewrite fsub1set seq_fsetE; apply/(nthP _); exists i.
- by move=> x; rewrite fsub0set.
- by move=> i; rewrite fsub0set.
- by move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
- by move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
Qed.

Lemma fsubset_seq_fset (K : choiceType) (s1 s2 : seq K) :
    reflect {subset s1 <= s2} ((seq_fset s1) `<=` (seq_fset s2)).
Proof.
apply: (@equivP _ _ _ (@fsubsetP _ _ _)).
by split => h x; move/(_ x) : h; rewrite !seq_fsetE.
Qed.

Fact fv_tsubst_map (s : seq nat) (t : GRing.term F) :
  term_fv (subst_term s t) `<=`
  seq_fset [seq nth O s i | i <- (iota O (size s)) & (i \in term_fv t)].
Proof.
elim: t => //.
- move=> i /=.
  have [lt_is|leq_si] := ltnP i (size s); rewrite ?fsub0set //.
  rewrite fsub1set seq_fsetE; apply: map_f.
  by rewrite mem_filter in_fset1 eqxx mem_iota leq0n add0n.
- by move=> x; rewrite fsub0set.
- by move=> i; rewrite fsub0set.
- move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
  + rewrite (fsubset_trans h1) //.
    apply/fsubset_seq_fset; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans h2) //.
    apply/fsubset_seq_fset; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 h1 t2 h2 /=; rewrite fsubUset; apply/andP; split.
  + rewrite (fsubset_trans h1) //.
    apply/fsubset_seq_fset; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans h2) //.
    apply/fsubset_seq_fset; apply: sub_map_filter => x.
    by rewrite in_fsetU => ->; rewrite orbT.
Qed.

Fact fv_subst_formula (s : seq nat) f :
  formula_fv (subst_formula s f) `<=` seq_fset s.
Proof.
rewrite /subst_formula.
move: s; elim: (qf_elim f) => // {f}.
- by move=> b s; rewrite fsub0set.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t1 t2 s; rewrite fsubUset !fv_tsubst.
- by move=> t s; rewrite fv_tsubst.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
- by move=> f1 h1 f2 h2 s; rewrite fsubUset h1 h2.
- by move=> i f h s /=; rewrite fsub0set.
- by move=> i f h s /=; rewrite fsub0set.
Qed.

Fact fv_qf_subst_formula (s : seq nat) f :
  formula_fv (qf_subst_formula s f) `<=`
  seq_fset [seq nth O s i | i <- (iota O (size s)) & (i \in formula_fv f)].
Proof.
move: s; elim: f => //.
- by move=> b s; rewrite fsub0set.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> t1 t2 s; rewrite fsubUset /=.
  apply/andP; split.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (fv_tsubst_map _ _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- by move=> t s; apply: fv_tsubst_map.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- move=> f1 h1 f2 h2 s /=.
  rewrite fsubUset.
  apply/andP; split.
  + rewrite (fsubset_trans (h1 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->.
  + rewrite (fsubset_trans (h2 _)) //.
    apply/fsubset_seq_fset.
    apply: sub_map_filter.
    move=> i.
    by rewrite in_fsetU => ->; rewrite orbT.
- by move=> i f hf s; rewrite fsub0set.
- by move=> i f hf s; rewrite fsub0set.
Qed.

Fact fv_subst_formula_map (s : seq nat) f :
  formula_fv (subst_formula s f) `<=`
        seq_fset [seq nth O s i | i <- (iota O (size s)) & (i \in formula_fv f)].
Proof.
rewrite /subst_formula.
rewrite (fsubset_trans (fv_qf_subst_formula _ _)) //.
apply/fsubset_seq_fset.
apply: sub_map_filter.
move=> i.
by move/fsubsetP/(_ i): (qf_elim_fv f).
Qed.

Fact fv_subst_nil f : formula_fv (subst_formula [::] f) = fset0.
Proof. by apply/eqP; rewrite -fsubset0 -seq_fset_nil fv_subst_formula. Qed.

Lemma leq_foldr_maxn j a (s : seq nat) : (j \in s -> j <= foldr maxn a s)%N.
Proof.
elim: s => // b s ih.
rewrite in_cons; move/orP => [/eqP eq_jb|j_in_s] /=.
- by rewrite eq_jb leq_maxl.
- by rewrite (leq_trans _ (leq_maxr _ _)) // ih.
Qed.

Lemma foldr_maxn_undup a s : foldr maxn a (undup s) = foldr maxn a s.
Proof.
elim: s => // b s ih /=.
have [b_in_s | b_notin_s] := boolP (b \in s); rewrite /= ih //.
by symmetry; apply/maxn_idPr; rewrite leq_foldr_maxn.
Qed.

Lemma foldr_maxn_leq a s b :
  ((foldr maxn a s <= b) = ((a <= b) && all (fun x => x <= b) s))%N.
Proof.
by elim: s; rewrite /= ?andbT // => c s ih; rewrite geq_max ih andbCA.
Qed.

Lemma subseq_cons (T : eqType) (x : T) (s1 s2 : seq T) :
  x \notin s1 -> subseq s1 (x :: s2) = subseq s1 s2.
Proof.
case: s1; first by rewrite /= sub0seq.
move=> y s1.
rewrite in_cons negb_or => /andP [/negbTE neq_xy x_notin_s1].
by rewrite /= eq_sym neq_xy.
Qed.

Lemma leq_foldr_maxl a s : (a <= foldr maxn a s)%N.
Proof. by elim: s => // *; rewrite (leq_trans _ (leq_maxr _ _)). Qed.

Lemma aux_leq_max_max a (s1 s2 : seq nat) : uniq s1-> uniq s2 ->
  {subset s1 <= s2} -> (foldr maxn a s1 <= foldr maxn a s2)%N.
Proof.
elim: s1; rewrite ?leq_foldr_maxl // => x s1 ih /andP [x_notin_s1 uniq_s1].
move=> uniq_s2 /subset_cons [x_in_s2 sub_12].
by rewrite geq_max leq_foldr_maxn // ih.
Qed.

Lemma leq_max_max a (s1 s2 : seq nat) :
  {subset s1 <= s2} -> (foldr maxn a s1 <= foldr maxn a s2)%N.
Proof.
rewrite -foldr_maxn_undup -[X in (_ <= X)%N]foldr_maxn_undup => h.
rewrite aux_leq_max_max ?undup_uniq // => x.
by rewrite !mem_undup; apply: h.
Qed.

Lemma holds_eq_vec e v1 v2 :
  holds e (eq_vec v1 v2) <-> (subst_env v1 e) = (subst_env v2 e).
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

Lemma subst_envP (i : nat) (t : i.-tuple nat) (e : seq F) :
  size (subst_env t e) = i.
Proof. by rewrite size_map size_tuple. Qed.

Fact subst_env_tupleP (i : nat) (t : i.-tuple nat) (e : seq F) :
  size (subst_env t e) == i. Proof. by rewrite subst_envP. Qed.

Canonical subst_env_tuple (i : nat) (t : i.-tuple nat) (e : seq F) :=
  Tuple (subst_env_tupleP t e).

Lemma f_is_funcE (f : {formula_(n + m) F}) :
  reflect
  (forall (t : n.-tuple F) (u1 u2 : m.-tuple F),
    rcf_sat (t ++ u1) f -> rcf_sat (t ++ u2) f -> u1 = u2)
  (rcf_sat [::] (functional f)).
Proof.
rewrite /functional !nquantify_add !add0n.
apply: (iffP idP).
+ move=> func t u1 u2 tu1f tu2f.
  move: func => /rcf_satP/nforallP /= /(_ t).
  rewrite -[in X in nquantify X](size_tuple t).
  move=> /nforallP /(_ u1).
  rewrite -[in X in nquantify X](size_tuple t).
  rewrite -[in X in nquantify X](size_tuple u1).
  rewrite -size_cat.
  move=> /nforallP /(_ u2) /=.
  rewrite !holds_subst !holds_eq_vec !subst_env_cat -catA.
  rewrite subst_env_iota_catl ?size_tuple //.
  rewrite subst_env_iota ?size_tuple //.
  rewrite catA -[(t ++ u1) ++ u2]cats0 -catA.
  rewrite subst_env_iota ?size_tuple //.
  move=> /(_ _) /val_inj; apply.
  by split; apply/rcf_satP.
+ move=> h; apply/rcf_satP/nforallP => v /=.
  rewrite -[in X in nquantify X](size_tuple v).
  apply/nforallP => w /=.
  rewrite -[in X in nquantify X](size_tuple v).
  rewrite -[in X in nquantify X](size_tuple w) -size_cat.
  apply/nforallP => z.
  rewrite -catA /= !holds_subst !holds_eq_vec !subst_env_cat.
  move=> [/rcf_satP h1 /rcf_satP h2].
  move: ((h [tuple of (subst_env (iota 0 n) (v ++ w ++ z))]
            [tuple of (subst_env (iota n m) (v ++ w ++ z))]
            [tuple of (subst_env (iota (n + m) m) (v ++ w ++ z))]) h1 h2).
  by move/(congr1 val).
Qed.

Lemma SAtotE (s : {SAset F ^ (n + m)}) :
  reflect
  (forall (x : 'rV[F]_n), exists (y : 'rV[F]_m), (row_mx x y) \in s)
  (s \in SAtot).
Proof.
rewrite inE; apply: (iffP (f_is_ftotalE _)) => s_sat x.
  have [y sat_s_xy] := s_sat (ngraph x).
  exists (\row_(i < m) (nth 0 y i)).
  by rewrite inE ngraph_cat ngraph_tnth.
have [y xy_in_s] := s_sat ((\row_(i < n) (nth 0 x i))).
exists (ngraph y).
by move: xy_in_s; rewrite inE ngraph_cat ngraph_tnth.
Qed.

Lemma ngraph_bij k : bijective (@ngraph F k).
Proof.
pose g := fun (x : k.-tuple F) => (\row_(i < k) (nth 0 x i)).
have h : cancel (@ngraph F k) g.
  by move=> x; apply/rowP => i; rewrite mxE nth_ngraph.
have h' : cancel g (@ngraph F k).
  by move=> x; rewrite ngraph_tnth.
exact: (Bijective h h').
Qed.

Lemma SAfuncE (s : {SAset F ^ (n + m)}) :
  reflect
  (forall (x : 'rV[F]_n), forall (y1 y2 : 'rV[F]_m),
  (row_mx x y1) \in s -> (row_mx x y2) \in s -> y1 = y2)
  (s \in SAfunc).
Proof.
rewrite inE; apply: (iffP (f_is_funcE _)) => fun_s x y1 y2.
  rewrite !inE !ngraph_cat => /fun_s fun_s1 /fun_s1.
  exact/bij_inj/ngraph_bij.
move=> s_sat1 s_sat2.
suff eq_y12 : (\row_(i < m) (nth 0 y1 i)) = (\row_(i < m) (nth 0 y2 i)).
  apply/eq_from_tnth => i.
  have /rowP /(_ i) := eq_y12.
  by rewrite !mxE !(tnth_nth 0).
by apply: (fun_s (\row_(i < n) (nth 0 x i)));
rewrite inE !ngraph_cat !ngraph_tnth.
Qed.

Fact nvar_SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) :
  formula_fv (nquantify m n Exists ((subst_formula ((iota m n)
          ++ (iota O m)) f) /\ (subst_formula (iota m n) s)))
  `<=` mnfset 0 m.
Proof.
rewrite formula_fv_nexists fsubDset fsubUset.
rewrite !(fsubset_trans (fv_subst_formula _ _));
by rewrite ?fsubsetUl // seq_fset_cat fsubset_refl.
Qed.

Definition SAimset (f : {SAset F ^ (n + m)}) (s : {SAset F^n}) :=
  \pi_{SAset F^m} (MkFormulan (nvar_SAimset f s)).

Lemma ex_yE (f : {formula_(n + m) F}) (t : 'rV[F]_n) :
  reflect (exists (u : 'rV[F]_m), rcf_sat (ngraph (row_mx t u)) f) (ex_y f t).
Proof.
apply: (iffP idP); rewrite /ex_y.
  rewrite -{1}[X in nquantify X _ _](size_ngraph t).
  move/rcf_satP/nexistsP=> [u  h].
  exists (\row_(i < m) (nth 0 u i)).
  by rewrite ngraph_cat ngraph_tnth; apply/rcf_satP.
move=> [u]; rewrite ngraph_cat => ftu.
apply/rcf_satP; rewrite -{1}[X in nquantify X _ _](size_ngraph t).
by apply/nexistsP; exists (ngraph u); apply/rcf_satP.
Qed.

Definition get_y (f : {formula_(n + m) F}) (x : 'rV[F]_n) : ('rV[F]_m):=
  match boolP (ex_y f x) with
| AltTrue p => proj1_sig (sigW (ex_yE f x p))
| AltFalse _ => (\row_(i < m) 0)
end.

Definition form_to_fun (f : {formula_(n + m) F}) : 'rV[F]_n -> 'rV[F]_m :=
  fun (x : 'rV[F]_n) => get_y f x.

Record SAfun := MkSAfun
{
  SAgraph :> {SAset F ^ (n + m)};
  _ : (SAgraph \in SAfunc) && (SAgraph \in SAtot)
}.

Definition SAfun_of of phant (F^n -> F^m) := SAfun.
Identity Coercion id_SAfun_of : SAfun_of >-> SAfun.
Local Notation "{ 'SAfun' }" := (SAfun_of (Phant (F^n -> F^m))).

Canonical SAfun_subType := [subType for SAgraph].
Definition SAfun_eqMixin := [eqMixin of SAfun by <:].
Canonical SAfun_eqType := EqType SAfun SAfun_eqMixin.
Definition SAfun_choiceMixin := [choiceMixin of SAfun by <:].
Canonical SAfun_choiceType := ChoiceType SAfun SAfun_choiceMixin.

Canonical SAfun_of_subType := [subType of {SAfun}].
Definition SAfun_of_eqType := [eqType of {SAfun}].
Definition SAfun_of_choiceType := [choiceType of {SAfun}].

Lemma SAfun_func (f : {SAfun}) (x : 'rV[F]_n) (y1 y2 : 'rV[F]_m) :
  row_mx x y1 \in SAgraph f -> row_mx x y2 \in SAgraph f -> y1 = y2.
Proof. by apply: SAfuncE; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Lemma SAfun_tot (f : {SAfun}) (x : 'rV[F]_n) :
  exists (y : 'rV[F]_m), row_mx x y \in SAgraph f.
Proof. by apply: SAtotE; case: f; move => /= [f h /andP [h1 h2]]. Qed.

Definition SAfun_to_fun (f : SAfun) : 'rV[F]_n -> 'rV[F]_m :=
  fun x => proj1_sig (sigW (SAfun_tot f x)).

Coercion SAfun_to_fun : SAfun >-> Funclass.

Lemma SAfun_functional (f : {SAfun}) : rcf_sat [::] (functional (SAgraph f)).
Proof. by move: f => [g /= /andP [functional_g _]]. Qed.

Lemma SAfun_ftotal (f : {SAfun}) : rcf_sat [::] (ftotal (SAgraph f)).
Proof. by move: f => [g /= /andP [_ ftotal_g]]. Qed.

End SAFunction.
Arguments SAfunc {F n m}.
Arguments SAtot {F n m}.
Notation "{ 'SAfun' T }" := (SAfun_of (Phant T)) : type_scope.

Section SAsetTheory.

Variable F : rcfType.

Lemma in_SAset_bottom (m : nat) (x : 'rV[F]_m) :
  x \in (@SAset_bottom F m) = false.
Proof. by rewrite pi_form. Qed.

Fact in_SAset_top (m : nat) (x : 'rV[F]_m) : x \in (@SAset_top F m).
Proof. by rewrite pi_form. Qed.

Lemma SAset1_neq0 (n : nat) (x : 'rV[F]_n) : (SAset1 x) != (@SAset_bottom F n).
Proof.
apply/negP; move/SAsetP/(_ x) => h.
by move: h; rewrite inSAset1 eqxx pi_form.
Qed.

Lemma SAemptyP (n : nat) (x : 'rV[F]_n) : x \notin (@SAset_bottom F n).
Proof. by rewrite in_SAset_bottom. Qed.

Lemma inSAset1B (n : nat) (x y : 'rV[F]_n) : (x \in SAset1 y) = (x == y).
Proof. by rewrite inSAset1. Qed.

Lemma sub_SAset1 (n : nat) (x : 'rV[F]_n) (s : {SAset F^n}) :
  (SAset1 x <= s)%O = (x \in s).
Proof.
apply: (sameP (rcf_satP _ _)).
apply: (equivP _ (nforallP _ _ _)).
apply: (iffP idP).
  move=> h t; rewrite cat0s /=.
  move/rcf_satP : h => holds_s.
  move/holds_tuple; rewrite inSAset1 => /eqP eq_x.
  by move: holds_s; rewrite -eq_x ngraph_tnth.
move/(_ (ngraph x)).
rewrite cat0s inE => /rcf_satP.
rewrite simp_rcf_sat => /implyP; apply.
apply/rcf_satP/holds_tuple; rewrite inSAset1; apply/eqP/rowP => i.
by rewrite mxE nth_ngraph.
Qed.

Lemma nn_formula (e : seq F) (f : formula F) : holds e (~ f) <-> ~ (holds e f).
Proof. by case: f. Qed.

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

Lemma decidableP (P : Prop) : decidable P -> Decidable.decidable P.
Proof. by move=> [p | np]; [left | right]. Qed.

Fact not_and (P Q : Prop) (b : bool) : reflect P b -> ~ (P /\ Q) ->  ~ P \/ ~ Q.
Proof. by move=> h; move/(Decidable.not_and P Q (decidableP (decP h))). Qed.

Lemma laya (e : seq F) (f1 f2 : formula F) :
  holds e (f1 /\ f2) <-> ((holds e f1) /\ (holds e f2)).
Proof. by []. Qed.

Lemma notP (e : seq F) (f : formula F) :
  holds e (~ f) <-> holds e (f ==> False).
Proof. by split => // h h'; move: (h h'). Qed.

Lemma non_empty : forall (n : nat) (s : {SAset F^n}),
  ((@SAset_bottom F n) < s)%O -> {x : 'rV[F]_n | x \in s}.
Proof.
move=> a s /andP [bot_neq_s _].
move: s bot_neq_s; apply: quotW => /= f; rewrite eqmodE /=.
move=> /rcf_satP/n_nforall_formula/nexistsP P.
apply: sigW; move: P => [x hx] /=; exists (\row_(i < a) x`_i).
rewrite inE ngraph_tnth rcf_sat_repr_pi.
by move/rcf_satP: hx; rewrite cat0s !simp_rcf_sat; case: rcf_sat.
Qed.

Lemma les1s2 : forall (n : nat) (s1 s2 : {SAset F^n}),
  (forall (x : 'rV[F]_n), x \in s1 -> x \in s2) -> (s1 <= s2)%O.
Proof.
move=> a s1 s2 sub12; apply/rcf_satP/nforallP => t.
rewrite cat0s /= => /rcf_satP s1_sat; apply/rcf_satP.
by move/(_ ((\row_(i < a) t`_i))): sub12; rewrite !inE ngraph_tnth => ->.
Qed.

Lemma SAunion : forall (n : nat) (x : 'rV[F]_n) (s1 s2 : {SAset F^n}),
  (x \in SAset_join s1 s2) = (x \in s1) || (x \in s2).
Proof.
move=> n x s1 s2.
rewrite /SAset_join pi_form !inE.
apply/idP/idP.
  move/rcf_satP => /=.
  by move=> [l|r]; apply/orP; [left|right]; apply/rcf_satP.
by move/orP => [l|r]; apply/rcf_satP; [left|right]; apply/rcf_satP.
Qed.

Lemma in_graph_SAfun (n m : nat) (f : {SAfun F^n -> F^m}) (x : 'rV[F]_n) :
  row_mx x (f x) \in SAgraph f.
Proof.
by rewrite /SAfun_to_fun; case: ((sigW (SAfun_tot f x))) => y h.
Qed.

Lemma in_SAimset (m n : nat) (x : 'rV[F]_n)
 (s : {SAset F^n}) (f : {SAfun F^n -> F^m}) :
  x \in s -> f x \in SAimset f s.
Proof.
rewrite pi_form /= => h.
have hsiz : m = size (ngraph (f x)) by rewrite size_ngraph.
rewrite [X in nquantify X _ _]hsiz.
apply/rcf_satP/nexistsP.
exists (ngraph x).
split; last first.
+ apply/holds_subst.
  move: h; rewrite inE.
  move/rcf_satP.
  rewrite -[ngraph (f x) ++ ngraph x]cats0.
  by rewrite -catA subst_env_iota // size_ngraph.
+ apply/holds_subst.
  move: h; rewrite inE.
  move/rcf_satP => h.
  rewrite subst_env_cat subst_env_iota_catl ?size_ngraph //.
  rewrite -[ngraph (f x) ++ ngraph x]cats0.
  rewrite -catA subst_env_iota ?size_ngraph //.
  move: (in_graph_SAfun f x); rewrite inE.
  by move/rcf_satP; rewrite ngraph_cat.
Qed.

Lemma SAsetfunsort (n m: nat) (f : {SAfun F^n -> F^m})
  (s : {SAset F^n}) (y : 'rV[F]_m) :
   reflect (exists2 x : 'rV[F]_n, x \in s & y = f x)
            (y \in (SAimset f s)).
Proof.
apply: (iffP idP); last by move=> [x h] ->; apply: in_SAimset.
rewrite /SAimset pi_form.
move/rcf_satP.
rewrite /= -[X in nquantify X _ _ _](size_ngraph y).
move/nexistsP => [t] /=.
rewrite !holds_subst subst_env_cat; move => [h1 h2].
exists (\row_(i < n) t`_i).
+ rewrite inE ngraph_tnth.
  apply/rcf_satP.
  move: h2; rewrite -[ngraph y ++ t]cats0 -catA.
  by rewrite subst_env_iota //  ?size_tuple.
+ move: h1.
  rewrite subst_env_iota_catl ?size_ngraph //.
  rewrite -[ngraph y ++ t]cats0 -catA.
  rewrite subst_env_iota ?size_ngraph // ?size_tuple //.
  rewrite /SAfun_to_fun; case: sigW => /= x h h'.
  symmetry; apply: (SAfun_func h).
  by rewrite inE ngraph_cat ngraph_tnth; apply/rcf_satP.
Qed.

Definition SAset_setMixin :=
  SET.Semiset.Mixin SAemptyP inSAset1B sub_SAset1 non_empty
  les1s2 SAunion SAsetfunsort.

Notation SemisetType set m :=
  (@SET.Semiset.pack _ _ set _ _ m _ _ (fun => id) _ id).
Canonical SAset_setType := SemisetType (SAtype F) SAset_setMixin.

Lemma in_SAfun (n m : nat) (f : {SAfun F^n -> F^m})
  (x : 'rV[F]_n) (y : 'rV[F]_m):
  (f x == y) = (row_mx x y \in SAgraph f).
Proof.
apply/eqP/idP => [<- | h]; first by rewrite in_graph_SAfun.
exact: (SAfun_func (in_graph_SAfun _ _)).
Qed.

Lemma SAfunE (n m : nat) (f1 f2 : {SAfun F^n -> F^m}) :
  reflect (f1 =1 f2) (f1 == f2).
Proof.
apply: (iffP idP); first by move/eqP ->.
move=> h; apply/SAsetP => x.
by rewrite -(cat_ffun_id x) -!in_SAfun h.
Qed.

Definition max_abs (k : nat) (x : 'rV[F]_k) :=
  \big[maxr/0]_(i < k) `|(x ord0 i)|.

Definition distance (k : nat) (x y : 'rV[F]_k) := max_abs (x - y).

(* Lemma max_vectP (k : nat) (x : 'rV[F]_k) (i :'I_k) : x ord0 i <= max_abs x. *)
(* Proof. *)
(* rewrite /max_abs; move: x i. *)
(* elim: k => [x [i lt_i0]| k ihk x i] //. *)
(* have : \big[Num.max/0]_(i0 < k.+1) `|x ord0 i0| =  *)
(*     Num.max (\big[Num.max/0]_(j0 < k) `|x ord0 ((widen_ord (leqnSn k) j0))|) (`|x ord0 ord_max|). *)
(* apply: big_ord_recr. *)
(* Qed. *)

Lemma max_vectP (k : nat) (x : 'rV[F]_k) (i :'I_k) : x ord0 i <= max_abs x.
Proof.
rewrite /max_abs; move: x i.
elim: k => [x [i lt_i0]| k ihk x i] //.
rewrite big_ord_recl lter_maxr.
have [->|] := eqVneq i ord0; first by rewrite ler_norm.
rewrite eq_sym => neq_i0; apply/orP; right.
move: (unlift_some neq_i0) => /= [j lift_0j _].
move: (ihk (\row_(i < k) x ord0 (lift ord0 i)) j); rewrite mxE /=.
rewrite (eq_big predT (fun i => `|x ord0 (lift ord0 i)|)) //.
  by rewrite -lift_0j.
by move=> l _; rewrite mxE.
Qed.

Definition abs (i j : nat) : formula F :=
  ((('X_j == 'X_i) \/ ('X_j == - 'X_i)) /\ (0 <=% 'X_j))%oT.

Lemma absP (e : seq F) (i j : nat) : holds e (abs i j) <-> e`_j = `|e`_i|.
Proof.
rewrite /abs /=; split.
+ move=> [[->|-> h]]; first by move=> h; rewrite ger0_norm.
  by rewrite ler0_norm // -oppr_gte0.
+ move->.
  rewrite normr_ge0; split => //.
  have [le_e0|lt_0e] := ler0P e`_i; first by right.
  by left.
Qed.

Lemma absP2 (e : seq F) (i j : nat) : rcf_sat e (abs i j) = (e`_j == `|e`_i|).
Proof.
apply/rcf_satP/eqP; first by move/absP.
by move=> h; apply/absP.
Qed.

Fact nvar_abs (i j : nat) : @nvar F (maxn i j).+1 (abs i j).
Proof.
rewrite /nvar -maxnSS !fsubUset !fsub1set !seq_fsetE !mem_iota.
by rewrite !add0n !maxnSS !ltnS leq_maxl leq_maxr fsub0set.
Qed.

Fact nvar_abs2 : @nvar F (1 + 1) (abs O 1).
Proof. by rewrite /nvar !fsubUset !fsub1set !seq_fsetE fsub0set. Qed.

Definition absset := \pi_{SAset F ^ (1 + 1)} (MkFormulan nvar_abs2).

Lemma functional_absset : absset \in SAfunc.
Proof.
apply/rcf_satP/nforallP => t.
move=> [/holds_subst/holds_repr_pi/absP h1 /holds_subst/holds_repr_pi/absP h2].
apply/holds_eq_vec; move: h1 h2; case: t => s sz //= {sz}.
case: s => // a s; case: s => // b s -> {b}; case: s => //.
  by move <-.
by move=> b // _ ->.
Qed.

Lemma total_absset : absset \in SAtot.
Proof.
apply/rcf_satP/nforallP => t /=.
rewrite -[X in nquantify X _ _ _](size_tuple t).
apply/nexistsP.
have size_abs_t : (size [::`|t`_0|]) == 1%N by [].
exists (Tuple size_abs_t).
move: size_abs_t; case: t => s; case: s => // x s /=.
rewrite eqSS size_eq0 => /eqP -> _.
apply/holds_repr_pi => /=.
split; last by rewrite normr_ge0.
have [le_e0|lt_0e] := ler0P x; first by right.
by left.
Qed.

Fact SAfun_SAabs : (absset \in SAfunc) && (absset \in SAtot).
Proof. by rewrite functional_absset total_absset. Qed.

Definition SAabs := MkSAfun SAfun_SAabs.

Definition diagf_form (f : {formula_(1 + 1) F}) (n : nat) (v1 v2 : seq nat) :=
(if size v1 == size v2 then
(\big[And/True]_(i < size v1)
(subst_formula [::(nth O v1 (nat_of_ord i)); (nth O v2 (nat_of_ord i))] f)%oT)
                       else False).

Fact pre_nvar_diagf_form (a b n : nat) (f : {formula_(1 + 1) F}) :
  @nvar F ((maxn a b) + n) (diagf_form f n (iota a n) (iota b n)).
Proof.
rewrite /diagf_form !size_iota eqxx /nvar formula_fv_bigAnd.
apply/bigfcupsP => /= i _.
rewrite (fsubset_trans (fv_subst_formula _ _)) //.
apply/fsubsetP=> j.
rewrite !seq_fsetE mem_iota /=.
rewrite in_cons mem_seq1 add0n !nth_iota //.
rewrite addn_maxl.
by move/orP => [/eqP -> | /eqP ->]; rewrite leq_max ltn_add2l ltn_ord //= orbT.
Qed.

Fact nvar_diagf_form (f : {formula_(1 + 1) F}) (n : nat) :
  @nvar F (n + n) (diagf_form f n (iota 0 n) (iota n n)).
Proof. by rewrite -{1}[n]max0n pre_nvar_diagf_form. Qed.

Definition diagf (n : nat) (f : {formula_(1 + 1) F}) :=
  \pi_{SAset F ^ (n + n)} (MkFormulan (nvar_diagf_form f n)).

Lemma functional_diagf (f : {SAfun F^1 -> F^1}) (n : nat) :
  diagf n f \in SAfunc.
Proof.
apply/rcf_satP/nforallP => t [/holds_subst h1 /holds_subst h2].
move: h1 h2; rewrite !subst_env_cat /diagf.
move/holds_repr_pi/rcf_satP => h1.
move/holds_repr_pi/rcf_satP.
move: h1.
rewrite /= /diagf_form !size_iota eqxx !rcf_sat_forall=> /forallP h1 /forallP h2.
apply/holds_eq_vec.
apply: (@eq_from_nth _ 0) => [ | i ]; rewrite !subst_envP // => lt_in.
rewrite !(nth_map O) ?size_iota //.
move/(_ (Ordinal lt_in))/rcf_satP/holds_subst : h2.
move/(_ (Ordinal lt_in))/rcf_satP/holds_subst : h1.
rewrite !nth_iota //= ?nth_cat ?size_iota ?subst_envP lt_in.
rewrite -[X in (_ < X)%N]addn0 ltn_add2l ltn0 add0n.
rewrite !(nth_map O) ?size_iota // ?(addnC, addnK) //.
rewrite [in (n + _ - n)%N]addnC addnK.
rewrite !nth_iota // add0n => /rcf_satP h1 /rcf_satP h2.
move: (@SAfun_func F 1 1 f (const_mx t`_i)
                           (const_mx t`_(n + i))
                           (const_mx t`_(2 * n + i))).
rewrite !inE !ngraph_cat /= enum_ordS.
have -> : enum 'I_0 = [::] by apply: size0nil; rewrite size_enum_ord.
rewrite /= !mxE mul2n -addnn.
by move/(_ h1 h2)/matrixP/(_ ord0 ord0); rewrite !mxE.
Qed.

Lemma total_diagf (f : SAfun F 1 1) (n : nat) : diagf n f \in SAtot.
Proof.
apply/rcf_satP/nforallP => t.
rewrite -[X in nquantify X _ _ _](size_tuple t).
apply/nexistsP.
pose x := \row_(i < n) ((f (const_mx (nth 0 t (nat_of_ord i)))) ord0 ord0).
exists (ngraph x); apply/holds_repr_pi => /=.
rewrite /diagf_form !size_iota eqxx.
apply/rcf_satP; rewrite rcf_sat_forall; apply/forallP => /= i.
apply/rcf_satP/holds_subst.
rewrite ?nth_iota // add0n /= !nth_cat size_tuple ltn_ord.
rewrite -ltn_subRL subnn ltn0. (* this line can be used earlier in the code *)
rewrite addnC addnK.
move : (in_graph_SAfun f (const_mx t`_i)); rewrite inE.
move/rcf_satP; apply: eqn_holds => j y.
rewrite !mxE /=.
rewrite (nth_map 0); last by rewrite size_enum_ord ltn_ord.
rewrite (nth_map 0); last by rewrite -enumT size_enum_ord.
rewrite -enumT nth_ord_enum; case: y => m lt_m2.
rewrite mxE; case: splitP => k ->; first by rewrite !ord1 mxE.
rewrite !ord1 addn0 -[in RHS]tnth_nth /=.
have -> : [seq (\row_i1 (f (const_mx t`_i1)) 0 0) 0 i0 | i0 <- enum 'I_n]`_i =
           (\row_i1 (f (const_mx t`_i1)) 0 0) 0 i.
  by rewrite mxE (nth_map i _) ?size_enum_ord // nth_ord_enum mxE.
by rewrite mxE.
Qed.

Fact SAfun_diagf (f : {SAfun F^1 -> F^1}) (n : nat) :
   (diagf n f \in SAfunc) && (diagf n f \in SAtot).
Proof. by rewrite functional_diagf total_diagf. Qed.

Definition SAdiagf (f : {SAfun F^1 -> F^1}) (n : nat) :=
  MkSAfun (SAfun_diagf f n).

Definition comp_formula (m n p : nat)
  (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) : formula F :=
  nquantify (m + p) n Exists
  ((subst_formula ((iota O m) ++ (iota (m + p) n)) (repr (val f))) /\
  (subst_formula ((iota (m + p) n) ++ (iota m p)) (repr (val g)))).

Fact nvar_comp_formula (m n p : nat)
  (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) :
  @nvar F (m + p) (comp_formula f g).
Proof.
rewrite /nvar /comp_formula /= formula_fv_nexists fsubDset fsetUC -seq_fset_cat.
rewrite -iota_add /= fsubUset.
rewrite ?(fsubset_trans (fv_subst_formula _ _)) // => {f} {g};
rewrite seq_fset_cat fsubUset; apply/andP; split.
case: n=> [|n]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n.
case: p=> [|p]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n leq_addr.
case: m=> [|m]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n add0n -addnA leq_addr.
case: n=> [|n]; rewrite ?seq_fset_nil ?fsub0set //.
by rewrite mnfset_sub // leq0n /= add0n.
Qed.

Definition SAcomp_graph m n p (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) 
  := \pi_{SAset F ^ (m + p)} (MkFormulan (nvar_comp_formula f g)).

Lemma holds_ngraph (m n : nat) (f : {SAfun F^m -> F^n}) (t : 'rV[F]_(m + n)) :
reflect (holds (ngraph t) f) (t \in SAgraph f).
Proof. by rewrite inE; apply: rcf_satP. Qed.

Lemma SAcomp_graphP (m n p : nat)
  (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p})
  (u : 'rV[F]_m) (v : 'rV[F]_p) :
    (row_mx u v \in SAcomp_graph f g) = (g (f u) == v).
Proof.
rewrite /SAcomp_graph /= pi_form ngraph_cat /comp_formula.
have h : size ([seq u ord0 i | i <- enum 'I_m] ++
               [seq v ord0 i | i <- enum 'I_p]) = (m + p)%N.
  by rewrite size_cat size_map size_enum_ord size_map size_enum_ord.
rewrite /= -[X in nquantify X _ _ _]h.
apply: (sameP (rcf_satP _ _)).
apply: (equivP _ (nexistsP _ _ _)).
apply: (iffP idP); last first.
+  move=> [t] /=.
  move=> [ /holds_subst hf /holds_subst hg].
  move: hf hg.
  rewrite subst_env_cat -catA.
  rewrite subst_env_iota_catl; last by rewrite size_map size_enum_ord.
  rewrite catA subst_env_iota_catr ?size_tuple ?card_ord //.
  rewrite subst_env_cat subst_env_iota_catr ?size_tuple ?card_ord //.
  rewrite -catA subst_env_iota; last 2 first.
  - by rewrite size_map size_enum_ord.
  - by rewrite size_map size_enum_ord.
  rewrite -[t]ngraph_tnth -!ngraph_cat.
  move/holds_ngraph; rewrite -in_SAfun; move/eqP ->.
  by move/holds_ngraph; rewrite -in_SAfun; move/eqP ->.
+ move/eqP => eq_gfu_v.
  exists (ngraph (f u)).
  split; apply/holds_subst; rewrite subst_env_cat.
  - rewrite -catA subst_env_iota_catl; last by rewrite size_map size_enum_ord.
    rewrite catA subst_env_iota_catr ?size_tuple ?card_ord // -ngraph_cat.
    by apply/holds_ngraph; apply: in_graph_SAfun.
  - rewrite subst_env_iota_catr ?size_tuple ?card_ord //.
    rewrite -catA subst_env_iota; last 2 first.
      by rewrite size_map size_enum_ord.
    by rewrite size_map size_enum_ord.
    rewrite -ngraph_cat; apply/holds_ngraph; rewrite -eq_gfu_v.
    exact: in_graph_SAfun.
Qed.

Fact SAfun_SAcomp m n p (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) :
  (SAcomp_graph f g \in SAfunc) && (SAcomp_graph f g \in SAtot).
Proof.
apply/andP; split.
  by apply/SAfuncE => x y1 y2; rewrite !SAcomp_graphP; move=> /eqP-> /eqP->.
by apply/SAtotE => x; exists (g (f x)); rewrite SAcomp_graphP.
Qed.

Definition SAcomp m n p (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) :=
  MkSAfun (SAfun_SAcomp f g).

Lemma SAcompP m n p (f : {SAfun F^m -> F^n}) (g : {SAfun F^n -> F^p}) :
  SAcomp f g =1 g \o f.
Proof.
move=> x; apply/eqP; rewrite eq_sym -SAcomp_graphP.
by move: (in_graph_SAfun (SAcomp f g) x).
Qed.

Fact form_rproj_proof (n k : nat) (f : {formula_n F}) : 
  nvar k.+1 (nquantify k.+1 (n.-1 - k) Exists f).
Proof.
move: (nvar_formulan f); rewrite /nvar => nvar_f.
rewrite formula_fv_nexists fsubDset fsetUC -mnfset_triangle.
rewrite (fsubset_trans nvar_f) // => {f} {nvar_f}. 
case: n => [|n] ; first by rewrite seq_fset_nil fsub0set.
rewrite mnfset_sub //= !add0n.
have [lt_nk|leq_kn] := ltnP n k; first by rewrite ltn_addr // ltnW.
by rewrite -[k.+1]add1n -addnA subnKC // add1n ltnSn.
Qed.

Definition form_rproj (n k : nat) (f : {formula_n F}) := 
  MkFormulan (form_rproj_proof k f).

Definition rproj (n k : nat) (s : {SAset F ^ n}) := 
  \pi_{SAset F ^ k.+1} (form_rproj k s).

Fact eq_knk (n : nat) (k : 'I_n) : (k.+1 + (n.-1 - k) = n)%N.
Proof.
move: k; case: n => [[*]|n k] //.
by rewrite -[k.+1]add1n -addnA subnKC //= leq_ord.
Qed.

Fact castmx_tcast (a n : nat) (p : (1 = 1)%N * (n = a)) (x : 'rV[F]_n) : 
  ngraph (castmx p x) = tcast (snd p) (ngraph x).
Proof.
apply: eq_from_tnth => i.
by rewrite tcastE !tnth_map castmxE cast_ord_id !tnth_ord_tuple.
Qed.

Fact val_tcast (n m : nat) (p : n = m) t : tcast p t = t :> seq F.
Proof. by move: p; case: _ /. Qed.

Fact ngraph_castmx (a n : nat) (p : (1 = 1)%N * (n = a)) 
  (x : 'rV[F]_n) : 
  ngraph (castmx p x) = ngraph x :> seq F.
Proof. by rewrite castmx_tcast val_tcast. Qed.

Lemma rprojP (n : nat) (k : 'I_n) (s : {SAset F ^ n}) (u : 'rV[F]_k.+1) : 
  u \in (rproj k s) <-> 
  exists (v : 'rV[F]_(n.-1 - k)), 
    (castmx ((erefl _), (eq_knk _)) (row_mx u v)) \in s. 
Proof.
rewrite /rproj inE rcf_sat_repr_pi /form_rproj /=.
pose e := [seq u ord0 i | i <- enum 'I_k.+1].
have size_e : size e = k.+1 by rewrite /e size_map size_enum_ord.
rewrite -[X in nquantify X _ _ _]size_e.
split.
+ move/rcf_satP/nexistsP => [v hv].
  exists (\row_(i < n.-1 - k) (nth 0 v i)).
  rewrite inE; apply/rcf_satP.
  move: hv; congr holds; rewrite ngraph_castmx ngraph_cat /=.
  congr cat.
  apply: (@eq_from_nth _ 0) => [|i].
    by rewrite size_map size_tuple size_enum_ord.
  rewrite size_tuple; move: v.
  case: (n.-1 - k)%N => // m v lt_iv.
  rewrite (nth_map ord0) ?size_enum_ord // mxE.
  by rewrite nth_enum_ord.
+ move=> [v].
  rewrite inE ngraph_castmx.
  move/rcf_satP; rewrite ngraph_cat=> h.
  by apply/rcf_satP/nexistsP; exists (ngraph v).
Qed.

Section Interval.

Fact nvar_interval_a_inf (a : F) : 
  formula_fv ((a %:T) <% 'X_0)%oT `<=` mnfset 0 1.
Proof. by rewrite /= fset0U; apply/fsubsetP => x; rewrite in_fset1. Qed.

Definition interval_a_inf (a : F) := 
  \pi_({SAset F^1}) (MkFormulan (nvar_interval_a_inf a)).

Fact nvar_interval_inf_b (b : F) : 
  formula_fv ('X_0 <% (b %:T))%oT `<=` mnfset 0 1.
Proof. by rewrite /= fsetU0; apply/fsubsetP => x; rewrite in_fset1. Qed.

Definition interval_inf_b (b : F) := 
  \pi_({SAset F^1}) (MkFormulan (nvar_interval_inf_b b)).

Fact nvar_interval_a_b (a b : F) :
  formula_fv ((a %:T <% 'X_0) /\ ('X_0 <% b %:T))%oT `<=` mnfset 0 1.
Proof.
by rewrite /= fset0U fsetU0 fsetUid; apply/fsubsetP => x; rewrite in_fset1.
Qed.

Definition interval_a_b (a b : F) : {SAset F^1} := 
  \pi_({SAset F^1}) (MkFormulan (nvar_interval_a_b a b)).

Fail Check (setT : {SAset F}).

Import SET.SetSyntax.

Check (setT : {SAset F^1}).

Definition singleton (a : F) : {SAset F ^ 1} := SET.set1 (\row_(i < 1) a).

Lemma in_interval_a_inf (a : F) (x : 'rV_1) : 
  (x \in (interval_a_inf a)) = (a < x 0 0).
Proof.
rewrite /interval_a_inf inE rcf_sat_repr_pi.
by apply/rcf_satP/idP ; rewrite /= enum_ordS.
Qed.

Lemma in_interval_inf_b (b : F) (x : 'rV_1) : 
  (x \in (interval_inf_b b)) = (x 0 0 < b).
Proof.
rewrite /interval_a_inf inE rcf_sat_repr_pi.
by apply/rcf_satP/idP ; rewrite /= enum_ordS.
Qed.

Lemma in_interval_a_b (a b : F) (x : 'rV_1) : 
  (x \in (interval_a_b a b)) = (a < x 0 0 < b).
Proof.
rewrite /interval_a_inf inE rcf_sat_repr_pi.
by apply/rcf_satP/idP ; rewrite /= enum_ordS ; move/andP.
Qed.

Lemma in_singleton (a : F) (x : 'rV_1) : (x \in (singleton a)) = (x 0 0 == a).
Proof.
rewrite /singleton inE rcf_sat_repr_pi /SAset1_formula /=.
rewrite enum_ordS map_cons big_ord_recl big_ord0 mxE.
by apply/rcf_satP/idP => [ [/eqP eq_xa _] | /eqP ->].
Qed.

Definition in_interval := 
  (in_interval_a_inf, in_interval_inf_b, in_interval_a_b, in_singleton).

Lemma intervalI_inf_b_sing (b a : F) :
  SET.SetSyntax.setI (interval_inf_b b) (singleton a) = 
  if a < b then (singleton a) else set0.
Proof.
have [lt_ab|] := boolP (a < b).
+ apply/eqP/SAsetP => x.
  rewrite !in_interval SET.SemisetTheory.in_setI !in_interval.
  have [->|/negbTE ->] := eqVneq (x 0 0) a; first by rewrite eqxx andbT.
  by rewrite andbF.
+ rewrite -lerNgt => leq_ba.
  apply/eqP/SAsetP => x.
  rewrite SET.SemisetTheory.in_setI !in_interval SET.SemisetTheory.in_set0.
  move: leq_ba ; apply: contraTF.
  by rewrite andbC => /andP [] /eqP -> ; rewrite ltrNge.
Qed.

Lemma intervalI_inf_b_int (c a b : F) :
  SET.SetSyntax.setI (interval_inf_b c) (interval_a_b a b) = 
  interval_a_b a (Num.min c b).
Proof.
apply/eqP/SAsetP => x.
rewrite !in_interval SET.SemisetTheory.in_setI !in_interval.
by rewrite andbC ltr_minr andbAC andbA.
Qed.

Lemma intervalI_inf_b_a_inf (b a : F) :
  SET.SetSyntax.setI (interval_inf_b b) (interval_a_inf a) = 
  interval_a_b a b.
Proof.
apply/eqP/SAsetP => x.
by rewrite !in_interval SET.SemisetTheory.in_setI !in_interval andbC.
Qed.

(* Definition is_pos_nat (x : F) := *)
(*   if x > 0 then  *)
(*            else false. *)

(* Definition is_nat (x : F) := *)

(* Variables (f : nat -> nat) (x : nat) (y : F). *)

(* Check ((f x).+1 : nat). *)
(* Check (x%:R : F). *)
(* Check (((f x).+1)%:R : F). *)

(* Definition send_to_F (f : nat -> nat) : F -> F := *)
(*   fun (x : nat) => *)

(* Definition dec_eq (A : Type) := forall (f g : A -> A), Decidable.decidable (f =1 g). *)

(* Lemma not_dec_eq_nat : ~ (dec_eq nat).  *)
(* Proof. *)
(* rewrite /dec_eq => h. *)

(* Qed. *)


(* Lemma not_dec_equality : ~ (forall (f g : F -> F), Decidable.decidable (f =1 g)). *)
(* Proof. *)
(* suff h : ~ (forall (f : F -> F), Decidable.decidable (forall x, f x = 0)). *)
(* move=> h2. *)
(* apply: h => f. *)
(* move/(_ f)/(_ (fun x => 0)) : h2. *)
(* move=> [eq_f0|Neq_f0]. *)
(* left => x. *)
(* by rewrite eq_f0. *)
(* right. *)
(* move=> h. *)
(* apply: Neq_f0. *)
(* by move=> y. *)
(* rewrite /Decidable.decidable. *)
(* move=> h. *)

(* rewrite /=. *)



(* move=> h. *)
(* pose g0 : F -> F := fun x => 0. *)

(* Qed. *)

(* Variables (f g : F -> F). *)

(* Check (f =1 g). *)
(* Check (Decidable.decidable (f =1 g)). *)

(* Decidable.decidable *)

(* Definition eq_dec := forall (f g : F -> F),  *)

(* Lemma not_dec_equality : forall (f g : F -> F),  *)

Definition intervalI :=
  (intervalI_inf_b_sing, intervalI_inf_b_int, intervalI_inf_b_a_inf).

(* generalization ? *)
Lemma neq_interval_a_b_sing (a b c : F) : interval_a_b a b != singleton c. 
Proof.
apply/negP.
move/SAsetP.
have [lt_ab| /negP leq_ba] := boolP (a < b) ; last first.
  move/(_ (\row_(i < 1) c)).
  rewrite !in_interval !mxE eqxx /=.
  move/andP => [lt_ac lt_cb].
  by move: (ltr_trans lt_ac lt_cb).
have [|] := boolP ((\row_(i < 1) c) \in (interval_a_b a b)).
rewrite in_interval mxE.
move/andP => [lt_ac lt_cb].
move/(_ ((\row_(i < 1) ((c + b) / 2%:R)))).
rewrite !in_interval mxE.
rewrite !midf_lt //= andbT.
rewrite ltr_pdivl_mulr; last by rewrite ltr0n.
rewrite {1}mulr2n !mulrDr !mulr1 ltr_add //=.
move/(@Logic.eq_sym _ _ _).
have -> : ((c + b) / 2%:R == c) = ((c + b) == c + c)%R ; last first.
move/eqP/addrI/eqP.
by rewrite gtr_eqF.
apply/eqP/eqP; last first.
  by move=> -> ; rewrite -mulr2n -[X in X / _]mulr_natr mulfK // pnatr_eq0.
move/(congr1 (fun x => x * 2%:R)).
rewrite mulfVK; last by rewrite pnatr_eq0.
by move=> -> ; rewrite mulr2n !mulrDr !mulr1.
rewrite in_interval mxE.
rewrite negb_and.
move/orP=> [/negbTE le_ca| /negbTE le_bc].
move/(_ (\row_(i < 1) c)).
by rewrite !in_interval mxE eqxx le_ca.
move/(_ (\row_(i < 1) c)).
by rewrite !in_interval mxE eqxx le_bc andbF .
Qed.


End Interval.

Section Continuity.

Definition sub_vec (v1 v2 v3 : seq nat) : formula F :=
if ((size v1 == size v2) && (size v1 == size v3)) 
  then \big[And/True]_(i < size v1) ( 'X_(nth O v1 i) ==
       'X_(nth O v2 i) + 'X_(nth O v3 i))%oT 
  else False.

Lemma sub_vecP (e : seq F) (v1 v2 v3 : seq nat) :
rcf_sat e (sub_vec v1 v2 v3) = ((size v1 == size v2) && (size v1 == size v3)) &&
[forall i, 
(e`_(nth O v3 (i : 'I_(size v1))) == e`_(nth O v1 i) - e`_(nth O v2 i))].
Proof.
rewrite /sub_vec ; case : (_ == _) ; case : (_ == _) => //.
rewrite rcf_sat_forall ; apply/eq_forallb => i.
by apply/rcf_satP/idP => //=; rewrite eq_sym subr_eq addrC; move/eqP.
Qed.

Definition abs_vec (v1 v2 : seq nat) : formula F := 
  if size v1 == size v2 
    then (\big[And/True]_(i < size v1) (abs (nth O v1 i)) (nth O v2 i))%oT 
    else False.

Lemma abs_vecP (e : seq F) (v1 v2 : seq nat) :
rcf_sat e (abs_vec v1 v2) = (size v1 == size v2)
          && [forall i, e`_(nth O v2  (i : 'I_(size v1))) == `|e`_(nth O v1 i)|].
Proof.
rewrite /abs_vec ; case : (_ == _) => //=.
rewrite rcf_sat_forall; apply/eq_forallb => i.
by rewrite absP2.
Qed.

Definition max_vec (v : seq nat) (n : nat) : formula F :=
  ((\big[Or/False]_(i < size v) ('X_n == 'X_(nth O v i))) /\
  (\big[And/True]_(i < size v) ('X_(nth O v i) <=% 'X_n)))%oT.

(* Lemma max_vecP (e : seq F) (v : seq nat) (n : nat) : *)
(* rcf_sat e (max_vec v n) = . *)
(* Proof. *)
(* maxr *)
(* foldr *)
(* Qed. *)

Definition bloc (n : nat) : formula F := 
  (sub_vec (iota 0 n) (iota n n) (iota (n + n) n))
  /\ (abs_vec (iota (n + n) n) (iota (3 * n) n))
  /\ (max_vec (iota (3 * n) n) (4 * n))
  /\ ('X_(4 * n) <=% 'X_((4 * n).+1)).

(* Lemma holds_bloc (e : seq F) (n : nat) : *)
(*     holds e (bloc n) <->  *)

Variables (n m : nat).

Definition pre_is_continuous_form (f : {formula_(n + m) F}) : formula F :=  
  (bloc n) ==> (subst_formula (iota (4 * n + 2) (4 * m + 1)) (bloc m))
  /\ (subst_formula ((iota 0 n) ++ (iota (4 * n + 2) m)) f)
  /\ (subst_formula ((iota n n) ++ (iota (4 * n + m + 2) m)) f).

Definition is_continuous_form (f : {formula_(n + m) F}) : formula F :=
  nquantify 0 n Forall ('forall 'X_(4 * n + 4 * m + 3),
                       ('exists 'X_(4 * n + 1), (nquantify n (2 * n) Forall
                       (nquantify (n + n) (2 * n + 1) Forall
                       (nquantify (4 * n + 2) (4 * m + 1) Forall (pre_is_continuous_form f)))))).

(* Axiom is_continuous : {SAfun F^n -> F^m} -> bool. *)
Definition is_continuous (f : {SAfun F^n -> F^m}) := 
  rcf_sat [::] (is_continuous_form f).

Definition continuous_spec (f : {SAfun F^n -> F^m}) : Prop := 
  forall (x : 'rV[F]_n) (eps : F), exists (eta : F), forall (y : 'rV[F]_n), 
  distance x y < eta -> distance (f x) (f y) < eps.

(* Axiom continousP :  *)
(*   forall (f : {SAfun F^n -> F^m}), reflect (continuous_spec f) (is_continuous f). *)

Lemma fsubst_forall (i j : nat) (f : formula F) (t : GRing.term F) : 
  (i != j)%N -> 
  fsubst ('forall 'X_i, f) (j, t) = ('forall 'X_i, (fsubst f (j, t)))%oT. 
Proof. by move/negbTE=> /= ->. Qed. 

Lemma fsubst_nquantify (f : formula F) (i : nat) (t : GRing.term F) a b: 
(i < a)%N || (a + b <= i)%N -> 
  fsubst (nquantify a b Forall f) (i, t) = 
  (nquantify a b Forall (fsubst f (i, t))). 
Proof.
move: f i t a ; elim : b => [ | b ihb] f i t a h ; first by rewrite !nquantify0.
rewrite nquantSin ihb; last first.
+ move/orP: h => [lt_ia | ] ; first by rewrite lt_ia.
  by rewrite addnS ; move/ltnW -> ; rewrite orbT.
+ rewrite nquantSin fsubst_forall //.
  move/orP: h => [lt_ia |].
    by rewrite neq_ltn (leq_trans lt_ia) ?orbT // ?leq_addr.
  by rewrite addnS neq_ltn ; move ->.
Qed.



Lemma continuousP (f : {SAfun F^n -> F^m}) : 
  reflect (continuous_spec f) (is_continuous f).
Proof.
rewrite /continuous_spec /is_continuous. 
rewrite /is_continuous_form /pre_is_continuous_form /bloc.
apply: (iffP idP).
+ move/rcf_satP.
  rewrite /=.
  move/nforallP.
  move=> h x eps.
  move: h.
  move/(_ (ngraph x)).
  rewrite cat0s.
  rewrite /=.
  move/(_ eps)=> [eta h].
  exists eta.
  move=> y.
  move: h.
  rewrite -holds_fsubst.
  rewrite -holds_fsubst.
  rewrite fsubst_nquantify; last first.
    rewrite -mulSn addn1.
    rewrite (leq_trans _ (leqnSn _)) ?orbT //.
    by rewrite leq_mul.
  rewrite fsubst_nquantify; last first.
    apply/orP; right.
    admit.
  have h : size ([seq x ord0 i | i <- enum 'I_n]) = n.
    rewrite size_map.
    by rewrite size_enum_ord.
  rewrite -[in X in nquantify X _ _ _]h.
  move/nforallP.
  have h2 : forall (a : nat), (2 * a = a + a)%N.
    admit.
  rewrite h2.
  move/(_ (ngraph (row_mx x y))).
  rewrite /=.
  rewrite fsubst_nquantify; last first.
    admit.
  rewrite fsubst_nquantify; last first.
    admit.
  rewrite fsubst_nquantify; last first.
    admit.
  rewrite fsubst_nquantify; last first.
    admit.
  rewrite /=.
  have -> : (4 * n)%N == (4 * n + 1)%N = false.
    admit.
  rewrite -[((4 * n) .+1)%N]addn1 eqxx /=.
  have -> : (4 * n)%N == (4 * n + 4 * m + 3)%N = false.
    admit.
  rewrite /=.
  rewrite [X in fsubst X]fsubst_id; last first.
    rewrite /sub_vec.
    rewrite !size_iota eqxx /=.
    rewrite formula_fv_bigU.
    rewrite /=.
    apply/bigfcupP.
    move=> [i hi].
    rewrite !inE.
    rewrite !nth_iota ?ltn_ord //.
    admit.
  rewrite fsubst_id; last first.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    admit.
  rewrite fsubst_id; last first.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    rewrite formula_fv_bigOr.
    rewrite /=.
    apply/bigfcupP.
    rewrite size_iota.
    move=> [i /= _].
    rewrite !inE.
    rewrite !nth_iota ?ltn_ord //.
    admit.
  rewrite fsubst_id; last first.
  rewrite formula_fv_bigOr.
  apply/bigfcupP.
  rewrite size_iota.
  move=> [i /= _].
  rewrite !inE.
  rewrite !nth_iota ?ltn_ord //.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    rewrite formula_fv_bigAnd /=.
    apply/bigfcupP.
    rewrite size_iota.
    move=> [i /= _].
    rewrite !inE.
    rewrite !nth_iota ?ltn_ord //.
    admit.
  rewrite fsubst_id; last first.
    rewrite formula_fv_bigAnd /=.
    apply/bigfcupP.
    rewrite size_iota.
    move=> [i /= _].
    rewrite !inE.
    rewrite !nth_iota ?ltn_ord //.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    rewrite -fsub1set.
    have fsubset_trans2 :
    forall (x y z : {fset nat}), (x `<=` y) -> ((z `<=` x) -> (z `<=` y)).
      move=> u v w huw hwu.
      by apply: (fsubset_trans hwu).
    apply: (@contra _ ([fset (4 * n + 1)%N]
   `<=`seq_fset (iota (4 * n + 2) (4 * m + 1)))); last first.
      rewrite fsub1set.
      rewrite seq_fsetE.
      rewrite mem_iota.
      admit.
    apply: fsubset_trans2.
    by rewrite fv_subst_formula.
  rewrite fsubst_id; last first.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    admit.
  rewrite fsubst_id; last first.
    admit.
  rewrite [X in fsubst X]fsubst_id; last first.
    admit.
  rewrite fsubst_id; last first.
    admit.
Admitted.

End Continuity.

Section PolynomialTerm.

Definition nvar_term (T : Type) n : pred_class := fun t :
  term T => (term_fv t `<=` mnfset O n).

Variables (R : unitRingType) (n : nat).

Record Polynomialn := MkPolynomialn
{
  underlying_term :> term R;
  _ : (nvar_term n underlying_term) && (GRing.rterm underlying_term)
}.

(* Notation "'{polynomial_' n R }" := (polynomialn R n). *)

Canonical Polynomialn_subType := [subType for underlying_term].
(* Definition Polynomialn_eqMixin := [eqMixin of Polynomialn by <:]. *)
(* Canonical SAfun_eqType := EqType SAfun SAfun_eqMixin. *)
(* Definition SAfun_choiceMixin := [choiceMixin of SAfun by <:]. *)
(* Canonical SAfun_choiceType := ChoiceType SAfun SAfun_choiceMixin. *)


End PolynomialTerm.

(* Section MorePolynomialTerm. *)
(* Definition polynomialn_eqMixin (R : unitRingType) n := [eqMixin of {polynomial_n R} by <:]. *)
(* Canonical polynomialn_eqType n := *)
(*   EqType (polynomialn n) (polynomialn_eqMixin n). *)


(* End MorePolynomialTerm. *)

Section CAD.

Variable (is_connected : forall (n : nat), {SAset F ^ n} -> bool).

Section Varn.
Variable (n : nat).

Import SET.SetSyntax.

(* temporary hack *)
Notation SAimset := (@SET.imset _ _ _ SAset_setType).

Definition connected_spec (s : {SAset F ^ n}) : Prop :=
  forall (x y : 'rV[F]_n), exists (f : {SAfun F^1 -> F^n}),
    is_continuous f /\ (f 0 = x) /\ (f 1 = y)
                    /\ (SAimset f (interval_a_b 0 1) \subset s).

Axiom connectedP : forall (s : {SAset F ^ n}),
  reflect (connected_spec s) (is_connected s).

Section AuxPredicates.
Variable (cad : {fset {SAset F ^ n}}).

Definition non_empty_cells := all (fun x => x != set0) (enum_fset cad).

Definition connected_cells := all (@is_connected n) (enum_fset cad).

Definition disjoint_cells :=
 all (fun x => ((x.1 != x.2)%PAIR ==> (((x.1 :&: x.2)%PAIR) == set0))) 
     [seq (a, b) | a <- (enum_fset cad), b <- (enum_fset cad)].

(* Definition disjoint_cells2 := *)
(*   all predT (enum_fset [fset (a, b) | a : cad, b : cad]). *)

(* Variables (m : nat) (s : {SAset F ^ m}). *)
(* Check (\big[setU/set0]_(i : cad) val i) : {}. *)
(* Check (setT). *)

Definition covers (s : {SAset F ^ n}) := 
  s \subset (\big[setU/set0]_(i : cad) val i).

Definition projection_cell (k : 'I_n) :=
all (fun x => 
      ((x.1 != x.2)%PAIR ==> 
        ( ((((rproj k x.1) :&: (rproj k x.2))%PAIR) == set0)
          || ((((rproj k x.1) :&: (rproj k x.2))%PAIR) == setT) ))) 
    [seq (a, b) | a <- (enum_fset cad), b <- (enum_fset cad)].

Definition cylindric := [forall k, projection_cell k].

End AuxPredicates.

Record CAD_output := MkCAD
{
  cells :> {fset {SAset F ^ n}};
  _ : (non_empty_cells cells) && (disjoint_cells cells)
                              && (covers cells setT)
                              && (connected_cells cells)
                              && (cylindric cells)
}.

End Varn.

(* Variables (n : nat) (x : {SAset F ^ n}) (s : {fset {SAset F ^ n}}). *)

(* Check (all true ). *)

Lemma disjoint_cellsP (n : nat) (x : {SAset F ^ n}) (s : {fset {SAset F ^ n}}) :
  x \notin s ->
  disjoint_cells (x |` s) = 
  (all (fun (y : {SAset F ^ n}) 
   => (SET.SetSyntax.setI y x == 0)%O) (enum_fset s)) && (disjoint_cells s).
Proof.
move=> notin_xs ; rewrite /disjoint_cells /=.
have h : enum_fset (x |` s) =i x :: (enum_fset s).
  by move=> y ; rewrite in_cons !inE.
have h2 : [seq (a, b) | a <- enum_fset (x |` s), b <- enum_fset (x |` s)] =i
          [seq (a, b) | a <- x :: (enum_fset s), b <- x :: (enum_fset s)].
  by apply: mem_allpairs.
rewrite (eq_all_r h2) => {h2} /=.
rewrite eqxx all_cat.
have h2 : [seq (a, b) | a <- enum_fset s, b <- x :: enum_fset s] =i
          [seq (a, x) | a <- enum_fset s] ++
          [seq (a, b) | a <- enum_fset s, b <- enum_fset s].
  by rewrite -cat1s => y ; rewrite allpairs_catr mem_cat.
rewrite /=.
rewrite (eq_all_r h2) => {h2}.
rewrite all_cat andbA ; congr andb => //=.
rewrite andb_idl ; last first.
  rewrite !all_map ; apply: sub_all => y /=. 
  by rewrite eq_sym SET.SemisetTheory.setIC.
rewrite all_map ; apply: eq_in_all => /= y.
case: (SET.SetSyntax.setI y x == 0%O) => //= ; rewrite ?implybT //=.
by rewrite implybF negbK ; apply: contraTF ; move/eqP ->.
Qed.

Check (forall (n : nat), seq (mpoly.mpoly n F) -> CAD_output n).

Variables (o1 : CAD_output O) (o2 : CAD_output 1) 
          (o3 : forall (n : nat), seq (mpoly.mpoly n F) -> CAD_output n).

Variable (is_cst : forall n m, {SAfun F^n -> F^m} -> {SAset F ^ n} -> bool).

Lemma is_cstP (n m : nat) (f : {SAfun F^n -> F^m}) (s : {SAset F^n}) :
  reflect (forall (x y : 'rV_n), f x = f y) (is_cst f s).
Admitted.

Variable (sign : {SAfun F^1 -> F^1}).

Notation "{ 'mpoly' T [ n ] }" := (mpoly_of n (Phant T)).

Variable (sampoly : forall (n : nat), mpoly n F -> {SAfun F^n -> F^1}).
(* Variable (sampoly : forall (n : nat), {mpoly F[n]}). *)

Import SET.SetSyntax.
(* temporary hack *)
Notation SAimset := (@SET.imset _ _ _ SAset_setType).
(* Notation proper0 := (@proper0 _ _ _ SAset_setType). *)
Import SET.SemisetTheory.

Lemma aux_set (n : nat) (s : {SAset F^n}) : s != set0 -> set0 \proper s.
Proof. by rewrite (@proper0 _ _ _ SAset_setType n s). Qed.

(* Definition get_val (n : nat) (s : {SAset F^n}) := match (boolP (s == set0)) with *)
(*   | AltTrue _ => None *)
(*   | AltFalse p => Some (sval (@set_gt0_ex _ _ _ SAset_setType n s (aux_set p)))  *)
(* end. *)

Definition get_cst_value m x0 n (s : {SAset F^n}) x (f : {SAfun F^n -> F^m}) :=
  if (x \in s) && (is_cst f s) then (f x) else x0.

(* Lemma get_cst_ValueP (n : nat) (s : {SAset F^n}) (p : mpoly.mpoly n F) : *)
(* reflect Logic.True true. *)

Definition is_invariant n (s : {SAset F^n}) (p : mpoly.mpoly n F) : bool :=
  is_cst (sampoly p) s.

Definition cst_sign (n : nat) (p : mpoly n F) (s : {SAset F ^ n}) : bool := 
  is_cst (SAcomp (sampoly p) sign) s.

(* works *)
(* Variable (n : nat). *)
(* Check ({ipoly F[n]}). *)
(* Check ({mpoly F[n]}). *)
(* Check ({ipoly F[n]}^p). *)

Definition partial_eval n (p : {mpoly F[n.+1]}) (t : n.-tuple F) : {poly F} :=
  let aux (i : 'I_n.+1) := 
    match (unlift ord0 i) with 
      | None => 'X
      | Some j => (tnth t j)%:P
    end
  in mmap polyC aux p.

Definition last_size (n : nat) (p : {mpoly F[n.+1]}) := size (muni p).

Definition p_invariant (n : nat) (ps : seq {mpoly F[n]}) (s : {SAset F ^ n}) :=
  all (fun x => is_invariant s x) ps.

Variable (locally_cst : forall (n m : nat), 
                        forall (f : {SAfun F^n -> F^m}), 
                        forall (s : {SAset F ^ n}), bool).

Lemma locally_cstP (n m : nat) (s : {SAset F ^ n}) (f : {SAfun F^n -> F^m}): 
reflect (forall (x : 'rV_n), x \in s -> 
  exists (eps : F), forall (y : 'rV_n), distance x y < eps -> f y = f x) 
  (locally_cst f s).
Admitted.

Lemma prop39 (n m : nat) (s : {SAset F ^ n}) (f : {SAfun F^n -> F^m}) : 
  is_connected s -> locally_cst f s -> is_cst f s.
Proof.
Admitted.

(* not finished *)
Lemma th513 (n : nat) (x0 : 'rV_1) (p q : (mpoly.mpoly n.+1 F)) (s : {SAset F ^ n}) 
  (x : 'rV[F]_n) : 
  is_connected s -> 
  (is_invariant (sa_lift_form s) p) -> 
  (get_cst_value x0 (sa_lift_form s) (sa_lift_point x) (sampoly p) != 0).
Proof.
Admitted.

Definition poly_trunc (R : ringType) (p : {poly R}) := 
  \poly_(i < (size p) - 1) p`_i.

(* Variables (n : nat) (p : {mpoly F[n.+1]})  *)
(*           (truncation : forall (n : nat), {mpoly F[n.+1]} -> {fset {mpoly F[n.+1]}}). *)
(* Check (let q := muni p in (((size q) <= 1)%N || ((msize (lead_coef q)) <= 1)%N)). *)
(* Check (let q := muni p in [fset q]). *)
(* Check (let q := muni p in (mmulti q)). *)
(* Check (let q := muni p in (aux_trunc (mmulti q))). *)
(* Check (let q := muni p in (aux_trunc p)). *)
(* Check (let q := muni p in (mmulti (aux_trunc p))). *)
(* Check (let q := muni p in (truncation (mmulti (aux_trunc p)))). *)

Fixpoint aux_truncation m n  (p : {mpoly F[n.+1]}) : {fset {mpoly F[n.+1]}} :=
  match m with
  | O => fset0
  | m.+1 => let q := muni p in
              if (((size q) <= 1)%N || ((msize (lead_coef q)) <= 1)%N)
                then [fset p]
                else [fset p] `|` (aux_truncation m (mmulti (poly_trunc q)))
end.

Fixpoint truncation (n : nat) (p : {mpoly F[n.+1]}) : {fset {mpoly F[n.+1]}} :=
  let m := (size (muni p)) in
  aux_truncation m p.

(* Check ({realclosure F}). *)

(* Lemma aux_truncationP (m : nat) (n : nat) (q p : {mpoly F[n.+1]}) : *)
(*   let s := behead (aux_truncation m p) in  *)
(*   let r := muni (head q (aux_truncation m p)) in *)
(*   (forall (x : {mpoly F[n.+1]}), x \in s ->  *)
(*     let y := muni x in (1 < size y)%N && (1 < msize (lead_coef y))%N) *)
(*   /\ (((size r) <= 1)%N || ((msize (lead_coef r)) <= 1)%N). *)
  

(*   match aux_truncation m p with *)
(*   | [::] => True *)
(*   | x::s => forall (x : {mpoly F[n.+1]}), x \in s ->  *)
(*     let y := muni x in (1 < size y)%N && (1 < msize (lead_coef y))%N *)
(* end. *)

(*   let s := behead (aux_truncation m p) in *)
(*   forall (x : {mpoly F[n.+1]}), x \in s ->  *)
(*     let y := muni x in (1 < size y)%N && (1 < msize (lead_coef y))%N. *)


(* Lemma truncationP (n : nat) (q p : {mpoly F[n.+1]}) : *)
(*   let r := muni (head q (truncation p)) in  *)
(*     (((size r) <= 1)%N || ((msize (lead_coef r)) <= 1)%N). *)
(* Proof. *)
(* rewrite /=. *)
(* rewrite /truncation. *)
(* Admitted. *)

(* Lemma truncationP2 (n : nat) (q p : {mpoly F[n.+1]}) : *)
(*  let s := behead (truncation p) in  *)
(*     all (fun x => let y := muni x in (1 < size y)%N && (1 < msize (lead_coef y))%N) s. *)
(* Proof. *)

(* Admitted. *)

Definition add_deriv n (s : {fset {mpoly F[n.+1]}}) : {fset {mpoly F[n.+1]}} := 
s `|` [fset p^`M(ord_max) | p in s].

Definition roots_set (p : {poly F}) := seq_fset (rootsR p).

(* Fixpoint to_gring_form (f : qe_rcf.formula F) : GRing.formula F := match f with *)
(*   | qe_rcf.Bool b => GRing.Bool b *)
(*   | qe_rcf.Equal t1 t2 => GRing.Equal t1 t2 *)
(*   | qe_rcf.Lt t1 t2 => GRing.Bool () *)
(*   | qe_rcf.Le t1 t2 => GRing.Bool () *)
(*   | qe_rcf.And f1 f2 => GRing.And (to_gring_form f1) (to_gring_form f2) *)
(*   | qe_rcf.Or f1 f2 => GRing.Or (to_gring_form f1) (to_gring_form f2) *)
(*   | qe_rcf.Implies f1 f2 => GRing.Implies (to_gring_form f1) (to_gring_form f2) *)
(*   | qe_rcf.Not f1 => GRing.Not (to_gring_form f1) *)
(* end.  *)

(* Definition myproj (n : nat) (s : seq (GRing.term F) * seq (GRing.term F)) := to_gring_form (wproj n s). *)

(* Check (@GRing.QEdecFieldMixin F myproj). *)

(* Lemma req1 : GRing.wf_QE_proj myproj. *)
(* Proof. *)
(* move=> i bc /= h. *)
(* apply/andP; split. *)
(* qf_form *)
(* Qed. *)

(* Check (finmempred [pred x | x \in root q]). *)

(* pred_fset *)
(* finmempred *)
(* nthroot *)
(* Check (roots q). *)
(* [seq s*t | s <- iroots p, t <- iroots q] *)
(* Check (finset (root q)). *)

(* Check [pred x | x \in root p]. *)


Variables (n : nat) (p : {mpoly F[n.+1]}) (q : {mpoly F[n]}).
Variable (s1 : {fset {mpoly F[n.+1]}}) (s2 : {fset {mpoly F[n]}}).

(* Check (muni p). *)
(* Check (roots_set (muni p)). *)

Definition aux2 (_ : 'I_0) : F := 0.

Check (@mmap O F F (@idfun F) (fun _ => 0)).

Definition mpoly0 (x : {mpoly F[0]}) : F := (@mmap O F F (@idfun F) (fun _ => 0) x).

Lemma mpoly0K : cancel mpoly0 (@mpolyC O F).
Proof.
move=> x; rewrite /mpoly0.
move: (nvar0_mpolyC x) => nvar0.
rewrite [RHS]nvar0.
apply/eqP; rewrite mpolyC_eq; apply/eqP.
rewrite /mmap {1}[in LHS]nvar0 msuppC.
have [->|/negbTE xN0] := eqVneq x@_0 0; first by rewrite eqxx big_nil.
by rewrite xN0 big_seq1 mmap11 mulr1.
Qed.

Lemma mpolyC0K : cancel (@mpolyC O F) mpoly0.
Proof. by move=> x; rewrite /mpoly0 mmapC. Qed.

Lemma mpoly0_bij : bijective mpoly0.
Proof.
exists (@mpolyC O F).
exact: mpoly0K.
exact: mpolyC0K.
Qed.
Check (map_poly mpoly0).

Definition aux3 (p : {poly {mpoly F[0]}}) : {poly F} := map_poly mpoly0 p.

Definition cad1 (s : {fset {mpoly F[1]}}) := 
  \bigcup_(p <- (enum_fset s)) (roots_set (aux3 (muni p))).

Definition orderr (xs : {fset F}) : seq F := enum_fset xs.

Definition sort_seq (xs : seq F) : seq F := xs.

(* Check (F : rcfType). *)
(* Check (F : numDomainType). *)
(* Check (@ler F). *)

(* Variables (x y : F). *)
(* Variable (u : {fset {SAset F ^ 1}}). *)
(* Check (x < y). *)

(* Check (@path.sort F (@ltr F)). *)
(* Check (rel F). *)
(* Check ([::x]). *)
(* Check [::x; y]. *)

Definition sorted_seq (xs : seq F) := (@path.sort F (@ler F) xs).

Import SET.SetSyntax.

Check (setT : {SAset F^1}).

Fixpoint aux_cells1 (x : F) (xs : seq F) : {fset {SAset F ^ 1}} := 
match xs with
  | [::] => [fset (interval_a_inf x)]
  | y::s => (interval_a_b x y) |` ((singleton y) |` (aux_cells1 y s))
end.

Definition cells1 (xs : {fset F}) : {fset {SAset F ^ 1}} := 
match (sorted_seq (enum_fset xs)) with
  | [::] => [fset setT]
  | x::s => (interval_inf_b x) |` ((singleton x) |` (aux_cells1 x s))
end.

Lemma testpath (T : eqType) (leT : rel T) (a : T) (s : seq T) :
  path.sorted leT (a :: s) -> path.sorted leT s.
Proof. by case: s => // b s; move/andP => [_]. Qed.

(* Lemma auxpath (T : eqType) (leT : rel T) (P : seq T -> Prop) : *)
(*   P [::] -> *)
(*   (forall (a : T) (s : seq T), P s -> path.sorted leT (a :: s) -> P (a :: s)) -> *)
(*   forall (s : seq T), path.sorted leT s -> P s. *)

(* Lemma auxpath (T : eqType) (leT : rel T) (P : seq T -> Prop) :  *)
(*   P [::] -> *)
(*   (forall (a : T) (s : seq T), P s -> path.sorted leT (a :: s) -> P (a :: s)) -> *)
(*   forall (s : seq T), path.sorted leT s -> P s. *)
(* Proof. *)
(* move=> Pnil. *)
(* move=> ih s. *)
(* elim: s => [_ | ]. *)
(* exact: Pnil. *)
(* move=> a s. *)
(* move=> h. *)
(* apply: ih. *)
(* apply: h. *)
(* Qed. *)

(* Lemma auxpath (T : eqType) (leT : rel T) (P : seq T -> Prop) :  *)
(*   P [::] -> forall (x : T) (s : seq T),  *)
(*   -> forall (s : seq T), P (path.sort leT s). *)
(* Proof. *)

(* Qed. *)

Lemma ltn_sorted_uniq_leq (s : seq F) : 
  path.sorted ltr s = uniq s && path.sorted ler s.
Proof.
case: s => //= m s; elim: s m => //= p' s IHs m.
rewrite inE Num.Internals.ltr_def negb_or IHs -!andbA.
case sn: (m \in s); last by rewrite eq_sym ; do !bool_congr.
rewrite andbF.
apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
rewrite eqr_le lenm andbT.
by apply: (allP (@path.order_path_min F ler (@ler_trans F) p' s le_ms)).
Qed.

Lemma non_empty_aux_cells1 (x : F) (xs : seq F) : 
  path.path ltr x xs -> non_empty_cells (aux_cells1 x xs).
Proof.
move: x ; elim: xs => [x _ | x s ih y].
+ rewrite /non_empty_cells ; apply/allP => c.
  rewrite mem_enum_fset in_fset1 ; move/eqP ->.
  apply/negP.
  move/SAsetP/(_ (\row_(i < 1) (x + 1)%R)).
  by rewrite [RHS]inE in_interval mxE -[X in X < _]addr0 ltr_add2l ltr01.
+ move/andP => [lt_yx path_x_s].
  rewrite /non_empty_cells ; apply/allP => c.
  rewrite in_fsetU ; move/orP => [|]; last first.
    rewrite finmap.inE finmap.inE.
    move/orP => [/eqP ->|]; first by rewrite set1_neq0.
    move: (ih x path_x_s) ; rewrite /non_empty_cells.
    by move/allP/(_ c) ; rewrite mem_enum_fset.
  rewrite in_fset1 ; move/eqP ->.
  apply/negP ; move/SAsetP.
  move/(_ (\row_(i < 1) ((x + y) / 2%:R))).
  rewrite in_interval mxE ltr_pdivl_mulr; last by rewrite ltr0n.
  rewrite ltr_pdivr_mulr; last by rewrite ltr0n.
  by rewrite inE mulr2n !mulrDr !mulr1 ltr_add2r ltr_add2l andbb lt_yx.
Qed.

Lemma ltrxSx (x : F) : (x < x + 1)%R.
Proof. by rewrite -[X in X < _]addr0 ltr_add2l ltr01. Qed.

Lemma sing_in_aux_cells (a x : F) (xs : seq F) : 
  path.path ltr x xs -> (singleton a) \in (aux_cells1 x xs) = (a \in xs).
Proof.
move: a x.
elim: xs => [a x _ | b xs ih a x].
rewrite /= finmap.inE in_nil. 
apply/negbTE.
apply/negP.
move/SAsetP.
move/(_ (\row_(i < 1) ((Num.max a x) + 1)%R)).
rewrite !in_interval mxE.
rewrite (ler_lt_trans _ (ltrxSx _)) ; last by rewrite ler_maxr lerr orbT.
apply/negP.
rewrite neqr_lt.
rewrite (ler_lt_trans _ (ltrxSx _)) ?orbT //=.
by rewrite ler_maxr lerr.
rewrite /=.
move/andP => [lt_ya path_ax].
rewrite inE !finmap.inE.
rewrite ih //.
have /negbTE -> : singleton a != interval_a_b x b.
rewrite eqEsubset.
rewrite negb_and.

apply/negP.
(* move/SAsetP. *)


(* move: (@ltr_maxr F x a x). *)
(* rewrite ltr_maxr. *)

(* rewrite in_interval finmap.inE. *)
(* rewrite /=. *)

(* in_interval. *)
Admitted.

Lemma non_empty_cells1 (xs : {fset F}) : non_empty_cells (cells1 xs).
Proof.
rewrite /non_empty_cells ; apply/allP => c.
rewrite /cells1 mem_enum_fset /sorted_seq.
move: (@enum_fset_uniq F xs) 
      (@path.sort_sorted F _ (@ler_total F) (enum_fset xs)).
rewrite -(@path.sort_uniq F ler).
move: (path.sort <=%R (enum_fset xs)) => {xs} s.
case: s => [_ _ | a s /= /andP [ha uniq_s] path_as].
  rewrite in_fset1 ; move/eqP ->.
  rewrite -proper0 ; apply/properP ; split; rewrite ?le0x //.
  exists 0; last exact: notin_set0.
  rewrite /setT.
  by rewrite /setT -sub_SAset1 SAset_topP. (* should be in set.v ? *)
rewrite in_fset1U ?finmap.inE => /orP [/eqP -> | /orP [/eqP -> | h2]]; rewrite ?set1_neq0 //.
  apply/negP ; move/SAsetP/(_ (\row_(i < 1) (a - 1)%R)).
  rewrite in_SAset_bottom in_interval mxE ltr_subl_addr.
  by rewrite -[X in X < _]addr0 ltr_add2l ltr01.
suffices path_as' : path.path <%R a s.
  move: (@non_empty_aux_cells1 a s path_as').
  rewrite /non_empty_cells.
  by move/allP/(_ c) ; rewrite mem_enum_fset => ->.
move: ha uniq_s path_as h2.
case: s => [ // | b s /=].
rewrite in_cons negb_or.
move/andP => [neq_ab a_notin_s].
move/andP => [b_notin_s uniq_s].
move/andP => [leq_ab path_bs].
rewrite ltr_neqAle neq_ab leq_ab /= => _.
rewrite pathE; last exact: ltr_trans.
rewrite ltr_sorted_uniq_ler uniq_s.
apply/andP ; split; first exact: (@path.path_sorted _ _ b _).
apply/allP => x x_in_s.
rewrite ltr_neqAle ; move: b_notin_s x_in_s.
have [-> | Neq_bx] := eqVneq b x ; first by case: (x \in s).
move=> b_notin_s x_in_s ; rewrite Neq_bx /=.
move: path_bs ; rewrite pathE; last exact: ler_trans.
by move => /andP [_ /allP ->].
Qed.

Fact Nfset0 (cT : choiceType )(x : (@fset0 cT)) : false.
Proof. by case x. Qed.

(* Lemma testset (m : nat) (s t : {SAset F ^ m}) (x : 'rV[F]_m) : *)
(*   x \in (setU s t)%O. *)
(* Proof. *)
(* rewrite inE. *)

(* rewrite in_set0. *)
(* Qed. *)

(* Lemma joinU (m : nat) (s t : {fset {SAset F ^ m}}) : *)
(* (\join_(i : s `|` t) val i)%O = fsetU (\join_(i : s) val i)%O *)
(*                                 (\join_(i : t) val i)%O. *)

(* Context {disp : unit}. *)
(* Local Notation blatticeType := (blatticeType disp). *)
(* Context {L : blatticeType}. *)
(* Implicit Types (x y z : L). *)
(* Variables (I : finType) (A B : {set I}) (G : I -> L). *)
(* Check ((\join_(i in A) G i)%O). *)
(* Check ((\join_(i in B) G i)%O). *)
(* Check (join (\join_(i in A) G i)%O (\join_(i in B) G i)%O). *)


(* Lemma joins_setU2 (I : finType) (A B : {set I}) (G : I -> L) : *)
(*   (\join_(i in (finset.setU A B)) G i)%O = (join (\join_(i in A) G i) (\join_(i in B) G i))%O. *)
(* Proof. *)
(* apply/eqP.  *)
(* rewrite eq_le.  *)
(* rewrite leUx. *)
(* rewrite !le_joins. *)
(* rewrite ?andbT. *)
(* apply/joinsP => i. *)
(* rewrite finset.inE; move=> /orP. *)
(* case=> ?. *)
(* rewrite lexU //. *)
(* rewrite join_sup //. *)
(* Admitted. *)

(* Variable (elementType : Type) (eqType_of_elementType : elementType -> eqType) *)
(*          (disp : unit) *)
(*          (set : SET.Semiset.Exports.semisetType eqType_of_elementType disp) *)
(*          (X : elementType) (x : eqType_of_elementType X) *)
(*          (A B : SET.Semiset.sort set X). *)

(* Lemma aux (m : nat) (s t : {fset {SAset F ^ m}}) : *)
(*  s `<=` t -> (\join_(i in fsub s t) val i = \join_(i : s) val i)%O. *)
(* Proof. *)

(* apply: in_it. *)
(* have [|] := altP (val i \in t). *)
(* case: _ / in_it. *)
(* have [|] := boolP (val i \in t). *)


(* rewrite {2}in_it. *)
(* Set Printing All. idtac. *)
(* rewrite in_it. *)

(* case: _ /. *)

(* move: {2}(val i \in t) (erefl (val i \in t)). *)
(* move=> b. *)
(* case: _ /. *)
(* case: _ /. *)

(* move=> in_it. *)
(* case: in_it. *)
(* have [Ex | E'x] := boolP (val i \in t). *)
(* case:  (boolP (val i \in t)). *)
(* case/boolP. : (val i \in t). *)
(* Fail move ->. *)
(* Admit *)

(* if (val i \in t) then (FSetSub (auxh2 i)) else z. *)

Lemma aux (m : nat) (s t : {fset {SAset F ^ m}}) :
 (\join_(i in fsub s t) val i = \join_(i : s `&` t) val i)%O.
Proof.
case : (fset_0Vmem (s `&` t)) => [sintert_empty | [dv indef]].
  rewrite sintert_empty big_fset0 big_pred0 // => x; apply/negP => abs.
  suff : val x \in s `&` t by rewrite sintert_empty finmap.inE.
  by rewrite finmap.inE; apply/andP;split;[apply/valP | move: abs; rewrite finmap.inE].
have def := [` indef].
have hP : forall (x : s), x \in fsub s t -> val x \in s `&` t.
  by move => x; rewrite !finmap.inE => ->; rewrite andbT; apply/valP.
have hP' : forall (x : s `&` t), val x \in s.
  move=> x; have : val x \in s `&` t by apply/valP.
  by rewrite finmap.inE; case/andP.
set h := fun x => [` hP' x].
have bijon : {on (fsub s t), bijective h}.
  exists (fun x : s => insubd def (val x)).
    move => x xfsubst.
    by apply/val_inj; rewrite val_insubd (hP (h x) xfsubst).
  move => x xfsubst; rewrite /h; apply/val_inj.
  by rewrite -[LHS]/(val (insubd _ _)) val_insubd (hP _ xfsubst).
rewrite (reindex h bijon) /=.
apply: eq_big => // x; rewrite -[LHS]/(h x \in fsub s t).
  rewrite finmap.inE /h /=.
have : val x \in s `&` t by apply/valP.
by rewrite finmap.inE; case/andP.
Qed. 

Lemma joinU (m : nat) (s t : {fset {SAset F ^ m}}) :
  (\join_(i : s `|` t) val i)%O = join (\join_(i : s) val i)%O
                                       (\join_(i : t) val i)%O.
Proof.
move: (@joins_setU _ [blatticeType of {SAset F ^ m}] (fset_sub_finType (s `|` t))
       (fsub (s `|` t) s) (fsub (s `|` t) t) (fun x => fsval x)).
rewrite !aux fsetUKC fsetUK => <-.
apply: eq_big => [i|i _ //].
by rewrite finset.in_setU !in_fsub -in_fsetU -in_fsub fsubT in_setT.
Qed.

Definition auxp m (s : {fset {SAset F ^ m}}) y : (pred (fset_sub_type s)) 
  := (fun (z : s) => y \in (val z)).

(* Lemma in_join (m : nat) (s : {fset {SAset F ^ m}}) (y : 'rV[F]_m) : *)
(*   [exists x, x \in (@auxp _ s y)] = (y \in (\join_(i : s) val i)%O). *)
(* Proof. *)
(* Admitted. *)

Lemma aux_covers1 (x : F) (xs : seq F) : 
  path.path ltr x xs -> 
  (\big[setU/set0]_(i : (aux_cells1 x xs )) val i) = (interval_a_inf x).
Proof.
rewrite /aux_cells1 ; move: x ; elim: xs => [x _ | a xs ih x]. 
  by rewrite big_fset1.
move/andP => [lt_xa path_a_xs].
rewrite !joinU !big_fset1 ; apply/setP => y.
rewrite inE in_setU ih // !in_interval eq_sym -ler_eqVlt.
have [leq_ay|] := boolP (a <= y 0 0); first by rewrite orbT (ltr_le_trans lt_xa).
by rewrite -ltrNge => -> ; rewrite andbT orbF.
Qed.

Lemma covers1 (xs : {fset F}) : 
  covers (cells1 xs) setT.
Proof.
rewrite /covers le1x ; apply/SAsetP => x.
rewrite /setT -[RHS]sub_SAset1 SAset_topP /cells1 /sorted_seq.
move: (@path.sort_sorted F _ (@ler_total F) (enum_fset xs)).
move: (@enum_fset_uniq F xs).
rewrite -(@path.sort_uniq F ler).
move: (path.sort <=%R (enum_fset xs)) => {xs} s uniq_s sorted_s.
have sorted_s': path.sorted <%R s by rewrite ltr_sorted_uniq_ler uniq_s sorted_s.
move: uniq_s sorted_s sorted_s'.
case: s => [_ _ _ | a s /=].
by rewrite big_fset1 /setT -sub_SAset1 SAset_topP. (* should be in set.v ? *)
move/andP => [a_notin_s uniq_s] path_as path_as'.
rewrite !joinU inE in_setU !big_fset1 aux_covers1 // !in_interval.
by rewrite eq_sym -ler_eqVlt lerNgt orbN.
Qed.

Lemma aux_disjoint1 x s : 
  path.path ltr x s -> disjoint_cells (aux_cells1 x s).
Proof.
rewrite /aux_cells1.
rewrite /disjoint_cells.
rewrite /=.
move=> path_xs.
apply/allP.
rewrite /=.
move=> [u v].
move/allpairsP.
rewrite /=.
move=> /= [[u' v']].
rewrite /=.
move=> [].
move=> h1 h2.
move/eqP.
rewrite -pair_eqE /=.
move/andP => [/eqP equ /eqP eqv]. 
apply/implyP.
(* move=> Neq_uv. *)
move: h1 h2.
rewrite equ eqv.
move=> {equ} {eqv} {u} {v}.
move: u' v' x path_xs.
elim: s.
move=> u v x.
rewrite !finmap.inE.
move=> path_as.
move=> /eqP hu.
move=> /eqP hv.
by rewrite hu hv eqxx.
move=> a l ih u v x.
rewrite /=.
move/andP => [lt_xa path_al].
rewrite !finmap.inE.
move/or3P => [/eqP hu1|/eqP hu2|hu3] ; move/or3P => [/eqP hv1|/eqP hv2|hv3].
+ by rewrite hu1 hv1 eqxx.
+ move=> _ ; rewrite hu1 hv2.
  apply/eqP/setP => i.
  rewrite in_set0 in_setI !in_interval.
  apply/negbTE ; rewrite [_ < a]ltr_def andbAC eq_sym.
  by case: (_ == _) ; rewrite ?andbF. 
+ admit.
+ move=> _ ; rewrite hu2 hv1.
  apply/eqP/setP => i.
  rewrite in_set0 in_setI !in_interval.
  apply/negbTE.
  rewrite andbCA.
  rewrite [_ < a]ltr_def eq_sym.
  by case: (_ == _) ; rewrite ?andbF.
+ by rewrite hu2 hv2 eqxx.
+ admit.
+ admit.
+ apply: (@ih _ _ _ path_al) => //.
  rewrite hv2.
  rewrite //=.
+ admit.
Admitted.

(* by apply: (@ih _ _ _ path_al). *)


(* rewrite -andbA. *)

(*   rewrite ltr_def. *)
(*   case: (_ == _) ; rewrite ?andbF. *)
(*   rewrite !andbA. *)
(*   rewrite ltr_def. *)
(*   apply/negbTE ; rewrite ltr_def andbAC eq_sym. *)
(*   by case: (_ == _) ; rewrite ?andbF. *)


(*   rewrite andbA. *)
  
(*   rewrite negb_and. *)
(*   apply/orP. *)
  
(*   rewrite andbC. *)
    
(*   move/andP. *)
(* + *)
(* + *)
(* + *)
(* + *)


(* move/orP => [/eqP ->|] ; move/orP => [/eqP ->|]. *)
(* by rewrite eqxx. *)

(* rewrite inE. *)


(* elim: s. *)
(* move=> /= [u v]. *)
(* rewrite /=. *)
(* move/allpairsP. *)
(* rewrite finmap.inE. *)
(* move=> [/eqP -> /eqP ->]. *)
(* move/eqP. *)
(* rewrite -pair_eqE /=. *)
(* move/andP => [/eqP -> /eqP ->]. *)
(* by rewrite eqxx. *)

(* move: x. *)
(* elim: s => /= [x|x l ih]. *)
(* apply/allP => /= [[u v]]. *)

(* move=> [[u' v'] /= ]. *)
(* rewrite !finmap.inE. *)
(* move=> [/eqP -> /eqP ->]. *)
(* move/eqP. *)
(* rewrite -pair_eqE /=. *)
(* move/andP => [/eqP -> /eqP ->]. *)
(* by rewrite eqxx. *)
(* move=> a. *)
(* rewrite /=. *)

(* Qed. *)


Lemma disjoint1 (xs : {fset F}) : disjoint_cells (cells1 xs).
Proof.
rewrite /cells1 /sorted_seq.
move: (@path.sort_sorted F _ (@ler_total F) (enum_fset xs)).
move: (@enum_fset_uniq F xs).
rewrite -(@path.sort_uniq F ler).
rewrite /=.
move: (path.sort <=%R (enum_fset xs)) => {xs} s uniq_s sorted_s.
have sorted_s': path.sorted <%R s by rewrite ltr_sorted_uniq_ler uniq_s sorted_s.
move: uniq_s sorted_s sorted_s'.
case: s => [_ _ _ | a s /=].
rewrite /disjoint_cells.
rewrite /=.
apply/allP.
move=> /= x /=.
move/allpairsP.
rewrite /=.
move=> [[u v]] /= [].
rewrite !finmap.inE.
move/eqP -> ; move/eqP -> => ->.
by rewrite eqxx /=.
move=> b s' /=.
rewrite disjoint_cellsP; last first.
rewrite !finmap.inE.
rewrite negb_or.
admit.
rewrite disjoint_cellsP; last first.
admit.
move=> path_as.
rewrite aux_disjoint1 //.
rewrite andbT.
apply/andP ; split.


(* rewrite /=. *)
(* Check (interval_inf_b a) : {SAset F ^ 1}. *)
(* Check (aux_cells1 a s). *)
(* move/allP. *)


(* rewrite /disjoint_cells. *)
(* apply/allP. *)

(* move: (@path.sort_sorted F _ (@ler_total F) (enum_fset xs)). *)
(* move: (@enum_fset_uniq F xs). *)
(* rewrite -(@path.sort_uniq F ler). *)
(* move: (path.sort <=%R (enum_fset xs)) => {xs} s uniq_s sorted_s. *)
(* rewrite -(@path.sort_uniq F ler). *)
(* rewrite /=. *)
(* apply/allP. *)
(* move=> /= [x y] /=. *)
(* move/allpairsP. *)
(* rewrite /=. *)
(* move=> [[u v] /= [hu hv]]. *)
(* move=> [[u v] /= ]. *)
(* rewrite mem *)
(* move=> [hu hv]. *)
(* move/eqP. *)
(* rewrite -pair_eqE /=. *)
(* move/andP => [/eqP eq_xu /eqP eq_yv]. *)
(* apply/implyP. *)
(* move=> Neq_xy. *)

(* rewrite /=. *)
(* exists (x, y). *)
(* rewrite mem_map. *)
(* move/mapP. *)
(* rewrite in_map. *)
Admitted.


(* Variable (xs : {fset F}). *)

(* Definition cs := cells1 xs. *)

(* Lemma csP : (non_empty_cells cs) && (disjoint_cells cs) *)
(*                               && (@covers 1 cs (setT )) *)
(*                               && (connected_cells cs) *)
(*                               && (cylindric cs). *)
(* Proof. *)
(* rewrite -!andbA; apply/and5P; split. *)
(* + exact: non_empty_cells1. *)
(* + exact:  *)
(* + *)
(* + *)
(* + *)
(* apply/andP. *)
(* split. *)
(* apply/and5P. *)
(* apply/and5P. *)
(* Qed. *)

(* Check (MkCAD (non_empty_cells1 xs)). *)


End CAD.

Definition elimination (n : nat) (s : {fset {mpoly F[n.+2]}}) 
                                                      : {fset {mpoly F[n.+1]}} :=
let s' := s `|` [fset p^`M(ord_max) | p in s] in
let ps :=
(\bigcup_(p <- (enum_fset s'))
  [fset (subresultant j (muni x) ((muni x)^`()))
    | x in truncation p, j in mnfset O (size (muni x)).-2])
`|`
(\bigcup_(p <- (enum_fset (s' `*` s')) | (p.1 != p.2)%PAIR)
  [fset (subresultant j (muni (xy.1)) (muni (xy.2)))%PAIR
    | xy in ((truncation (p.1)%PAIR) `*` (truncation (p.2)%PAIR)),
      j in mnfset O (size (muni xy.2))%PAIR.-1
    & ((size (muni (xy.2)%PAIR)) < (size (muni (xy.1)%PAIR)))%N])
`|`
(\bigcup_(p <- (enum_fset (s' `*` s')) | (p.1 != p.2)%PAIR)
  [fset (subresultant j (muni (xy.2)) (muni ((mwiden (lead_coef (muni xy.2))) * xy.1 - (mwiden (lead_coef (muni xy.1))) * xy.2)))%PAIR
    | xy in ((truncation (p.1)%PAIR) `*` (truncation (p.2)%PAIR)),
      j in mnfset O (size (muni xy.2))%PAIR.-1
    & ((size (muni (xy.2)%PAIR)) == (size (muni (xy.1)%PAIR)))%N])
`|`
(\bigcup_(p <- (enum_fset s'))
[fset (lead_coef (muni p)) | x in truncation p])
in [fset x | x in ps & (1 < size (muni x))%N].

(* Fixpoint cylindrifying (n : nat) (i : 'I_n) (s : {fset {mpoly F[n.+2]}}) :  *)
(* {fset {mpoly F[(n - i).+2]}} :=  *)
(* match i as x in {fset {mpoly F[n.+2]}} return {fset {mpoly F[(n - i).+2]}} with *)
(*   | O => s *)
(*   | _ => (elimination s) *)
(* end. *)

(* Fixpoint cylindrifying (i n : nat) (s : {fset {mpoly F[n.+2]}}) :=  *)
(* match i with *)
(*   | O => s *)
(*   | 1 => s *)
(*   | i.+2 => cylindrifying i (elimination s) *)
(* end. *)

(* (* Check (p^`M(ord_max)). *) *)
(* (* Check (q^`M(ord0)). *) *)

(* (* mderiv *) *)
(* (* mderivm *) *)

(* Definition CAD_algo := forall (n : nat), seq (mpoly.mpoly n F) -> CAD_output. *)

(* Fixpoint cad_algo (s : seq (mpoly.mpoly n F)) : CAD_output := match n with *)
(* | 0 => *)
(* | 1 => *)
(* | n.+1 => *)

End SAsetTheory.



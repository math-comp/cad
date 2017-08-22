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
From mathcomp Require Import matrix finmap order set.

From SemiAlgebraic Require Import auxresults semialgebraic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope abstract_set_scope with set.
Local Open Scope abstract_set_scope.

Import GRing.Theory Num.Theory Num.Def.
Import ord.
Import Order.Theory Order.Syntax Order.Def.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope quotient_scope.
Local Open Scope type_scope.

Reserved Notation "'{formula_' n F }"
  (n at level 0, format "'{formula_' n  F }").
Reserved Notation "{ 'SAset' F }"
  (format "{ 'SAset'  F }").
Reserved Notation "{ 'SAfun' T }"
  (format "{ 'SAfun'  T }").

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

Variables (F : rcfType )(n : nat) (is_connected : {SAset F ^ n} -> bool).

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

Definition connected_cells := all is_connected (enum_fset cad).

Definition disjoint_cells :=
 all (fun x => ((x.1 != x.2)%PAIR ==> (((x.1 :&: x.2)%PAIR) == set0))) 
     [seq (a, b) | a <- (enum_fset cad), b <- (enum_fset cad)].

Definition union_cells := \big[setU/set0]_(i <- (enum_fset cad)) i == setT.

Definition projection_cell (k : 'I_n) :=
all (fun x => ((x.1 != x.2)%PAIR ==> (((((rproj k x.1) :&: (rproj k x.2))%PAIR) == set0)
                                      || ((((rproj k x.1) :&: (rproj k x.2))%PAIR) == setT) ))) 
     [seq (a, b) | a <- (enum_fset cad), b <- (enum_fset cad)].

Definition projection_cells := [forall k, projection_cell k].

End AuxPredicates.

Record CAD_output := MkCAD
{
  cells :> {fset {SAset F ^ n}};
  _ : (non_empty_cells cells) && (disjoint_cells cells)
                              && (union_cells cells)
                              && (connected_cells cells)
                              && (projection_cells cells)
}.

Definition CAD_algo := forall (n : nat), seq (mpoly.mpoly n F) -> CAD_output.

Fixpoint cad_algo (s : seq (mpoly.mpoly n F)) : CAD_output := match n with
| 0 =>
| 1 =>
| n.+1 =>

End SASetTheory.

Section CAD.
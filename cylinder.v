From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat bigop tuple fintype finfun path ssralg ssrnum matrix finmap.
Require Import semialgebraic.
(* TODO: the following imports should not be needed after cleanup. *)
From mathcomp Require Import generic_quotient.
Require Import formula.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope type_scope.

Section SApartition.
Variables (R : rcfType) (n : nat).

Definition SAset_disjoint (s1 s2 : {SAset R^n}) :=
  SAset_meet s1 s2 == SAset0 R n.

Definition SAset_trivI (I : {fset {SAset R^n}}) :=
  [forall s1 : I, [forall s2 : I, (val s1 != val s2) ==> SAset_disjoint (val s1) (val s2)]].

Definition SAset_partition (I : {fset {SAset R^n}}) :=
  (SAset0 R n \notin I) && SAset_trivI I && (\big[@SAset_join R n/SAset0 R n]_(s : I) val s == SAset0 R n).

End SApartition.

Definition SAset_cast {R : rcfType} {n m : nat} (s : {SAset R^n}) :
  n = m -> {SAset R^m}.
by move=> <-.
Defined.

Section CylindricalDecomposition.
Variables (R : rcfType) (n : nat).

Fact lift0' {k} (i : 'I_k) : (lift ord0 i = i + 1 :> nat)%N.
Proof. by rewrite lift0 addn1. Qed.

Definition isCylindricalDecomposition (S : forall i : 'I_n.+1, {fset {SAset R^i}}) :=
  (forall i : 'I_n.+1, SAset_partition R i (S i))
  /\ forall (i : 'I_n) (s : S (lift ord_max i)),
    exists m, exists xi : m.-tuple {SAfun R^i -> R^1},
      sorted (@SAfun_lt R i) xi
      /\ forall s' : S (lift ord0 i),
        (exists k : 'I_m, SAset_cast (val s') (lift0' i) == SAset_meet (SAgraph (tnth xi k)) (SAset_prod (SAset_cast (val s) (lift_max i)) (@SAset_top R 1)))
        \/ (exists k : 'I_m, exists km : k.+1 < m,
          forall (x : 'rV[R]_i) (y : 'rV[R]_1),
            (row_mx x y \in SAset_cast (val s') (lift0' i)) = (x \in SAset_cast (val s) (lift_max i)) && (tnth xi k x ord0 ord0 < y ord0 ord0)%R && (y ord0 ord0 < tnth xi (Ordinal km) x ord0 ord0)%R)
        \/ (forall (x : 'rV[R]_i) (y : 'rV[R]_1),
             (row_mx x y \in SAset_cast (val s') (lift0' i)) = (x \in SAset_cast (val s) (lift_max i)) && [forall k : 'I_m, y ord0 ord0 < tnth xi k x ord0 ord0])%R
        \/ (forall (x : 'rV[R]_i) (y : 'rV[R]_1),
             (row_mx x y \in SAset_cast (val s') (lift0' i)) = (x \in SAset_cast (val s) (lift_max i)) && [forall k : 'I_m, tnth xi k x ord0 ord0 < y ord0 ord0])%R.

End CylindricalDecomposition.

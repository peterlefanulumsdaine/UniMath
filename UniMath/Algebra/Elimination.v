(** * Matrices

Gaussian Elimination over integers.

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.


Local Definition R := pr1hSet natcommrig.


Definition gauss_add_row {m n : nat} {mat : Matrix R m n}
  {r1 r2 : ⟦ m ⟧%stn} : (Matrix R m n).
Proof.
  intros i j.
  induction (stn_eq_or_neq i r1).
  - exact (op1 (mat r1 j)  (mat r2 j)). (* Target row *)
  - exact (mat r1 j). (* Regular row (ID)*)
Defined.

Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix R m n)
  (s : R) (r : ⟦ m ⟧%stn): Matrix R m n.
Proof.
  intros i j.
  induction (stn_eq_or_neq i r).
  - exact (s * (mat i j))%rig.
  - exact (mat i j).
Defined.

Definition gauss_switch_row {m n : nat} (mat : Matrix R m n)
  (r1 r2 : ⟦ m ⟧%stn) : Matrix R m n.
Proof.
  intros i j.
  induction (stn_eq_or_neq i r1).
  - exact (mat r2 j).
  - induction (stn_eq_or_neq i r2).
    + exact (mat r1 j).
    + exact (mat i j).
Defined.

(*
Lemma test_row_switch {m n : nat} (mat : Matrix R m n)
  (r1 r2 : ⟦ m ⟧%stn) : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
Proof.
  intros.
Admitted.
*)

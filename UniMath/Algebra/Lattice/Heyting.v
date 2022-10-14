(** * Heyting algebras *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.

Section Def.

  Context {X : hSet} (L : lattice X).
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ∧ y" := (Lmin L x y).

  Definition exponential (x y : X) : UU :=
    ∑ exp_x_y : X, ∏ z : X, z ≤ exp_x_y <-> (z ∧ x) ≤ y.

  Definition make_exponential {x y} (exp_x_y:X) exp_ump : exponential x y :=
    (exp_x_y ,, exp_ump).

  (** An exponential is a binary operation on [X] satisfying this law *)
  Definition exponential_structure : UU :=
    ∏ x y : X, exponential x y.

  Definition exponential_map (exp : exponential_structure) : X -> X -> X :=
    fun x y => pr1 (exp x y).
  Coercion exponential_map : exponential_structure >-> Funclass.

  Definition exponential_is_exponential (exp : exponential_structure) :
    ∏ x y z : X, z ≤ (exponential_map exp x y) <-> (z ∧ x) ≤ y :=
  fun x y => pr2 (exp x y).

End Def.

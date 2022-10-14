(** * Boolean algebras *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Complement.
Require Import UniMath.Algebra.Lattice.Distributive.
Require Import UniMath.Algebra.Lattice.Heyting.

Section Def.

  Context {X : hSet} (L : bounded_lattice X).

  (** The normal "∧", "∨" notation conflicts with that for [hProp], whereas
      "+", "×" conflict with notation for types. *)
  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ⊗ y" := (Lmin L x y).
  Local Notation "x ⊕ y" := (Lmax L x y).
  Local Notation "⊤" := (Ltop L).
  Local Notation "⊥" := (Lbot L).

  (** While complements are not unique in arbitrary lattices, they are in the
      distributive case. Therefore, Boolean algebra structure is a proposition. *)
  Definition is_boolean : hProp.
  Proof.
    use make_hProp.
    - refine (∑ is_distr : is_distributive L, _).
      use make_hProp.
      + exact (complemented_structure L).
      + apply impred; intro.
        apply distributive_lattice_complements_are_unique; auto.
    - abstract (apply isaprop_total2).
  Defined.

End Def.

Definition is_distributive_of_is_boolean {X : hSet} {L : bounded_lattice X}
  : is_boolean L -> is_distributive L := pr1.

Definition make_is_boolean {X : hSet} (L : bounded_lattice X) :
  is_distributive L -> complemented_structure L -> is_boolean L.
Proof.
  intros ? ?.
  use tpair.
  - assumption.
  - assumption.
Defined.


Definition boolean_algebra (X : hSet) :=
  ∑ L : bounded_lattice X, is_boolean L.

Section Accessors.
  Context {X : hSet} (B : boolean_algebra X).

  Definition boolean_algebra_lattice  : bounded_lattice X :=
    pr1 B.

  Definition boolean_algebra_is_boolean :
    is_boolean boolean_algebra_lattice := pr2 B.

  Definition boolean_algebra_complement : complemented_structure boolean_algebra_lattice :=
    pr2 (pr2 B).

End Accessors.

Coercion boolean_algebra_lattice : boolean_algebra >-> bounded_lattice.

(** Every Boolean algebra has eponentials (is a Heyting algebra). *)
Section Heyting.

  Context {X : hSet} (L : boolean_algebra X).

  Local Notation "x ≤ y" := (Lle L x y).
  Local Notation "x ∧ y" := (Lmin L x y).
  Local Notation "x ∨ y" := (Lmax L x y).
  Local Notation "¬ x" := (boolean_algebra_complement L x).

  (* TODO: upstream *)
  Lemma Lmax_monot_r {x y:X} (le_x_y : x ≤ y) (z:X) : (x ∧ z) ≤ (y ∧ z).
  Proof.
    cbn in *.
    rewrite <- isassoc_Lmin.
    rewrite (isassoc_Lmin _ x z y).
    rewrite (iscomm_Lmin _ z y).
    rewrite <- isassoc_Lmin, isassoc_Lmin.
    apply maponpaths_12.
    - assumption.
    - apply Lmin_id.
  Qed.

  Lemma lattice_ldistr : isldistr (Lmax L) (Lmin L).
    intros x y z.
    use is_distributive_of_is_boolean.
    use boolean_algebra_is_boolean.
    Proof.

  Defined.
  Lemma boolean_algebra_exponential : exponential_structure L.
  Proof.
    intros x y.
    exists ((¬ x) ∨ y).
    intros z; use make_dirprod; intros H.
    - use istrans_Lle. { exact ((¬ x ∨ y) ∧ x). }
      { apply Lmax_monot_r; assumption. }
      rewrite

    -
  Abort.
End Heyting.

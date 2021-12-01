(**

Direct definition of terminal object together with:

- A proof that the terminal object is a property in a (saturated/univalent) category ([isaprop_Terminal])
- Construction of the terminal object from the empty product ([terminal_from_empty_product])


*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.
Local Open Scope logic.

Section def_terminal.

Context {C : precategory}.

Definition isTerminal (b : C) : UU := ∀ a : C, iscontr_hProp (a --> b).

Definition isTerminal_iscontr {b:C} (b_term : isTerminal b) (a : C)
  : iscontr (a --> b)
:= b_term a.

Definition make_isTerminal (b : C) (H : ∏ (a : C), iscontr (a --> b)) :
  isTerminal b
:= H.

Lemma isaprop_isTerminal (x : C) : isaprop (isTerminal x).
Proof.
  apply propproperty.
Qed.

Definition Terminal : UU := ∑ a, isTerminal a.

Definition TerminalObject (T : Terminal) : C := pr1 T.
Coercion TerminalObject : Terminal >-> ob.

Definition Terminal_property (T : Terminal) : isTerminal T := pr2 T.

Definition TerminalArrow (T : Terminal) (b : C) : b --> T := pr1 (pr2 T b).

Lemma TerminalArrowEq {T : Terminal} {a : C} (f g : a --> T) : f = g.
Proof.
  apply proofirrelevancecontr, (Terminal_property T a).
Qed.

Definition make_Terminal (b : C) (H : isTerminal b) : Terminal.
Proof.
  exists b; exact H.
Defined.

Lemma TerminalArrowUnique {T : Terminal} {a : C} (f : C⟦a,TerminalObject T⟧) :
  f = TerminalArrow T _.
Proof.
  apply TerminalArrowEq.
Defined.

Lemma TerminalEndo_is_identity {T : Terminal} (f : T --> T)
  : f = identity T.
Proof.
  apply TerminalArrowEq.
Qed.

Lemma isiso_from_Terminal_to_Terminal (T T' : Terminal) :
   is_iso (TerminalArrow T T').
Proof.
  apply (is_iso_qinv _ (TerminalArrow T' T)).
  now split; apply TerminalArrowEq.
Defined.

Definition iso_Terminals (T T' : Terminal) : iso T T' :=
  (TerminalArrow T' T,,isiso_from_Terminal_to_Terminal T' T) .

Definition hasTerminal := ishinh Terminal.

End def_terminal.

Arguments Terminal : clear implicits.
Arguments isTerminal : clear implicits.
Arguments TerminalObject {_} _.
Arguments TerminalArrow {_} _ _.
Arguments TerminalArrowUnique {_} _ _ _.
Arguments make_isTerminal {_} _ _ _.
Arguments make_Terminal {_} _ _.

(** * Having a terminal object is a property, in a (saturated/univalent) category *)

Section Terminal_Unique.

Variable C : category.
Hypothesis H : is_univalent C.

Lemma isaprop_Terminal : isaprop (Terminal C).
Proof.
  apply invproofirrelevance.
  intros T T'.
  apply (total2_paths_f (isotoid _ H (iso_Terminals T T')) ).
  apply proofirrelevance. apply isaprop_isTerminal.
Qed.

End Terminal_Unique.


Section Terminal_and_EmptyProd.

  (** Construct Terminal from empty arbitrary product. *)
  Definition terminal_from_empty_product (C : category) :
    Product empty C fromempty -> Terminal C.
  Proof.
    intros X.
    use (make_Terminal (ProductObject _ C X)).
    use make_isTerminal.
    intros a.
    assert (H : ∏ i : empty, C⟦a, fromempty i⟧) by
        (intros i; apply (fromempty i)).
    apply (make_iscontr (ProductArrow _ _ X H)); intros t.
    apply ProductArrowUnique; intros i; apply (fromempty i).
  Defined.

End Terminal_and_EmptyProd.

(* Section Terminal_from_Lims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)
(* Require Import UniMath.CategoryTheory.limits.graphs.limits. *)
(* Require Import UniMath.CategoryTheory.opp_precat. *)

(* Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op"). *)

(* Context {C : precategory}. *)

(* Definition empty_graph : graph. *)
(* Proof. *)
(*   exists empty. *)
(*   exact (λ _ _, empty). *)
(* Defined. *)

(* Definition termDiagram : diagram empty_graph C^op. *)
(* Proof. *)
(* exists fromempty. *)
(* intros u; induction u. *)
(* Defined. *)

(* Definition termCone (c : C) : cone termDiagram c. *)
(* Proof. *)
(* simple refine (make_cone _ _); intro u; induction u. *)
(* Defined. *)

(* Lemma Terminal_from_Lims : Lims C -> Terminal C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ termDiagram); intros cc iscc; destruct cc as [c cc]; simpl in *. *)
(* apply (make_Terminal c); apply make_isTerminal; intros b. *)
(* case (iscc _ (termCone b)); intros f Hf; destruct f as [f fcomm]. *)
(* apply (tpair _ f); intro g. *)
(* simple refine (let X : ∑ x : b --> c, *)
(*                        ∏ v, coconeIn cc v · x = coconeIn (termCone b) v := _ in _). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Terminal_from_Lims. *)

(** * Construction of terminal object in a functor category *)
Section TerminalFunctorCat.

Variables (C D : category) (ID : Terminal D).

Definition Terminal_functor_precat : Terminal [C,D].
Proof.
use make_Terminal.
- use make_functor.
  + use tpair.
    * intros c; apply (TerminalObject ID).
    * simpl; intros a b f; apply (TerminalArrow ID).
  + split.
    * intro a; apply TerminalArrowEq.
    * intros a b c f g; apply TerminalArrowEq.
- intros F.
  use tpair.
  + use make_nat_trans; simpl.
    * intro a; apply TerminalArrow.
    * intros a b f; simpl.
      apply TerminalArrowEq.
  + abstract (intros α; apply (nat_trans_eq D); intro a; apply TerminalArrowEq).
Defined.

End TerminalFunctorCat.

(** Morphisms from the terminal object are monic *)
Section monics_terminal.

Context {C : category} (TC : Terminal C).

Lemma from_terminal_isMonic (a : C) (f : C⟦TC,a⟧) : isMonic f.
Proof.
apply make_isMonic; intros b g h H.
now apply TerminalArrowEq.
Qed.

End monics_terminal.

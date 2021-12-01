(**

Direct definition of initial object together with:

- A proof that initial object is a property in a (saturated/univalent) category ([isaprop_Initial])
- Construction of initial from the empty coproduct ([initial_from_empty_coproduct])
- Initial element in a functor precategory ([Initial_functor_precat])

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
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.
Local Open Scope logic.

Section def_initial.

Context {C : precategory}.

Definition isInitial (a : C) : UU := ∀ b : C, iscontr_hProp (a --> b).

Definition isInitial_iscontr {a:C} (a_init : isInitial a) (b : C)
  : iscontr (a --> b)
:= a_init b.

Definition make_isInitial (b : C) (H : ∏ (a : C), iscontr (b --> a))
 : isInitial b
:= H.

Lemma isaprop_isInitial (x : C) : isaprop (isInitial x).
Proof.
  apply propproperty.
Qed.

Definition Initial : UU := ∑ a, isInitial a.

Definition InitialObject (O : Initial) : C := pr1 O.
Coercion InitialObject : Initial >-> ob.

Definition Initial_property (O : Initial) : isInitial O := pr2 O.

Definition InitialArrow (I : Initial) (b : C) : I --> b := pr1 (pr2 I b).

Lemma InitialArrowEq {I : Initial} {a : C} (f g : I --> a) : f = g.
Proof.
  apply proofirrelevancecontr, (Initial_property I a).
Qed.

Definition make_Initial (a : C) (H : isInitial a) : Initial.
Proof.
  exists a; exact H.
Defined.

Lemma InitialArrowUnique {I : Initial} {a : C} (f : C⟦InitialObject I,a⟧) :
  f = InitialArrow I _.
Proof.
  apply InitialArrowEq.
Defined.

Lemma InitialEndo_is_identity {O : Initial} (f : O --> O)
  : f = identity O.
Proof.
  apply InitialArrowEq.
Qed.

Lemma isiso_from_Initial_to_Initial (O O' : Initial) :
   is_iso (InitialArrow O O').
Proof.
  apply (is_iso_qinv _ (InitialArrow O' O)).
  split; apply InitialArrowEq.
Defined.

Definition iso_Initials (O O' : Initial) : iso O O' :=
   (InitialArrow O O',,isiso_from_Initial_to_Initial O O').

Definition hasInitial : UU := ishinh (Initial).

End def_initial.

Arguments Initial : clear implicits.
Arguments isInitial : clear implicits.
Arguments InitialObject {_} _.
Arguments InitialArrow {_} _ _.
Arguments InitialArrowUnique {_} _ _ _.
Arguments make_isInitial {_} _ _ _.
Arguments make_Initial {_} _ _.


(** * Having an initial object is a property, in a (saturated/univalent) category *)
Section Initial_Unique.

  Variable C : category.
  Hypothesis H : is_univalent C.

Lemma isaprop_Initial : isaprop (Initial C).
Proof.
  apply invproofirrelevance.
  intros O O'.
  apply (total2_paths_f (isotoid _ H (iso_Initials O O')) ).
  apply proofirrelevance. apply isaprop_isInitial.
Qed.

End Initial_Unique.


Section Initial_and_EmptyCoprod.

  (** Construct Initial from empty arbitrary coproduct. *)
  Definition initial_from_empty_coproduct (C : category):
    Coproduct empty C fromempty -> Initial C.
  Proof.
    intros X.
    use (make_Initial (CoproductObject _ _ X)).
    use make_isInitial.
    intros b.
    assert (H : ∏ i : empty, C⟦fromempty i, b⟧) by
        (intros i; apply (fromempty i)).
    apply (make_iscontr (CoproductArrow _ _ X H)); intros t.
    apply CoproductArrowUnique; intros i; apply (fromempty i).
  Defined.

End Initial_and_EmptyCoprod.

(* Section Initial_from_Colims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)

(* Variable C : precategory. *)

(* Definition empty_graph : graph. *)
(* Proof. *)
(*   exists empty. *)
(*   exact (λ _ _, empty). *)
(* Defined. *)

(* Definition initDiagram : diagram empty_graph C. *)
(* Proof. *)
(* exists fromempty. *)
(* intros u; induction u. *)
(* Defined. *)

(* Definition initCocone (b : C) : cocone initDiagram b. *)
(* Proof. *)
(* simple refine (make_cocone _ _); intros u; induction u. *)
(* Defined. *)

(* Lemma Initial_from_Colims : Colims C -> Initial C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ initDiagram); intros cc iscc; destruct cc as [c cc]. *)
(* apply (make_Initial c); apply make_isInitial; intros b. *)
(* case (iscc _ (initCocone b)); intros f Hf; destruct f as [f fcomm]. *)
(* apply (tpair _ f); intro g. *)
(* transparent assert (X : (∑ x : c --> b, ∏ v, *)
(*                        coconeIn cc v · x = coconeIn (initCocone b) v)). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Initial_from_Colims. *)

(** * Construction of initial object in a functor category *)
Section InitialFunctorCat.

Variables (C D : category) (ID : Initial D).

Definition Initial_functor_precat : Initial [C, D].
Proof.
use make_Initial.
- use make_functor.
  + use tpair.
    * intros c; apply (InitialObject ID).
    * simpl; intros a b f; apply (InitialArrow ID).
  + split.
    * intro a; apply InitialArrowEq.
    * intros a b c f g; apply pathsinv0, InitialArrowEq.
- intros F.
  use tpair.
  + use make_nat_trans; simpl.
    * intro a; apply InitialArrow.
    * intros a b f; simpl.
      apply InitialArrowEq.
  + abstract (intros α; apply (nat_trans_eq D); intro a; apply InitialArrowEq).
Defined.

End InitialFunctorCat.

(** Morphisms to the initial object are epis *)
Section epis_initial.

Context {C : precategory} (IC : Initial C).

Lemma to_initial_isEpi (a : C) (f : C⟦a,IC⟧) : isEpi f.
Proof.
apply make_isEpi; intros b g h H.
now apply InitialArrowEq.
Qed.

End epis_initial.

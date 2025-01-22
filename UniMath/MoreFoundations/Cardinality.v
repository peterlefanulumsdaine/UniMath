(*******************************************************************************

  Cardinality

  This file is currently work in progress, but aims to contain:

  - constructions on injections/bijections between sets that underlie standard cardinality results
  - a univalent treatment of cardinality itself, as the set-truncation of the universe of sets

*******************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.MoreFoundations.DecidablePropositions.


(** * Explicit results on injections and bijections *)

(* The Cantor–Schröder–Bernstein theorem requires at least some decidability assumption.  We give it therefore in several versions:
- a “precise” form, assuming the precise decidability instance required;
- a constructive form with stronger but more natural assumptions: decidable images plus WLPO(?)
- the classical form, assuming general LEM instead of any specific instances *)

Section Cantor_Schroeder_Bernstein.

Context {A B : UU} (f : A -> B) (g : B -> A).

Definition csb_decision : UU.
Admitted.

Definition cantor_schroeder_bernstein_precise (f_inj :

End Cantor_Schroeder_Bernstein.

(** * Cardinality proper *)

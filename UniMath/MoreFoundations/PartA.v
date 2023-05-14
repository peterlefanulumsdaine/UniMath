(** This file contain various results that could be upstreamed to Foundations/PartA.v *)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

(** * Generalisations of [maponpaths]

The following are a uniformly-named set of lemmas giving how multi-argument (non-dependent) functions act on paths, generalising [maponpaths].

  The naming convention is that e.g. [maponpaths_135] takes paths in the 1st, 3rd, and 5th arguments, counting _backwards_ from the end.  (The “counting backwards” is so that it doesn’t depend on the total number of arguments the function takes.)

  All are defined in terms of [maponpaths], to allow use of lemmas about it for reasoning about these.

 See below for a note about defining duplicates/special cases of these lemmas downstream. *)

Definition maponpaths_1 {X A : UU} (f : X -> A) {x x'} (e : x = x')
  : f x = f x'
:= maponpaths f e.

Definition maponpaths_2 {Y X A : UU} (f : Y -> X -> A)
    {y y'} (e_y : y = y') x
  : f y x = f y' x
:= maponpaths (fun y => f y x) e_y.

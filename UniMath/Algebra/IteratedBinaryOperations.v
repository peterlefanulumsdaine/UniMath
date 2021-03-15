Require Export UniMath.Combinatorics.Lists.
Require Export UniMath.Combinatorics.FiniteSequences.
Require Export UniMath.Algebra.RigsAndRings.
Require Export UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.MoreFoundations.NegativePropositions.

(** Contents:

- the n-ary operations obtained by iterating (typically associative) binary operations
- generalised associativity for such operations
- interaction with homomorphisms, and generalised distributivity
- generalised commutativity
- connections with cardinality on finite sets
- unordered n-ary operations

*)

Local Open Scope stn.

(* move upstream *)

(* end of move upstream *)

Local Notation "[]" := Lists.nil (at level 0, format "[]").
Local Infix "::" := cons.

(** general associativity for binary operations on types *)

Section BinaryOperations.

  Context {X:UU} (unel:X) (op:binop X).

  (* we use an extra induction step in each of the following definitions so
     we don't end up with superfluous unel factors *)

  Definition iterop_list : list X -> X :=
    foldr1 op unel.

  Definition iterop_fun {n} (x:stn n->X) : X.
  Proof.
    intros.
    induction n as [|n _].
    { exact unel. }
    { induction n as [|n I].
      { exact (x lastelement). }
      { exact (op (I (x ∘ dni lastelement)) (x lastelement)). }}
  Defined.

  Definition iterop_seq : Sequence X -> X.
  Proof.
    intros x.
    exact (iterop_fun x).
  Defined.

  (* since [iterop] have the length-1 case special-cased,
  they don’t definitionally satisfy the expected successor equation in general,
  so we prove that equation as a lemma *)

  Definition iterop_list_step (runax : isrunit op unel) (x:X) (xs:list X) :
    iterop_list (x::xs) = op x (iterop_list xs).
  Proof.
    generalize x; clear x.
    apply (list_ind (λ xs, ∏ x : X, iterop_list (x :: xs) = op x (iterop_list xs))).
    { intro x. simpl. apply pathsinv0,runax. }
    intros y rest IH x.
    reflexivity.
  Defined.

  Definition iterop_fun_step' (lunax : islunit op unel) {m} (xs:stn m -> X) (x:X) :
    iterop_fun (append_vec xs x) = op (iterop_fun xs) x.
  Proof.
    unfold iterop_fun at 1.
    simpl.
    induction m as [|m _].
    - simpl. rewrite append_vec_compute_2. apply pathsinv0. apply lunax.
    - simpl. rewrite append_vec_compute_2.
      apply (maponpaths (λ y, op y x)). apply maponpaths.
      apply append_and_drop_fun.
  Defined.

  Definition iterop_fun_step (lunax : islunit op unel) {m} (x:stn(S m) -> X) :
    iterop_fun x = op (iterop_fun (x ∘ dni lastelement)) (x lastelement).
  Proof.
    intros.
    unfold iterop_fun at 1.
    simpl.
    induction m as [|m _].
    - simpl. apply pathsinv0, lunax.
    - simpl. reflexivity.
  Defined.

  Definition iterop_fun_append (lunax : islunit op unel) {m} (x:stn m -> X) (y:X) :
    iterop_fun (append_vec x y) = op (iterop_fun x) y.
  Proof.
    rewrite (iterop_fun_step lunax).
    rewrite append_vec_compute_2.
    apply (maponpaths (λ x, op (iterop_fun x) y)).
    apply funextfun; intro i.
    unfold funcomp.
    rewrite append_vec_compute_1.
    reflexivity.
  Defined.

  (* we can now define the generalised associativity property for [iterop] *)

  Definition iterop_list_list : list(list X) -> X.
  Proof.
    intros w.
    exact (iterop_list (map iterop_list w)).
  Defined.

  Definition iterop_fun_fun {n} {m:stn n -> nat} : (∏ i (j:stn (m i)), X) -> X.
  Proof.
    intros x.
    exact (iterop_fun (λ i, iterop_fun (x i))).
  Defined.

  Definition iterop_seq_seq : Sequence (Sequence X) -> X.
  Proof.
    intros x.
    exact (iterop_fun_fun (λ i j, x i j)).
  Defined.

  Definition isAssociative_list := ∏ (x:list (list X)), iterop_list (Lists.flatten x) = iterop_list_list x.

  Definition isAssociative_fun :=
    ∏ n (m:stn n -> nat) (x : ∏ i (j:stn (m i)), X), iterop_fun (StandardFiniteSets.flatten' x) = iterop_fun_fun x.

  Definition isAssociative_seq :=
    ∏ (x : Sequence (Sequence X)), iterop_seq (FiniteSequences.flatten x) = iterop_seq_seq x.

  Lemma assoc_fun_to_seq : isAssociative_fun -> isAssociative_seq.
  Proof.
    intros assoc x.
    exact (assoc _ _ (λ i j, x i j)).
  Defined.

  Lemma assoc_seq_to_fun : isAssociative_seq -> isAssociative_fun.
  Proof.
    intros assoc n m x.
    exact (assoc (functionToSequence (λ i, functionToSequence (x i)))).
  Defined.

End BinaryOperations.

(** general associativity for monoids *)

Section Monoids.

  Local Open Scope multmonoid.

  Context {M:monoid}.

  Let oo := @op M.

  Let uu := unel M.

  Definition iterop_fun_mon {n} (x:stn n->M) : M := iterop_fun uu oo x.

  Definition iterop_list_mon : list M -> M := iterop_list uu oo.

  Definition iterop_seq_mon : Sequence M -> M := iterop_seq uu oo.

  Definition iterop_seq_seq_mon : Sequence (Sequence M) -> M := iterop_seq_seq uu oo.

  Definition iterop_list_list_mon : list (list M) -> M := iterop_list_list uu oo.

  Definition isAssociative_list_mon := isAssociative_list uu oo.

  Definition isAssociative_fun_mon := isAssociative_fun uu oo.

  Definition isAssociative_seq_mon := isAssociative_seq uu oo.

  (* some rewriting rules *)

  Lemma iterop_seq_mon_len1 (x : stn 1 -> M) :
    iterop_seq_mon (functionToSequence x) = x lastelement.
  Proof.
    reflexivity.
  Defined.

  Lemma iterop_seq_mon_step {n} (x:stn (S n) -> M) :
    iterop_seq_mon (S n,,x) = iterop_seq_mon (n,,x ∘ dni lastelement) * x lastelement.
  Proof.
    intros. induction n as [|n _].
    - cbn. apply pathsinv0, lunax.
    - reflexivity.
  Defined.

  Lemma iterop_list_mon_nil : iterop_list_mon [] = 1.
  Proof.
    reflexivity.
  Defined.

  Lemma iterop_list_mon_step (x:M) (xs:list M) :
    iterop_list_mon (x::xs) = x * iterop_list_mon xs.
  Proof.
    apply iterop_list_step. apply runax.
  Defined.

  Lemma iterop_list_mon_singleton (x : M) : iterop_list_mon (x::[]) = x.
  Proof.
    reflexivity.
  Defined.

  Lemma iterop_fun_mon_step {n} (x : stn(S n) -> M) :
    iterop_fun_mon x = (iterop_fun_mon (x ∘ dni lastelement)) * (x lastelement).
  Proof.
    apply iterop_fun_step, lunax.
  Defined.

  Lemma iterop_fun_mon_append {n} (x : stn n -> M) (y:M) :
    iterop_fun_mon (append_vec x y) = (iterop_fun_mon x) * y.
  Proof.
    apply iterop_fun_append, lunax.
  Defined.

  Local Lemma iterop_seq_mon_append (x:Sequence M) (m:M) :
    iterop_seq_mon (append x m) = iterop_seq_mon x * m.
  Proof.
     revert x m.
     intros [n x] ?. unfold append. rewrite iterop_seq_mon_step.
     rewrite append_vec_compute_2.
     apply (maponpaths (λ a, a * m)).
     apply (maponpaths (λ x, iterop_seq_mon (n,,x))).
     apply funextfun; intros [i b]; simpl.
     unfold funcomp.
     now rewrite append_vec_compute_1.
  Defined.

  Local Lemma iterop_seq_seq_mon_step {n} (x:stn (S n) -> Sequence M) :
    iterop_seq_seq_mon (S n,,x) = iterop_seq_seq_mon (n,,x ∘ dni lastelement) * iterop_seq_mon (x lastelement).
  Proof.
    intros.
    induction n as [|n _].
    - simpl. apply pathsinv0,lunax.
    - reflexivity.
  Defined.

  Lemma iterop_seq_mon_homot {n} (x y : stn n -> M) :
    x ~ y -> iterop_seq_mon(n,,x) = iterop_seq_mon(n,,y).
  Proof.
    revert x y. induction n as [|n N].
    - reflexivity.
    - intros x y h. rewrite 2 iterop_seq_mon_step.
      apply two_arg_paths.
      + apply N. apply funhomot. exact h.
      + apply h.
  Defined.

End Monoids.

(** The general associativity theorem. *)
Section Associativity_Theorem.

Local Open Scope multmonoid.

Lemma iterop_list_mon_concatenate {M : monoid} (l s : list M) :
  iterop_list_mon (Lists.concatenate l s) = iterop_list_mon l * iterop_list_mon s.
Proof.
  revert l. apply list_ind.
  - apply pathsinv0, lunax.
  - intros x xs J. rewrite Lists.concatenateStep.
    unfold iterop_list_mon.
    rewrite 2 (iterop_list_step _ _ (runax M)).
    rewrite assocax. apply maponpaths. exact J.
Defined.

Theorem associativityOfProducts_list (M:monoid) : isAssociative_list (unel M) (@op M).
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  unfold isAssociative_list.
  apply list_ind.
  - simpl. reflexivity.
  - intros x xs I. simpl in I.
    rewrite Lists.flattenStep. refine (iterop_list_mon_concatenate _ _ @ _).
    unfold iterop_list_list. rewrite mapStep.
    rewrite (iterop_list_step _ _ (runax M)).
    + apply (maponpaths (λ x, _ * x)). exact I.
Defined.

Theorem associativityOfProducts_seq (M:monoid) : isAssociative_seq (unel M) (@op M).
Proof.
  (** This proof comes from the Associativity theorem, % \cite[section 1.3, Theorem 1, page 4]{BourbakiAlgebraI}. \par % *)
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  unfold isAssociative_seq; intros. induction x as [n x].
  induction n as [|n IHn].
  { reflexivity. }
  change (flatten _) with (flatten ((n,,x): NonemptySequence _)).
  rewrite flattenStep.
  change (lastValue _) with (x lastelement).
  unfold iterop_seq_seq. simpl.
  unfold iterop_fun_fun.
  rewrite (iterop_fun_step _ _ (lunax M)).
  generalize (x lastelement) as z; intro z.
  unfold iterop_seq.
  induction z as [m z].
  induction m as [|m IHm].
  { simpl. rewrite runax.
    simple refine (_ @ IHn (x ∘ dni lastelement)).
    rewrite concatenate'_r0.
    now apply (two_arg_paths_b (natplusr0 (stnsum (length ∘ (x ∘ dni lastelement))))). }
  change (length (S m,, z)) with (S m). change (sequenceToFunction (S m,,z)) with z.
  rewrite (iterop_fun_step _ _ (lunax M)). rewrite concatenateStep.
  generalize (z lastelement) as w; intros.
  rewrite <- assocax. unfold append.
  Opaque iterop_fun. simpl. Transparent iterop_fun.
  rewrite (iterop_fun_append _ _ (lunax M)).
  apply (maponpaths (λ u, u*w)). simpl in IHm. apply IHm.
Defined.

Corollary associativityOfProducts' {M:monoid} {n} (f:stn n -> nat) (x:stn (stnsum f) -> M) :
  iterop_seq_mon (stnsum f,,x) = iterop_seq_seq_mon (partition f x).
Proof.
  intros. refine (_ @ associativityOfProducts_seq M (partition f x)).
  assert (L := flatten_partition f x). apply pathsinv0. exact (iterop_seq_mon_homot _ _ L).
Defined.

End Associativity_Theorem.

(** interaction with homomorphisms and distributivity *)
(* currently developed only for [interop_fun], not yet [_list] or [_seq] *)

Section Homomorphisms.

  Local Open Scope multmonoid.

  Context {X Y : monoid}.

  (* this result doesn’t use associativity, so could be directly generalised
     to [iterop_fun] instead of [iterop_fun_mon] if ever needed *)
  Definition monoidfun_iterop_fun (f : monoidfun X Y) {n} (a : ⟦n⟧ -> X)
    : f (iterop_fun_mon a) = iterop_fun_mon (fun i => f (a i)).
  Proof.
    induction n as [ | n' IH ].
    { apply monoidfununel. }
    repeat rewrite iterop_fun_mon_step.
    rewrite monoidfunmul.
    apply (maponpaths (fun x => x * _)), IH.
  Defined.

  Definition ismonoidfun_iterop_fun
      (f : X -> Y) (H_f : ismonoidfun f)
      {n} (a : ⟦n⟧ -> X)
    : f (iterop_fun_mon a) = iterop_fun_mon (fun i => f (a i)).
  Proof.
    apply (monoidfun_iterop_fun (monoidfunconstr H_f)).
  Defined.

End Homomorphisms.

Section Distributivity.

  Local Open Scope rig_scope.

  Context {A : rig}.

  (* this result doesn’t use the full rig structure, in particular not commutativty of addition; so could be generalised to any distributive pair of operations (in the sense assuming the unit condition [a * 0 = 0], not just [a * (b + c) = a * b + a * c]) *)

  Definition iter_add_rig {n} (a : ⟦n⟧ -> A) : A
    := @iterop_fun_mon (rigaddabmonoid A) _ a.

  Definition iter_add_ldistr (a : A) {n} (b : ⟦n⟧ -> A)
    : a * (iter_add_rig b) = iter_add_rig (fun i => a * b i).
  Proof.
    use (@ismonoidfun_iterop_fun (rigaddabmonoid A) (rigaddabmonoid A) (fun x => a * x)).
    (* TODO: abstract the following as e.g. [ismonoidfun_riglmult]? *)
    split.
    - intros ? ?; apply rigldistr.
    - apply rigmultx0.
  Defined.

  Definition iter_add_rdistr {n} (a : ⟦n⟧ -> A) (b : A)
    : (iter_add_rig a) * b = iter_add_rig (fun i => a i * b).
  Proof.
    refine (@ismonoidfun_iterop_fun (rigaddabmonoid A) (rigaddabmonoid A) (fun x => x * b) _ _ _).
    (* TODO: abstract the following as e.g. [ismonoidfun_rigrmult]? *)
    split.
    - intros ? ?; apply rigrdistr.
    - apply rigmult0x.
  Defined.

  Definition iter_mult_rig {n} (a : ⟦n⟧ -> A) : A
    := @iterop_fun_mon (rigmultmonoid A) _ a.

End Distributivity.

(** Generalized commutativity (definition) *)
(* currently proven only for [iterop_seq], not yet [_list] or [_fun] *)

Section Commutativity_Properties.

  Definition isCommutative_fun {X:UU} (unel:X) (op:binop X) :=
    ∏ n (x:⟦n⟧ -> X) (f:⟦n⟧≃⟦n⟧),
    iterop_fun unel op (x ∘ f) = iterop_fun unel op x.

  Definition isCommutative_fun_mon (M:monoid) :=
    isCommutative_fun (@unel M) (@op M).

  (* One may want commutativity along an equivalence,
  with the two sizes not obviously equal.

   Perhaps this should be the primary definition? *)
  Definition isCommutative_gen_fun {X:UU} (unel:X) (op:binop X) :=
    ∏ m n (x:⟦n⟧ -> X) (f:⟦m⟧≃⟦n⟧),
    iterop_fun unel op (x ∘ f) = iterop_fun unel op x.

  Definition isCommutative_gen_fun_mon (M:monoid) :=
    isCommutative_gen_fun (@unel M) (@op M).


End Commutativity_Properties.

(** Proof of generalised commutativity *)

Section Commutativity_Theorem.

  Local Open Scope multmonoid_scope.

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Ltac change_lhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T a y) end.
Ltac change_rhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T x a) end.

Lemma commutativityOfProducts_helper {M:abmonoid} {n} (x:stn (S n) -> M) (j:stn (S n)) :
  iterop_seq_mon (S n,,x) = iterop_seq_mon (n,,x ∘ dni j) * x j.
Proof.
  induction j as [j jlt].
  assert (jle := natlthsntoleh _ _ jlt).
  Local Open Scope transport.
  set (f := nil □ j □ S O □ n-j : stn 3 -> nat).
  assert (B : stnsum f = S n).
  { unfold stnsum, f; simpl. repeat unfold append_vec; simpl. rewrite natplusassoc.
    rewrite (natpluscomm 1). rewrite <- natplusassoc.
    rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }
  set (r := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B) ) :
              stn (stnsum f) ≃ stn (S n)).
  set (x' := x ∘ r).
  intermediate_path (iterop_seq_mon (stnsum f,, x')).
  { induction B. apply iterop_seq_mon_homot. intros i. unfold x'.
    unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
  unfold iterop_seq_mon. unfold iterop_seq.
  refine (associativityOfProducts' f x' @ _).
  unfold partition.
  rewrite 3 iterop_seq_seq_mon_step.
  change (iterop_seq_seq_mon (0,,_)) with (unel M); rewrite lunax.
  unfold funcomp at 1 2.
  set (s0 := dni lastelement (dni lastelement (@lastelement 0))).
  unfold funcomp at 1.
  set (s1 := dni lastelement (@lastelement 1)).
  set (s2 := @lastelement 2).
  unfold partition'. unfold inverse_lexicalEnumeration.
  change (f s0) with j; change (f s1) with (S O); change (f s2) with (n-j).
  set (f' := nil □ j □ n-j : stn 2 -> nat).
  assert (B' : stnsum f' = n).
  { unfold stnsum, f'; simpl. repeat unfold append_vec; simpl.
    rewrite natpluscomm. now apply minusplusnmm. }
  set (r' := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B') ) :
              stn (stnsum f') ≃ stn n).
  set (x'' := x ∘ dni (j,, jlt) ∘ r').
  intermediate_path (iterop_seq_mon (stnsum f',, x'') * x (j,, jlt)).
  { assert (L := iterop_seq_mon_len1 (λ j0 : stn 1, x' ((weqstnsum1 f) (s1,, j0)))).
    unfold functionToSequence in L.
    rewrite L. rewrite assocax. refine (transportf (λ k, _*k=_) (commax _ _ _) _).
    rewrite <- assocax.
    apply two_arg_paths.
    { refine (_ @ !associativityOfProducts' f' x'').
      unfold partition.
      rewrite 2 iterop_seq_seq_mon_step.
      change (iterop_seq_seq_mon (0,,_)) with (unel M); rewrite lunax.
      apply two_arg_paths.
      { unfold funcomp. set (s0' := dni lastelement (@lastelement 0)).
        unfold partition'. change (f' s0') with j.
        apply iterop_seq_mon_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply subtypePath_prop.
        change_lhs (stntonat _ i).
        unfold dni. unfold di.
        unfold stntonat.
        match goal with |- context [ match ?x with _ => _ end ]
                        => induction x as [c|c] end.
        { reflexivity. }
        { apply fromempty. assert (P := c : i ≥ j); clear c.
          exact (natlthtonegnatgeh _ _ (stnlt i) P). } }
      { unfold partition'. change (f' lastelement) with (n-j).
        apply iterop_seq_mon_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply subtypePath_prop. change_lhs (j+1+i). unfold dni, di.
        unfold stntonat.
        match goal with |- context [ match ?x with _ => _ end ]
                        => induction x as [c|c] end.
        { apply fromempty. exact (negnatlthplusnmn j i c). }
        { change_rhs (1 + (j + i)). rewrite <- natplusassoc. rewrite (natpluscomm j 1).
          reflexivity. } } }
    unfold x'. unfold funcomp. apply maponpaths.
    apply subtypePath_prop. change (j+0 = j). apply natplusr0. }
  { apply (maponpaths (λ k, k * _)). induction (!B').
    change_rhs (iterop_seq_mon (n,, x ∘ dni (j,, jlt))).
    apply iterop_seq_mon_homot; intros i.
    unfold x''. unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
Qed.

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  iterop_seq_mon (n,,x) = iterop_seq_mon (n,,x∘f).
Proof.
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  intros. induction n as [|n IH].
  - reflexivity.
  - set (i := @lastelement n); set (i' := f i).
    rewrite (iterop_seq_mon_step (x ∘ f)).
    change ((x ∘ f) lastelement) with (x i').
    rewrite (commutativityOfProducts_helper x i').
    apply (maponpaths (λ k, k*_)).
    set (f' := weqoncompl_ne f i (stnneq i) (stnneq i') : stn_compl i ≃ stn_compl i').
    set (g := weqdnicompl i); set (g' := weqdnicompl i').
    apply pathsinv0.
    set (h := (invweq g' ∘ f' ∘ g)%weq).
    assert (L : x ∘ f ∘ dni lastelement ~ x ∘ dni i' ∘ h).
    { intro j. unfold funcomp. apply maponpaths.
      apply (invmaponpathsincl _ ( isinclstntonat _ ) _ _).
      unfold h. rewrite 2 weqcomp_to_funcomp_app. rewrite pr1_invweq.
      induction j as [j J]. unfold g, i, f', g', stntonat.
      rewrite <- (weqdnicompl_compute i').
      unfold pr1compl_ne.
      unfold funcomp.
      rewrite homotweqinvweq.
      rewrite (weqoncompl_ne_compute f i (stnneq i) (stnneq i') _).
      apply maponpaths, maponpaths.
      apply subtypePath_prop.
      unfold stntonat.
      now rewrite weqdnicompl_compute. }
    rewrite (IH (x ∘ dni i') h).
    now apply iterop_seq_mon_homot.
Defined.

End Commutativity_Theorem.

(** An alternate proof of generalised commutativity of iterated sums/products *)
Section Commutativity_Theorem_bis.

  Context {M : abmonoid}.

  (* TODO: once done, pare these down to just what’s reqruied. *)
  Require Import UniMath.Foundations.All.
  Require Import UniMath.MoreFoundations.All.
  Require Import UniMath.Combinatorics.All.

  Local Definition iterop_fun_respects {m n} (e : ⟦m⟧ ≃ ⟦n⟧)
    := ∏ (a : ⟦n⟧ -> M), iterop_fun_mon (a ∘ e) = iterop_fun_mon a.

  Local Definition iterop_fun_respects_idweq {n} : iterop_fun_respects (idweq (⟦n⟧)).
  Proof.
    intros a; reflexivity.
  Defined.

  Local Definition iterop_fun_respects_comp {n1 n2 n3} (e1 : ⟦n1⟧ ≃ ⟦n2⟧) (e2 : ⟦n2⟧ ≃ ⟦n3⟧)
    (H_e1 : iterop_fun_respects e1) (H_e2 : iterop_fun_respects e2)
    : iterop_fun_respects (weqcomp e1 e2).
  Proof.
    intros a. exact (H_e1 (a ∘ e2) @ H_e2 a).
  Defined.

  (* TODO: perhaps upstream, globalise? *)
  Local Definition transpose_stn {n} (i j : ⟦n⟧) : ⟦n⟧ ≃ ⟦n⟧.
  Proof.
    use (weqtranspos i j); apply isisolatedinstn.
  Defined.

  (* TODO: move to tests? *)
  Local Definition transpose_stn_test : @transpose_stn 8 (●3) (●5) (●5) = (●3).
  Proof.
    reflexivity.
  Defined.

  (* TODO: move to tests? *)
  Local Definition transpose_stn_test_2 : @transpose_stn 8 (●3) (●5) (●4) = (●4).
  Proof.
    reflexivity.
  Defined.

  Definition transpose_stn_comp1 {n} (i j : ⟦n⟧)
    : (transpose_stn i j) i = j.
  Proof.
  Admitted.

  Definition transpose_stn_comp2 {n} (i j : ⟦n⟧)
    : (transpose_stn i j) j = i.
  Proof.
  Admitted.

  Definition transpose_stn_comp_rest {n} (i j k : ⟦n⟧)
      (ne_ik : i != k) (ne_jk : j != k)
    : transpose_stn i j k = k.
  Proof.
  Admitted.

  Local Definition stn_weq_extend {n m} : ⟦n⟧≃⟦m⟧ -> ⟦S n⟧≃⟦S m⟧.
  Admitted.

  Local Definition iterop_fun_respects_extend {n m} (e : ⟦n⟧≃⟦m⟧)
     : iterop_fun_respects e -> iterop_fun_respects (stn_weq_extend e).
  Admitted.

  Local Definition secondlast {n} : ⟦S (S n)⟧ := dni lastelement lastelement.

  (* TODO: should be inlined in [move_to_last] below once proven;
  split out for now to allow [move_to_last] to compute while this is admitted. *)
  Local Definition stn_nonlast_todo {n} (i : ⟦S n⟧) (ne_i_l : i != @lastelement n)
    : i < n.
  Admitted.

  (* the permutation moving [i] up to [lastelement] and otherwise order-preserving, *)
  (* defined in a way that facilitates proving [iterop_fun_respects]. *)
  Local Definition move_to_last n (i : ⟦ S n ⟧) : ⟦S n⟧ ≃ ⟦S n⟧.
  Proof.
    induction n as [ | n' IH].
    { apply idweq. }
    destruct (isdeceqstn _ i lastelement) as [ eq_i_l | neq_i_l ].
    { apply idweq. }
    refine (weqcomp _ (transpose_stn lastelement secondlast)).
    apply stn_weq_extend, IH.
    exists i. apply stn_nonlast_todo, neq_i_l.
  Defined.

  Local Definition iterop_fun_respects_move_to_last {n} (i : ⟦S n⟧)
    : iterop_fun_respects (move_to_last n i).
  Proof.
    induction n as [ | n' IH]; cbn.
    { apply iterop_fun_respects_idweq. }
    destruct (isdeceqstn _ i lastelement) as [ eq_i_l | neq_i_l ].
    { apply iterop_fun_respects_idweq. }
    apply iterop_fun_respects_comp.
    { apply iterop_fun_respects_extend, IH. }
    (* The following is the heart of the theorem:
       the actual use of associativity + commutativity. *)
    intros a.
    repeat rewrite iterop_fun_mon_step.
    unfold funcomp. repeat rewrite transpose_stn_comp1, transpose_stn_comp2.
    repeat rewrite assocax.
    eapply pathscomp0. { apply maponpaths, commax. }
    apply (maponpaths (fun x => x * _)%multmonoid).
    apply maponpaths, funextfun; intros j; apply maponpaths.
    use transpose_stn_comp_rest.
    { apply stnneq_to_nopath, dni_neq_i. }
    use (negf (invmaponpathsincl _ _ _ _)). { apply isincldni. }
    apply stnneq_to_nopath, dni_neq_i.
  Defined.

  (* Relevant lemmas: [cutonweq], [invcutonweq], [weqrecomplf] *)

  Theorem iter_add_commutative : isCommutative_gen_fun_mon M.
  Proof.
    intros m n a e.
    induction m as [ | m' IH]; destruct n as [ | n'];
    (* Cases where either [m] or [n] is [0] are trivial: *)
    [ reflexivity | destruct (negweqstn0sn _ e) | destruct (negweqstnsn0 _ e) | ].
    (* For the general case:
      first push the new last element along to the end;
      then (with the last element fixed) permute the rest.

    Concretely, factor the weq [ e : ⟦S m⟧ -> ⟦ S m ⟧] as:
       - [e1 := move_to_last m (e lastelement) ]
       - [e2 := (e1^–1) ; e ]

    We already showed iterop_fun respects [e1]; and [e2] fixes [lastelement], so is respected by induction. *)
  Admitted.

End Commutativity_Theorem_bis.


(** Products/sums over arbitrary finite sets, in commutative monoids *)

  Require Export UniMath.Combinatorics.FiniteSets.
  Require Export UniMath.Foundations.NaturalNumbers.

Section NatCard.

  (** first a toy warm-up with addition in nat, based on cardinalities of standard finite sets *)

  Theorem nat_plus_associativity {n} {m:stn n->nat} (k:∏ (ij : ∑ i, stn (m i)), nat) :
    stnsum (λ i, stnsum (curry k i)) = stnsum (k ∘ lexicalEnumeration m).
  Proof.
    intros. apply weqtoeqstn.
    intermediate_weq (∑ i, stn (stnsum (curry k i))).
    { apply invweq. apply weqstnsum1. }
    intermediate_weq (∑ i j, stn (curry k i j)).
    { apply weqfibtototal; intro i. apply invweq. apply weqstnsum1. }
    intermediate_weq (∑ ij, stn (k ij)).
    { exact (weqtotal2asstol (stn ∘ m) (stn ∘ k)). }
    intermediate_weq (∑ ij, stn (k (lexicalEnumeration m ij))).
    { apply (weqbandf (inverse_lexicalEnumeration m)). intro ij. apply eqweqmap.
      apply (maponpaths stn), (maponpaths k). apply pathsinv0, homotinvweqweq. }
    apply inverse_lexicalEnumeration.
  Defined.

  Corollary nat_plus_associativity' n (m:stn n->nat) (k:∏ i, stn (m i) -> nat) :
    stnsum (λ i, stnsum (k i)) = stnsum (uncurry (Z := λ _,_) k ∘ lexicalEnumeration m).
  Proof. intros. exact (nat_plus_associativity (uncurry k)). Defined.

  Lemma iterop_fun_nat {n:nat} (x:stn n->nat) : iterop_fun 0 add x = stnsum x.
  Proof.
    (* these are different because iterop_fun is careful to not add 0 in the case where n=1 *)
    intros. induction n as [|n I].
    - reflexivity.
    - induction n as [|n _].
      + reflexivity.
      + simple refine (iterop_fun_step 0 add natplusl0 _ @ _ @ ! stnsum_step _).
        apply (maponpaths (λ i, i + x lastelement)). apply I.
  Defined.

  Theorem associativityNat : isAssociative_fun 0 add.
  Proof.
    intros n m x. unfold iterop_fun_fun. apply pathsinv0. rewrite 2 iterop_fun_nat.
    intermediate_path (stnsum (λ i : stn n, stnsum (x i))).
    - apply maponpaths. apply funextfun; intro. apply iterop_fun_nat.
    - now apply nat_plus_associativity'.
  Defined.

  (* A shorter definition: *)
  Definition finsum' {X} (fin : isfinite X) (f : X -> nat) : nat.
  Proof.
    intros. exact (fincard (isfinitetotal2 (stn∘f) fin (λ i, isfinitestn (f i)))).
  Defined.

  (* exercise : show finsum = finsum' *)

End NatCard.

Definition MultipleOperation (X:UU) : UU := UnorderedSequence X -> X.

Section Mult.

  Context {X:UU} (op : MultipleOperation X).

  Definition composeMultipleOperation : UnorderedSequence (UnorderedSequence X) -> X.
  Proof.
    intros s. exact (op (composeUnorderedSequence op s)).
  Defined.

  Definition isAssociativeMultipleOperation := ∏ x, op (flattenUnorderedSequence x) = composeMultipleOperation x.

End Mult.

Definition AssociativeMultipleOperation {X} := ∑ op:MultipleOperation X, isAssociativeMultipleOperation op.

Definition iterop_unoseq_mon {M:abmonoid} : MultipleOperation M.
(* iterate the monoid operation over an unordered finite sequence of elements of M *)
Proof.
  intros m.
  induction m as [J m].
  induction J as [I fin].
  simpl in m.
  unfold isfinite, finstruct in fin.
  simple refine (squash_to_set
                   (setproperty M)
                   (λ (g : finstruct I), iterop_fun_mon (m ∘ g : _ -> M))
                   _
                   fin).
  intros. induction x as [n x]. induction x' as [n' x'].
  assert (p := weqtoeqstn (invweq x' ∘ x)%weq).
  induction p.
  assert (w := commutativityOfProducts (m ∘ x') (invweq x' ∘ x)%weq).
  simple refine (_ @ ! w); clear w. unfold iterop_seq_mon, iterop_fun_mon, iterop_seq.
  apply maponpaths. rewrite weqcomp_to_funcomp. apply funextfun; intro i.
  unfold funcomp. simpl. apply maponpaths. exact (! homotweqinvweq x' (x i)).
Defined.

Definition iterop_unoseq_abgr {G:abgr} : MultipleOperation G.
Proof.
  exact (iterop_unoseq_mon (M:=G)).
Defined.

Definition sum_unoseq_ring {R:ring} : MultipleOperation R.
Proof.
  exact (iterop_unoseq_mon (M:=R)).
Defined.

Definition product_unoseq_ring {R:commring} : MultipleOperation R.
Proof.
  exact (iterop_unoseq_mon (M:=ringmultabmonoid R)).
Defined.

Definition iterop_unoseq_unoseq_mon {M:abmonoid} : UnorderedSequence (UnorderedSequence M) -> M.
Proof.
  intros s. exact (composeMultipleOperation iterop_unoseq_mon s).
Defined.

Definition abmonoidMultipleOperation {M:abmonoid} (op := @iterop_unoseq_mon M) : MultipleOperation M
  := iterop_unoseq_mon.

Theorem isAssociativeMultipleOperation_abmonoid {M:abmonoid}
  : isAssociativeMultipleOperation (@iterop_unoseq_mon M).
Proof.

Abort.

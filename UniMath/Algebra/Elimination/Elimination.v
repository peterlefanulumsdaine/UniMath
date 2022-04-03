 (** * Matrices

Gaussian Elimination over integers.

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Maybe.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.NumberSystems.RationalNumbers.
Require Import UniMath.Tactics.Nat_Tactics.

Require Import UniMath.PAdics.z_mod_p.
Require Import UniMath.PAdics.lemmas.

Require Import UniMath.RealNumbers.Prelim.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.


Section LeadingEntry.

  Context (R: ring).
  Context (F: fld).

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition is_leading_entry {n : nat} (v : Vector F n) (i_1 : ⟦ n ⟧%stn) :=
      (v i_1 != 0%ring) × (∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> (v i_2) = 0%ring).

  Definition is_leading_entry_dual {n : nat} (v : Vector F n) (i_1 : ⟦ n ⟧%stn) :=
      (v i_1 != 0%ring) × (∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2 -> (v i_2) = 0%ring).


  (* Lemma fldchoice0 {X : fld} (e : X) : coprod (e = 0%ring) (e != 0%ring).
  Proof.
    destruct (fldchoice e).
    2: {left; assumption. }
    right.
    unfold multinvpair in m.
    unfold invpair in m.
    destruct m as [m1 m2].
    simpl.
    destruct m2 as [m2 m3].
    apply (@ringneq0andmultlinv X e m1).
    pose (H := nonzeroax).
    change 1%ring with 1%multmonoid in m3.
    assert (eq: (e * m1)%ring = 1%ring).
    { symmetry in m2. apply m3. }
    rewrite eq.
    apply nonzeroax.
  Defined.*)
 
  Definition leading_entry_compute_dual_internal
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧%stn).
  Proof.
    destruct iter as [iter lt].
    induction iter.
    { exact nothing. }
    simpl in lt.
    destruct (fldchoice0 (v (iter,, lt))).
    - refine (IHiter _).
      apply (istransnatlth _ _ _ lt (natgthsnn n)).
    - exact (just ((iter,, lt))).
  Defined.

  Definition leading_entry_compute_internal
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct (leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) iter) as [s | ?].
    - exact (just (dualelement s)).
    - exact nothing.
  Defined.

  Definition leading_entry_compute {n : nat} (v : Vector F n)
     := leading_entry_compute_internal v (n,, natgthsnn n).

  Definition leading_entry_dual_compute {n : nat} (v : Vector F n)
     := leading_entry_compute_dual_internal v (n,, natgthsnn n).
  Proof.

  Lemma leading_entry_compute_eq  {n : nat} (v : Vector F n)
  (i_1 i_2 : ⟦ n ⟧%stn)
  (e_1 : leading_entry_compute v = just i_1)
  (e_2 : leading_entry_dual_compute (λ i : ⟦ n ⟧%stn, v (dualelement i)) = just i_2)
  : i_1 = dualelement i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))
      as [s | contr].
    2: { unfold just, nothing in e_1. contradiction (negpathsii1ii2 i_1 tt). apply pathsinv0. apply e_1. }
    assert (e_3 : (dualelement s) = i_1).
    { apply just_injectivity. exact (e_1). }
    assert (e_4 : s = i_2). { unfold just in e_2. apply ii1_injectivity in e_2. assumption. }
    rewrite <- e_3; rewrite e_4; apply idpath.
  Defined.

  Lemma leading_entry_compute_internal_eq  {n : nat} (v : Vector F n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
    (e_2 : leading_entry_compute_dual_internal (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    apply (leading_entry_compute_eq v); try assumption.
  Defined.

  Lemma leading_entry_compute_impl {n : nat} (v : Vector F n)
  (i_1 : ⟦ n ⟧%stn)
  (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
  : ∑ (i_2 : ⟦ n ⟧%stn),
    leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))
      as [s | contr].
    2: {unfold just, nothing in e_1. contradiction (negpathsii1ii2 (i_1) tt). apply pathsinv0. apply e_1. }
    assert (e_2 : dualelement s = i_1). {apply just_injectivity. apply e_1. }
    apply dualelement_eq in e_2.
    rewrite e_2.
    use tpair. {apply s. }
    simpl. rewrite e_2. reflexivity.
  Defined.

  Definition select_pivot_row_easy_internal {m n : nat} (mat : Matrix F m n)
     (row_sep : ⟦ n ⟧%stn) (k : ⟦ n ⟧%stn) (iter : ⟦ S m ⟧%stn)
    : maybe (∑ i : ⟦ m ⟧%stn, row_sep ≤ i).
  Proof.
    destruct (leading_entry_compute_dual_internal ((col mat k)) iter) as [i | ?].
    2: { exact nothing. }
    destruct (natlthorgeh (pr1 i) row_sep) as [? | gt]. {exact nothing. }
    exact (just (i,, gt )).
  Defined.

  Definition select_pivot_row_easy {m n : nat} (mat : Matrix F m n)
             (row_sep k : ⟦ n ⟧%stn) (iter : ⟦ S m ⟧%stn) : maybe (⟦ m ⟧%stn).
  Proof.
    destruct (select_pivot_row_easy_internal mat row_sep k iter) as [t | ?].
    - apply (just (pr1 t)).
    - exact nothing.
  Defined.

  Lemma leading_entry_compute_dual_internal_correct1
      {n : nat} (vec : Vector F n) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < iter -> ((vec i) != 0%ring) ->
      ((leading_entry_compute_dual_internal vec iter)) != nothing.
  Proof.
    intros i H1 H2.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      apply negnatlthn0 in H1.
      contradiction.
    - rewrite nat_rect_step.
      destruct (fldchoice0 _) as [veq_iter_0 | ?]. 2: {simpl. unfold just. apply negpathsii1ii2. }
      simpl.
      destruct (nat_eq_or_neq i (pr1_)) as [eq' | contr_neq].
      2: { simpl. apply IHpr1_.
           assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
           apply (natleh_neq k_lt_pr1_ contr_neq).
      }
      simpl in H2.
      simpl in eq'.
      apply fromempty.
      assert (stn_eq : (pr1_,, pr2_) = i).
      { apply subtypePath_prop; simpl. rewrite <- eq'. simpl. reflexivity. }
      assert (absurd : vec i = vec (pr1_,, pr2_)).
      { apply maponpaths.
        apply subtypePath_prop.
        apply eq'.
      }
      rewrite absurd in H2.
      rewrite veq_iter_0 in H2.
      contradiction.
  Defined.

  Lemma leading_entry_compute_dual_internal_correct2
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : ((leading_entry_compute_dual_internal v iter)) != nothing )
    : (∑ i : ⟦ n ⟧%stn,
             just i = (leading_entry_compute_dual_internal v iter)
          ×  i < iter × (v i != 0%ring)).
  Proof.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    { simpl; intros; contradiction. }
    rewrite nat_rect_step.
    destruct (fldchoice0 _) as [eq0| neq0].
    - intros H.
      apply IH in H.
      destruct H as [H1 H2].
      destruct H2 as [H2 H3].
      destruct H3 as [H3 H4].
      use tpair.
      {exact H1. }
      use tpair. {assumption. }
      use tpair.
      { apply (istransnatlth _ _ _  H3 (natgthsnn iter) ). }
      simpl; apply H4.
    - intros ?. use tpair.
      { exact (iter ,, p). }
      use tpair. {simpl. reflexivity. }
      use tpair.
      { apply (natgthsnn iter). }
      simpl; intros.
      intros contr_eq0.
      contradiction neq0.
  Defined.

  Definition  leading_entry_compute_dual_internal_correct3
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : ((leading_entry_compute_dual_internal v iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
      destruct (fldchoice0 (v (iter,, p))) as [eq0 | ?].
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice i iter) as [le | eq]. {  apply natlthsntoleh; assumption. }
      + intros H.
        apply IHiter in H; try assumption.
      + intros ?.
        assert (stn_eq : i = (iter,, p)).
        { apply subtypePath_prop. rewrite <- eq. reflexivity. }
        rewrite stn_eq.
        rewrite eq0.
        reflexivity.
  Defined.

  Definition leading_entry_compute_dual_internal_correct4
    {n : nat} (v : Vector F n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ( ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%ring)
   -> (leading_entry_compute_dual_internal v iter) = nothing.
  Proof.
    intros H.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter; try apply idpath.
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p))) as [eq0 | neq0].
    - apply IHiter.
      intros.
      apply H.  {apply (istransnatgth _ _ _ (natgthsnn iter) X ) . }
    - rewrite H in neq0; try contradiction.
      apply (natgthsnn iter).
  Defined.

  (* Additionally we do return the first (in order of iteration) such  non-zero element.
     TODO horrible state of this proof should be put in order. *)
  Definition leading_entry_compute_dual_internal_correct5 {n : nat} (v : Vector F n)
    (iter : ⟦ S n ⟧%stn)
    (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_dual_internal v iter)) = (just i))
    : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i < i' -> i' < iter -> v i' = 0%ring).
  Proof.
    unfold leading_entry_compute_dual_internal.
    assert (ne_nothing : leading_entry_compute_dual_internal v iter != nothing).
    { destruct (maybe_choice (leading_entry_compute_dual_internal v iter)); try assumption.
      rewrite eq; apply negpathsii1ii2. }
    revert ne_nothing.
    destruct iter as [iter p].
    induction iter.
    { simpl. intros. use tpair; contradiction. }
    set (p' :=  (istransnatlth iter n (S n) p (natgthsnn n))).
    pose (@leading_entry_compute_dual_internal n v (S iter,, p) ) as H.
    destruct (@maybe_stn_choice F n H) as [s | ?].
    2: {contradiction. }
    unfold leading_entry_compute_dual_internal.
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p) )) as [z | nz].
    - intros H'.
      pose (first_nonzero := leading_entry_compute_dual_internal_correct2 v (iter,, p') H').
      assert (ne_nothing : leading_entry_compute_dual_internal v (S iter,, p) != nothing).
      { unfold leading_entry_compute_dual_internal.
        rewrite nat_rect_step.
        destruct (fldchoice0 _).
        2: { rewrite z in *. contradiction. }
        apply H'. }
      use tpair.
      { pose (C2 := @leading_entry_compute_dual_internal_correct2 n v (S iter,, p) ne_nothing).
        destruct C2 as [? C2].
        destruct C2 as [eq' C2].
        unfold H in s; destruct s as [s s_eq].
        rewrite eq in eq'.
        apply (just_injectivity) in eq'.
        rewrite <- eq'; apply (pr2 C2).
      }
      simpl; intros i' ? ?.
      destruct (natlehchoice i' iter) as [? | eq']. {assumption. }
      { apply (IHiter p'); try assumption.
        unfold H in eq.
        unfold leading_entry_compute_dual_internal in eq.
        rewrite nat_rect_step in eq.
        destruct (fldchoice0 _) in eq.
        2: {contradiction. }
        unfold leading_entry_compute_dual_internal.
        unfold p'; rewrite eq; reflexivity.
      }
      assert (stn_eq : i' = (iter,, p)).
      { apply subtypePath_prop. rewrite <- eq'; simpl. reflexivity. }
      rewrite stn_eq.
      rewrite z; apply idpath.
    - intros ?; simpl; use tpair.
      { destruct (maybe_choice (leading_entry_compute_dual_internal v (S iter,, p)))
          as [H' | contr_eq].
        2: { rewrite contr_eq in *; unfold just in eq.
             symmetry in eq. apply negpathsii1ii2 in eq.
             contradiction.
        }
        pose (C2 := @leading_entry_compute_dual_internal_correct2 n v (S iter,, p) H').
        destruct C2 as [i' C2].
        destruct C2 as [eq' C2].
        destruct s as [s s_eq].
        rewrite eq in eq'.
        destruct C2 as [? neq].
        apply (just_injectivity) in eq'.
        rewrite <- eq'; apply neq.
      }
      intros ? i'_gt_iter i_le_iter.
            apply natlthtonegnatgeh in i'_gt_iter.
      unfold leading_entry_compute_dual_internal in eq.
      rewrite nat_rect_step in eq.
      destruct (fldchoice0 _) as [? | eq'] in eq.
      {contradiction. }
      apply just_injectivity in eq.
      rewrite <- eq in *.
      contradiction.
  Defined.

  Definition leading_entry_compute_internal_correct1
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn) (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_internal v (n,, natgthsnn n))) = (just i))
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
    pose (H1 := leading_entry_compute_impl v i eq).
    destruct H1 as [i' H1].
    pose (H2 := leading_entry_compute_eq v i i' eq H1).
    unfold leading_entry_compute_internal in eq.
    pose (H := @leading_entry_compute_dual_internal_correct5 n
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n) (dualelement i)).
    destruct (@maybe_stn_choice F n
              (leading_entry_compute_dual_internal
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))) as [? | contr_eq].
    2: { contradiction (@negpathsii1ii2 ((⟦ n ⟧)%stn) unit (i') tt).
         unfold just in H1; rewrite <- H1.
         rewrite contr_eq. reflexivity.  }
    destruct t as [t H3].
    rewrite H2 in *.
    destruct H as [H4 H5].
    { rewrite <- H2. rewrite H2. rewrite dualelement_2x. apply H1. }
    use tpair. { rewrite dualelement_2x in H4. assumption. }
    simpl.
    intros j lt.
    change 0%ring with (@rigunel1 F) in *.
    rewrite <- (H5 (dualelement j)).
    - rewrite dualelement_2x; apply idpath.
    - apply dualelement_lt_comp. (exact lt).
    - exact (pr2 (dualelement j)).
  Defined.

  Lemma leading_entry_compute_internal_correct2
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (eq_nothing : ((leading_entry_compute_internal v iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, (dualelement i) < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert eq_nothing.
    unfold leading_entry_compute_internal, leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) pr2_). }
      destruct (fldchoice0 _) as [eq0 | ?].
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice (dualelement i) (iter)). {  apply natlthsntoleh; assumption. }
      { intros H. apply IHiter in H; try assumption. }
      intros ?.
      rewrite (dualelement_eq i (iter,, pr2_)); try reflexivity; try assumption.
      apply subtypePath_prop; assumption.
  Defined.

  Lemma leading_entry_compute_internal_correct3
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_internal v (n,, natgthsnn n))) = (just i))
    : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i' < i -> v i' = 0%ring).
  Proof.
    use tpair.
    - pose (H1 := @leading_entry_compute_internal_correct1).
      unfold is_leading_entry in H1.
      apply H1. {exact (n,, natgthsnn n). }
      exact eq.
    - simpl.
      intros i' i_gt_i'.
      pose (H2 := @leading_entry_compute_impl _ _ _ eq).
      destruct H2 as [H2 H3].
      pose (H4 := @leading_entry_compute_dual_internal_correct5 _ _ _ _ H3).
      simpl in H4.
      destruct H4 as [H4 H5].
      rewrite <- (H5 (dualelement i')).
      + rewrite dualelement_2x; reflexivity.
      + apply dualelement_lt_comp'.
        rewrite dualelement_2x.
        replace (dualelement H2) with i; try assumption.
        rewrite (@leading_entry_compute_internal_eq _ _ _ H2 eq H3).
        reflexivity.
      + exact (pr2 (dualelement i')).
  Defined.


  (* TODO less duplicate work*)
  Definition leading_entry_compute_internal_correct4
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : (∏ i : ⟦ n ⟧%stn, (dualelement i) < iter -> v i = 0%ring)
   -> (leading_entry_compute_internal v iter) = nothing.
  Proof.
    intros H1.
    unfold leading_entry_compute_internal, leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter; try reflexivity.
    rewrite nat_rect_step.
    destruct (fldchoice0 _) as [eq0 | neq0].
    - apply IHiter; intros H2 lt; apply H1.
      apply (istransnatgth _ _ _ (natgthsnn iter) lt).
    - rewrite H1 in neq0; try contradiction.
      rewrite dualelement_2x.
      apply (natgthsnn iter).
  Defined.

  Lemma leading_entry_compute_deceq {n : nat} (v : Vector F n) (i : ⟦ n ⟧%stn)
    : coprod (leading_entry_compute v = just i) (leading_entry_compute v = just i -> empty).
  Proof.
    destruct (@maybe_stn_choice F n (leading_entry_compute_internal v (n,, natgthsnn n)))
      as [some | none].
    - destruct some as [t ist].
      destruct (stn_eq_or_neq i t) as [eq | neq].
      + left. unfold is_leading_entry.
        rewrite eq.
        assumption.
      + right.
        intros isle.
        destruct (natgthorleh i t) as [gt | leh].
        * pose (H1 := (@leading_entry_compute_internal_correct3 n v i isle)).
          pose (H2 := (@leading_entry_compute_internal_correct3 n v t ist)).
          contradiction (pr1 H2).
          rewrite (pr2 H1 t); try reflexivity; assumption.
        * pose (H1 := (@leading_entry_compute_internal_correct3 n v i isle)).
          pose (H2 := (@leading_entry_compute_internal_correct3 n v t ist)).
          destruct (natlehchoice i t leh) as [lt | contr_eq].
          -- unfold is_leading_entry in isle.
             contradiction (pr1 H1).
             rewrite (pr2 H2 i); try assumption; reflexivity.
          -- unfold stntonat in neq. 
             rewrite ((subtypePath_prop contr_eq)) in neq; contradiction (@isirrefl_natneq _ neq).
    - right.
      intros contr_H.
      pose (H := (@leading_entry_compute_internal_correct3 n v i contr_H)).
      contradiction (pr1 H).
      rewrite ( ((@leading_entry_compute_internal_correct2 n v (n,, natgthsnn n) none)
        i (pr2 (dualelement i))));
      reflexivity.
  Defined.

  Lemma leading_entry_compute_internal_correct5
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (H1 : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i' < i -> v i' = 0%ring))
    : leading_entry_compute v = just i.
  Proof.
    destruct (leading_entry_compute_deceq v i) as [eq | contr_neq]; try assumption.
    pose (H2 := @leading_entry_compute_internal_correct1 n v).
    destruct (@maybe_stn_choice F n (leading_entry_compute v)) as [some | none].
    - contradiction (pr1 H1).
      destruct some as [some_stn some_eq].
      pose (H3 := (@leading_entry_compute_internal_correct3 n v some_stn some_eq)).
      destruct (stn_eq_or_neq i some_stn) as [eq | neq].
      { rewrite eq in contr_neq. exact (fromempty (contr_neq some_eq)). }
      destruct (natgthorleh some_stn i) as [gt | leh].
      + try apply (pr2 H3 i gt).
      + destruct (natlehchoice _ _ leh) as [? | contr_eq].
        { contradiction (pr1 H3). rewrite (pr2 (H1) some_stn); try reflexivity. assumption. }
        rewrite contr_eq in *.
        rewrite (subtypePath_prop contr_eq) in neq.
        contradiction (isirrefl_natneq _ neq).
    - pose (H4 := @leading_entry_compute_internal_correct2 _ _ _ none).
      contradiction (pr1 H1).
      rewrite (H4 _ (pr2 (dualelement i))).
      apply idpath.
  Defined.

  Lemma leading_entry_compute_correct1
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (eq:  (leading_entry_compute v = just i))
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
    use tpair.
    { apply leading_entry_compute_internal_correct3; assumption. }
    simpl.
    apply leading_entry_compute_internal_correct3; assumption.
  Defined.


  Lemma select_pivot_eq_leading_dual
    {m n : nat} (mat : Matrix F m n) (row_sep k : ⟦ n ⟧%stn) (i : stn m) (iter : ⟦ S m ⟧%stn)
    (ne_nothing : (select_pivot_row_easy mat row_sep k iter) = (just i))
    :
    (select_pivot_row_easy mat row_sep k iter) =
    (leading_entry_compute_dual_internal (col mat k) iter).
  Proof.
    unfold select_pivot_row_easy, select_pivot_row_easy_internal in *.
    destruct (leading_entry_compute_dual_internal (col mat k) iter) as [s | ?].
    - destruct (natlthorgeh _ _); simpl; try reflexivity.
      symmetry in ne_nothing. apply negpathsii1ii2 in ne_nothing.
      contradiction.
    - simpl in ne_nothing.
      symmetry in ne_nothing.
      apply negpathsii1ii2 in ne_nothing.
      contradiction.
  Defined.

  Lemma select_pivot_impl_leading_dual
    {m n : nat} (mat : Matrix F m n) (row_sep k : ⟦ n ⟧%stn) (i : stn m) (iter : ⟦ S m ⟧%stn)
    (k_le_i : k ≤ i)
    : (select_pivot_row_easy mat row_sep k iter) != nothing ->
    (leading_entry_compute_dual_internal (col mat k) iter) != nothing.
  Proof.
    unfold select_pivot_row_easy, select_pivot_row_easy_internal in *.
    destruct (leading_entry_compute_dual_internal (col mat k) iter) as [s | ?];
      simpl; try contradiction.
    destruct (natlthorgeh _ _); intros; try contradiction.
    apply negpathsii1ii2.
  Defined.

  Definition select_pivot_row_coprod {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (k : ⟦ n ⟧%stn) :
    coprod ((∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i k) != 0%ring)))
           (∏ i : ⟦ m ⟧%stn, row_sep ≤ i -> mat i k = 0%ring).
  Proof.
    pose (H := (leading_entry_compute_dual_internal_correct2 (col mat k) (m,, natgthsnn m))).
    destruct
      (maybe_choice (leading_entry_compute_dual_internal (col mat k) (m,, natgthsnn m))) as [nnone | none].
    - destruct H as [H1 H2]; try assumption.
      destruct (natlthorgeh H1 row_sep) as [? | gt].
      + apply ii2.
        set (H2' := (pr1 H2)); symmetry in H2'.
        pose (H3 := @leading_entry_compute_dual_internal_correct5 m (col mat k) (m,, natgthsnn m) H1 (H2')).
        destruct H3 as [H3 H4].
        intros i ke_le_i.
        unfold col, transpose, flip in *.
        rewrite H4; try reflexivity; try assumption.
        apply (natlthlehtrans H1 row_sep i); assumption.
        apply (pr2 i).
      + apply ii1.
        use tpair. { apply H1. }
        use tpair. {apply gt. }
        unfold col, transpose, flip in *.
        destruct H2 as [? H2].
        destruct H2 as [? H2].
        destruct (fldchoice0 (mat H1 k)) as [contr_eq | ?].
        { rewrite contr_eq in *. contradiction. }
        assumption.
    - apply ii2.
      pose (H' := @leading_entry_compute_dual_internal_correct3).
      intros.
      rewrite <- (H' m (col mat k) (m,, natgthsnn m) none i); try reflexivity.
      apply (pr2 i).
  Defined.

  Definition select_uncleared_column_compute
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0)
    : maybe ((⟦ m ⟧%stn) × (⟦ n ⟧%stn)).
  Proof.
    destruct (natchoice0 m) as [contr_eq | ngt0].
    {apply fromstn0. rewrite contr_eq. assumption. }
    destruct col_iter as [col_iter lt].
    induction col_iter as [| col_iter IH].
    - exact nothing.
    - destruct (select_pivot_row_coprod mat row_sep (col_iter,, lt)) as [nz | z].
      + exact (just (pr1 nz,, (col_iter,, lt))).
      + simpl in lt;
          exact (IH (istransnatlth _ _ _ lt (natgthsnn n))).
  Defined.

  Local Definition exists_first_uncleared
  {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
  :=
  ((∑ j: ⟦ n ⟧%stn, j < col_iter × (∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i j) != 0%ring)
  ×  ∏ i' : (⟦ m ⟧)%stn, forall (j' : stn n), row_sep ≤ i' -> j' < j -> mat i' j' = 0%ring))).

  Local Definition is_first_uncleared
  {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
  (j : stn n)
  := ((j < col_iter × (∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i j) != 0%ring)
  ×  ∏ i' : (⟦ m ⟧)%stn, forall (j' : stn n), row_sep ≤ i' -> j' < j -> mat i' j' = 0%ring))).

  Local Definition lower_left_zero {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
  := (∏ i : ⟦ m ⟧%stn, row_sep ≤ i
    -> (∏ j : ⟦ n ⟧%stn, j < col_iter -> mat i j = 0%ring)).

  (* Selecting the first (checking leftmost columns first)
     column that has a non-zero entry ≥ the row_sep. *)
  (* TODO rename row sep -> col sep ? *)
  Definition select_uncleared_column_internal
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0)
    : coprod
    (exists_first_uncleared mat row_sep col_iter)
    (lower_left_zero mat row_sep col_iter).
  Proof.
    destruct (natchoice0 m) as [contr_eq | ngt0].
    {apply fromstn0. rewrite contr_eq. assumption. }
    destruct col_iter as [col_iter lt].
    induction col_iter as [| col_iter IH].
    - right; intros ? ? ? contr.
      contradiction (negnatgth0n n contr).
    - assert (lt' : col_iter < S n). { simpl in lt. apply (istransnatlth _ _ _ lt (natgthsnn n)). }
      destruct (IH lt') as [IH_left | IH_right].
      + destruct IH_left as [m' IH_left].
        destruct IH_left as [H1 IH_left].
        destruct IH_left as [H2 H3].
        left.
        use tpair. { apply m'. }
        use tpair. { apply (istransnatlth _ _ _ H1 (natgthsnn col_iter)). }
        use tpair. { simpl in lt. apply H2. } apply H3.
      + destruct (select_pivot_row_coprod mat row_sep (col_iter,, lt)) as [nz | z].
        * left.
          use tpair. {exact (col_iter,, lt). }
          use tpair. { apply (natgthsnn col_iter). }
          use tpair. {apply nz. }
          use tpair. {apply nz. }
          use tpair. {apply nz. }
          simpl; intros i' j' ? ?.
          apply IH_right; try assumption.
        * right.
          intros i rowsep_le_i j j_lt_scoliter.
          destruct (natlehchoice j col_iter) as [? | eq].
          { apply (natlehlthtrans _ _ _ j_lt_scoliter). apply (natgthsnn col_iter). }
          { intros. apply IH_right; try assumption. }
          intros.
          rewrite <- (z i); try assumption.
          apply maponpaths.
          apply subtypePath_prop.
          assumption.
  Defined.

  Definition select_uncleared_column
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (p : n > 0)
    := select_uncleared_column_internal mat row_sep (n,, natgthsnn n) p.

  (*
  (* TODO show there exists a j such as the switch with i_1
     gives there exists a j' satisfying above. *)
  Lemma select_uncleared_column_inv1
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0)
    (piv : stn n)
    (is_piv : is_first_uncleared mat row_sep col_iter piv)
    : (exists_first_uncleared mat row_sep col_iter)
    -> forall (i : stn m),
      (is_first_uncleared (gauss_switch_row mat i piv) i).
     
    : coprod
    (first_uncleared mat row_sep col_iter)
    (∑ j: ⟦ n ⟧%stn, )
    (lower_left_zero mat row_sep col_iter).
    Proof.
    unfold first_uncleared.
    left.
    apply maponpaths.
    apply funextfun; intros j.
    do 2 apply maponpaths.
    apply funextfun; intros i.
    apply maponpaths.


    apply maponpaths.
    
    
    
    apply maponpaths.
    apply maponpaths_4. intros j.
    simpl.
    use tpair.
 *)
  (* Lemma select_pivot_inv1 {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn)
    (j : stn n)
    (p : n > 0)
    (row : stn m)
    (col : stn n)
    (eq_row : (pr1 (select_pivot mat row_sep p)) = row)
    (eq_col : (pr1 (pr2 (select_pivot mat row_sep p))) = col)
    : coprod (leading_entry_compute (mat row) = just col)
      (leading_entry_compute (mat row) = nothing).
  Proof.
    revert eq_row eq_col; set (select := select_pivot mat row_sep p);
      intros eq_row eq_col.
    destruct (natchoice0 m) as [contr_eq | ?].
    { apply fromstn0. rewrite contr_eq; assumption. }
    unfold select_pivot, select_pivot_internal in select.
    destruct (natchoice0 m) as [contr_eq | gt].
    { apply fromstn0. rewrite contr_eq. assumption. }
    rewrite <- eq_row.
    revert eq_row.
    destruct select as [row' select].
    destruct select as [col' select].
    destruct select as [some | none].
    - simpl.
      destruct some as [H1 H2].
      destruct H2 as [H2 H3];
      destruct H3 as [H3 H4].
      intros.
      left.
      apply (@leading_entry_compute_internal_correct5); try assumption.
      rewrite <- eq_col.
      use tpair; try assumption.
      simpl; intros.
      rewrite H4; try reflexivity; try assumption.
    - simpl; simpl in eq_col.
      intros.
      rewrite eq_row.
      destruct (@maybe_stn_choice F n (leading_entry_compute (mat row))) as [t | ?].
      2: { right; assumption. }
      pose (contr_neq := @leading_entry_compute_internal_correct3 n (mat row) (pr1 t) (pr2 t)).
      right.
      apply (@leading_entry_compute_internal_correct4). (* TODO don't dual*)
      intros.
      rewrite (pr2 none); try reflexivity.
      {rewrite <- (pr1 none); rewrite eq_row. apply isreflnatgeh. }
      exact (pr2 i).
  Defined.

  Lemma select_pivot_inv2 {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn)
    (i_1 i_2 : stn m)
    (j_1 j_2 : stn n)
    (le_sep : row_sep ≤ i_1)
    (p : n > 0)
    (H1 : leading_entry_compute (mat i_1) = just j_1)
    (H3 : (pr1 (pr2 (select_pivot mat row_sep p))) = j_2)
    : j_2 ≤ j_1.
  Proof.
    revert H3; set (select := select_pivot mat row_sep p); intros H3.
    destruct (natchoice0 m) as [contr_eq | ?].
    { apply fromstn0. rewrite contr_eq; assumption. }
    destruct select as [row select]; destruct select as [col select].
    destruct select as [left | right].
    - pose (le_i1_inv := @leading_entry_compute_internal_correct3 _ _ _ H1).
      destruct (natgthorleh j_2 j_1) as [contr_gt | ?]; try assumption.
      contradiction (pr1 le_i1_inv).
      rewrite (pr2 (pr2 (pr2 left))); try reflexivity; try assumption.
      simpl in H3; rewrite H3; assumption.
    - pose (le_i1_inv := @leading_entry_compute_internal_correct3 _ _ _ H1).
      destruct le_i1_inv as [le_i1_inv eq0].
      destruct (natgthorleh j_2 j_1) as [contr_gt | ?]; try assumption.
      contradiction le_i1_inv.
      rewrite (pr2 right); try reflexivity; try assumption.
      exact (pr2 j_1).
  Defined.

  Lemma select_pivot_inv3 {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn)
    (i_1 i_2 : stn m)
    (j_1 j_2 : stn n)
    (le_sep : row_sep ≤ i_1)
    (p : n > 0)
    (H1 : leading_entry_compute (mat i_1) = just j_1)
    (H3 : (pr1 (pr2 (select_pivot mat row_sep p))) = j_2)
    : j_2 ≤ j_1.
  Proof.
    revert H3; set (select := select_pivot mat row_sep p); intros H3.
    destruct (natchoice0 m) as [contr_eq | ?].
    { apply fromstn0. rewrite contr_eq; assumption. }
    destruct select as [row select]; destruct select as [col select].
    destruct select as [left | right].
    - pose (le_i1_inv := @leading_entry_compute_internal_correct3 _ _ _ H1).
      destruct (natgthorleh j_2 j_1) as [contr_gt | ?]; try assumption.
      contradiction (pr1 le_i1_inv).
      rewrite (pr2 (pr2 (pr2 left))); try reflexivity; try assumption.
      simpl in H3; rewrite H3; assumption.
    - pose (le_i1_inv := @leading_entry_compute_internal_correct3 _ _ _ H1).
      destruct le_i1_inv as [le_i1_inv eq0].
      destruct (natgthorleh j_2 j_1) as [contr_gt | ?]; try assumption.
      contradiction le_i1_inv.
      rewrite (pr2 right); try reflexivity; try assumption.
      exact (pr2 j_1).
  Defined.

  Lemma select_pivot_inv4 {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn)
    (i_1 row : stn m)
    (sep_le_i1 : row_sep ≤ i_1)
    (i1_le_i2 : i_1 ≤ row) 
    (p : n > 0)
    (col : stn n)
    (eq_row : (pr1 (select_pivot mat row_sep p)) = row)
    (eq_col : (pr1 (pr2 (select_pivot mat row_sep p))) = col)
    : ((pr1 (select_pivot (gauss_switch_row mat i_1 row) row_sep p)) = row).
  Proof.
    assert (eq: (leading_entry_compute ((gauss_switch_row mat i_1 (pr1 (select_pivot mat row_sep p))) i_1)
      = (leading_entry_compute (mat (pr1 (select_pivot mat row_sep p)))))).
    { apply maponpaths. rewrite eq_row.
      unfold gauss_switch_row.
      destruct (stn_eq_or_neq _ _) as [i1_eq_row | neq];
        rewrite stn_eq_or_neq_refl; try reflexivity.
    }
    pose (pivj := (pr1 (pr2 (select_pivot mat row_sep p)))).
    pose (H := (@select_pivot_inv1 m n _ row_sep col p row col eq_row eq_col)).
    apply pathsinv0.
    etrans. { rewrite <- eq_row. apply idpath. }
    destruct (stn_eq_or_neq (pr1 (select_pivot mat row_sep p))
      (pr1 (select_pivot (gauss_switch_row mat i_1 row) row_sep p))) as [? | contr_neq]; try assumption.
    destruct (natchoice0 m) as [? | gt]. {admit. }
    unfold gauss_switch_row.
    rewrite eq_row in *.

    unfold s

    
  Lemma select_pivot_inv1 {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn)
    (j : stn n)
    (p : n > 0)
    (eq : (pr1 (pr2 (select_pivot mat row_sep p))) = j)
    : coprod (leading_entry_compute (mat (pr1 (select_pivot mat row_sep p)))
      = just (pr1 (pr2 (select_pivot mat row_sep p))))

    revert piveq.
    set (sp := select_pivot (gauss_switch_row mat i_1 i_2) row_sep p).
    intros piveq.


    destruct sp as [H1 H2];
      destruct H2 as [H2 H3].
    destruct H3 as [some | none].
    2: { simpl. admit. }
    destruct some as [H3 H4]; destruct H4 as [H4 H5]; destruct H5 as [H5 H6].
    simpl.
    (* destruct (stn_eq_or_neq H1 i_2) as [? | contr_neq]; try assumption. *)
    rewrite <- piveq in *; clear piveq.
    destruct (select_pivot mat row_sep p) as [H1' H2'];
      destruct H2' as [H2' H3'].
    destruct H3' as [some' | none'].
    - simpl.

      destruct (stn_eq_or_neq H1 H1'); try assumption; simpl.
      simpl in H5.
      contradiction H5.
      unfold gauss_switch_row in *.
      destruct (stn_eq_or_neq _ _).
      {admit. }
      destruct (stn_eq_or_neq _ _).
      + rewrite coprod_rect_compute_1 in *.
        
        rewrite H6.
        rewrite H6.
      
    -
      [H3' H4'].
    simpl.

    -  
    contradiction H5.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq _ _); simpl.
    - simpl.
      destruct (stn_eq_or_neq _ _).
      + simpl.


        rewrite <- H6.
    
    -
    rewrite gauss_switch_row_inv2.

    rewrite H6.



    rewrite H6. try 
    rewrite <- piveq in gs_eq.
    rewrite <- piveq in gs_eq at 1.

    (* for all elements lower than X, we do Y. *)
    (* for all elements lower than (X moved to Z), we do Y *)
    


    unfold select_pivot, select_pivot_internal in *.
    
    destruct piveq as [H1 H2]. destruct H2 as [H2 H3].
    About funextfun.
    About funextfun.

  Defined.*)

End LeadingEntry.

Section Gauss.

  Context (R : rig).
  Context (F : fld).
  
  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition gauss_clear_column_step
    {m n : nat}
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (i : (stn m))
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    (*destruct (fldchoice0 (mat k_i k_j)) as [uninteresting | neq0]. {exact mat. }*)
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    - exact mat.
    - exact (add_row_matrix k_i i (- ( (mat i k_j) * fldmultinv' (mat k_i k_j)))%ring
      ** mat).
  Defined.

  Definition gauss_clear_column_step'
    {m n : nat}
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (i : (stn m))
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    (*destruct (fldchoice0 (mat k_i k_j)) as [uninteresting | neq0]. {exact mat. }*)
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    - exact mat.
    - exact (gauss_add_row mat k_i i (- ((mat i k_j) * fldmultinv' (mat k_i k_j)))%ring).
  Defined.

  Lemma gauss_clear_column_step_eq {m n : nat}
    (k_i i: (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (mat : Matrix F m n)
    : (gauss_clear_column_step k_i k_j i mat) = (gauss_clear_column_step' k_i k_j i mat).
  Proof.
    unfold gauss_clear_column_step.
    unfold gauss_clear_column_step'.
    (*destruct (fldchoice0 _) as [? | neq0]; try reflexivity.*)
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    {apply idpath. }
    rewrite add_row_mat_elementary.
    - apply idpath.
    - apply issymm_natneq.
      assumption.
  Defined.

  (* TODO generalize some of this material to rigs *)
  Lemma gauss_add_row_inv0
    {m n : nat}
    (mat : Matrix F m n)
    (i : ⟦ m ⟧%stn)
    (j: ⟦ m ⟧%stn)
    (s : F)
    : ∏ (k : ⟦ m ⟧%stn), j ≠ k -> gauss_add_row mat i j s k = mat k.
  Proof.
    intros k j_ne_k.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j].
    - rewrite k_eq_j in j_ne_k.
      apply isirrefl_natneq in j_ne_k.
      apply fromempty; assumption.
    - simpl.
      reflexivity.
  Defined.

  (* TODO step invs at same place *)
  Lemma gauss_clear_column_step_inv2
    {m n : nat}
    (k_i : stn m)
    (k_j : (⟦ n ⟧%stn))
    (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n)
    (j : ⟦ m ⟧%stn)
    (p : r ≠ j)
    : ((gauss_clear_column_step k_i k_j j mat) r) = (mat r).
  Proof.
    intros.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    (*destruct (fldchoice0 _); try reflexivity.*)
    destruct (stn_eq_or_neq j k_i) as [? | ?].
    {apply idpath. }
    apply funextfun; intros ?.
    rewrite gauss_add_row_inv0; try reflexivity.
    apply issymm_natneq; assumption.
  Defined.

  (* TODO fix numbering of these *)
  Lemma gauss_clear_column_step_inv7
    {m n : nat}
    (k_i : stn m)
    (k_j : (⟦ n ⟧%stn))
    (mat : Matrix F m n)
    (i : ⟦ m ⟧%stn)
    (p : k_i ≠ i)
    (neq0 : mat k_i k_j != 0%ring)
    : ((gauss_clear_column_step k_i k_j i mat) k_i k_j) != 0%ring.
  Proof.
    rewrite gauss_clear_column_step_inv2; try assumption.
  Defined.

  (* Equivalent and the right definition with iter as S n instead of n -> TODO is
     replacing uses of the other one with this one *)
  (* [gauss_clear_column' mat k p _]:
    clear column [k] in rows [0 ≤ i < p],
    from row 0 up to row p (though order doesn’t matter. *)
  (* TODO: rename to [gauss_clear_column_segment] *)
  (* Temporarily renamed to old ! To try to make all lemmas work on this one. *)
  Definition gauss_clear_column
    { m n : nat }
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn)
    : Matrix F m n.
  Proof.
    (*destruct (fldchoice0 (mat k_i k_j)) as [uninteresting | neq0]. {exact mat. }*)
    destruct iter as [iter lt].
    induction iter as [ | iter gauss_clear_column_IH ].
    { exact mat. }
    destruct (natgthorleh iter k_i) as [gt | leh].
    - refine (gauss_clear_column_step k_i k_j (iter,, lt) _ ).
      refine (gauss_clear_column_IH _).
      refine (istransnatlth _ _ _ (natgthsnn iter) _).
      assumption.
    - exact mat.
  Defined.

  Lemma gauss_clear_column_as_left_matrix 
    { m n : nat }
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    : Matrix F m m.
  Proof.
    (*destruct (fldchoice0 (mat k_i k_j)) as [uninteresting | neq0]. {exact (@identity_matrix F m). }*)
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - exact (@identity_matrix F m).
    - assert (p': iter < S m).
      { apply (istransnatlth _ _ _ (natgthsnn iter) p ). }
       destruct (natgthorleh iter k_i).
      + exact (add_row_matrix k_i (iter,, p)
        (- ((mat (iter,, p) k_j) * fldmultinv' (mat k_i k_j) ))%ring ** (IH p')).
      + exact (@identity_matrix F m ** (IH p')).
  Defined.

  Lemma gauss_add_row_inv1
    {m n : nat}
    (mat : Matrix F m n)
    (i : ⟦ m ⟧%stn)
    (j: ⟦ m ⟧%stn)
    (s : F)
    : ∏ (k : ⟦ m ⟧%stn),
      (mat i = const_vec 0%ring) -> gauss_add_row mat i j s = mat.
  Proof.
    intros k eq0.
    apply funextfun; intros i'; apply funextfun; intros j'.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'];
      simpl; try reflexivity.
    simpl.
    rewrite <- i'_eq_j'.
    rewrite eq0.
    unfold const_vec ; simpl.
    rewrite (@ringmultx0 F).
    rewrite (@rigrunax1 F).
    reflexivity.
  Defined.

  Lemma gauss_add_row_inv2
    {m n : nat}
    (mat : Matrix F m n)
    (i_1 i_2: ⟦ m ⟧%stn)
    (s : F)
    : ∏ (j_1: ⟦ n ⟧%stn),
    (mat i_1 j_1 = 0%ring)
    -> (gauss_add_row mat i_1 i_2 s) i_2 j_1 = mat i_2 j_1.
  Proof.
    intros j_1 eq0.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'];
      simpl; try reflexivity.
    rewrite eq0.
    rewrite (@ringmultx0 F).
    rewrite (@rigrunax1 F).
    reflexivity.
  Defined.

  (* Restating a similar lemma for the regular version of this operation,
     in order to prove their equivalence
     TODO this should not be necessary - should follow from pr1_ \le j invariant
     TODO at least remove 'h' temp variable names*)
  Lemma gauss_clear_column_as_left_matrix_inv0
    { m n : nat }
    (iter : (stn (S m)))
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : stn n)
    (i : ⟦ m ⟧%stn)
    : iter ≤ i
    -> ((gauss_clear_column_as_left_matrix iter mat k_i k_j) ** mat) i = mat i.
  Proof.
    intros le.
    unfold gauss_clear_column_as_left_matrix.
    (*destruct (fldchoice0 _).
    { rewrite matlunax2; apply idpath. } *)
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl. intros. simpl.
      rewrite matlunax2. reflexivity.
    - unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh iter k_i) as [gt | ?].
      + unfold gauss_clear_column_as_left_matrix in IH.
        assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
        ( rewrite <- (IH lt)).
        rewrite matrix_mult_assoc.
        2 : { apply natlehtolehs in le; assumption. }
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq.  apply natgthtoneq in gt. assumption. }
        rewrite IH. 2 : {apply natlehsntolth in le. apply natlthtoleh in le. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply snlehtotonlt in le.
            - apply issymm_natneq. apply natgthtoneq; assumption.
            - apply natneq0togth0.
              destruct (natchoice0 iter) as [lt' | ?].
              + rewrite <- lt' in gt.
                apply negnatgth0n in gt.
                contradiction.
              + apply natgthtoneq.
                assumption.
        }
        rewrite IH; try apply idpath.
        apply natlehsntolth; apply natlthtoleh; assumption.
      + rewrite matlunax2.
        assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
        unfold gauss_clear_column_as_left_matrix in IH.
        rewrite <- (IH lt).
        2 : {apply (istransnatleh (natgehsnn iter) le). }
        unfold matrix_mult.
        apply funextfun; intros q.
        apply maponpaths; do 2 apply maponpaths_2.
        apply maponpaths.
        apply proofirrelevance; apply propproperty.
  Defined.

  Lemma gauss_clear_column_as_left_matrix_inv1
    { m n : nat }
    (iter : stn (S m))
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : (stn n))
    (i : ⟦ m ⟧%stn)
    (i_leh_k : i ≤ k_i)
    : (gauss_clear_column_as_left_matrix iter mat k_i k_j ** mat) i = mat i.
  Proof.
    unfold gauss_clear_column_as_left_matrix.
    (* destruct (fldchoice0 _). {rewrite matlunax2. apply idpath. } *)
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl. rewrite matlunax2. reflexivity.
    - intros.
      unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh iter k_i) as [gt | ?].
      + assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
        ( rewrite <- (IH lt)).
        unfold gauss_clear_column_as_left_matrix in *.
        rewrite IH.
        rewrite matrix_mult_assoc.
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq. apply natgthtoneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k gt).  }
        unfold gauss_clear_column_as_left_matrix in IH.
        rewrite IH.
        reflexivity.
      + rewrite matlunax2.
        unfold gauss_clear_column_as_left_matrix in IH.
        rewrite IH.
        reflexivity.
  Defined.

  Lemma clear_column_matrix_invertible
    { m n : nat }
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : stn n)
    : @matrix_inverse F _ (gauss_clear_column_as_left_matrix iter mat k_i k_j).
  Proof.
    (*set (pre := gauss_clear_column_as_left_matrix iter mat k_i k_j).*)
    unfold gauss_clear_column_as_left_matrix(* in pre*).
    (* destruct (fldchoice0 _). { apply identity_matrix_is_inv. } *)
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl. apply identity_matrix_is_inv.
    - rewrite nat_rect_step.
      destruct (natgthorleh iter k_i) as [gt | ?].
      2: { apply inv_matrix_prod_is_inv.
           - apply identity_matrix_is_inv.
           - apply IH. }
      apply inv_matrix_prod_is_inv.
      { apply add_row_matrix_is_inv.
        apply natlthtoneq; assumption. }
      apply IH.
  Defined.

  Definition gauss_clear_row
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    : Matrix F m n.
  Proof.
    destruct (natchoice0 n) as [contr_eq | p].
    { unfold Matrix, Vector. intros. apply fromstn0. rewrite contr_eq; assumption. }
    destruct (select_uncleared_column F mat row p) as [some | none].
    2 : {exact mat. }
    unfold exists_first_uncleared in some.
    refine (gauss_clear_column
      _  row (pr1 ((some ))) (m,, natlthnsn m)).
    exact (gauss_switch_row mat row (pr1 (pr2 (pr2 some)))).
  Defined.

  Definition gauss_clear_row_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    (p : n > 0)
    : Matrix F m m.
  Proof.
    (*destruct (pr2 (select_uncleared_column F mat row p)) as [some | none].*)
    destruct (select_uncleared_column F mat row p) as [some | none].
    2 : {exact (@identity_matrix F m). }
    set (mat_by_normal_op := (gauss_switch_row mat row (pr1 (pr2 (pr2 some))))).
    refine ((gauss_clear_column_as_left_matrix (m,, natgthsnn m) mat_by_normal_op row
      (pr1 (some))) ** _).
    refine (switch_row_matrix m row (pr1 (pr2 (pr2 some)))).
  Defined.

  Lemma clear_row_matrix_invertible
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    (p : n > 0)
    : @matrix_inverse F _ (gauss_clear_row_as_left_matrix mat row p).
  Proof.
    unfold gauss_clear_row_as_left_matrix.
    destruct (select_uncleared_column F mat row p) as [some | none].
    2: { destruct (natchoice0 m); try apply identity_matrix_is_inv;
         try apply nil_matrix_is_inv; try assumption;
         try apply identity_matrix_is_inv; symmetry; assumption.
    }
    apply inv_matrix_prod_is_inv.
    - apply clear_column_matrix_invertible.
    - apply switch_row_matrix_is_inv.
  Defined.

  Definition gauss_clear_rows_up_to
    { m n : nat }
    (mat : Matrix F m n)
    (row_sep : (⟦ S m ⟧%stn))
    : (Matrix F m n).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    { exact mat. }
    refine (gauss_clear_row _ (row_sep,, row_sep_lt_n)).
    refine (gauss_clear_earlier_rows _).
    exact (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ).
  Defined.

  Definition gauss_clear_rows
      { m n : nat } (mat : Matrix F m n)
    := gauss_clear_rows_up_to mat (m,, natgthsnn m).

  (* invertible matrix, such that left-multiplication by this
     corresponds to [gauss_clear_columns_up_to]  *)
  Lemma clear_rows_up_to_as_left_matrix_internal
      { m n : nat }
      (mat : Matrix F m n)
      (row_sep : (⟦ S m ⟧%stn))
      (p : n > 0)
    : (Matrix F m m).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    { exact (@identity_matrix F m). }
    assert (lt : row_sep < S m).  {apply (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ). }
    set (mat_by_normal_op :=  (gauss_clear_rows_up_to mat (row_sep,, lt))).
    refine ((gauss_clear_row_as_left_matrix mat_by_normal_op (row_sep,, row_sep_lt_n) p ** _)).
    exact (gauss_clear_earlier_rows lt).
  Defined.

  Lemma clear_rows_up_to_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (k : (⟦ S m ⟧%stn))
    (p : n > 0)
    : Matrix F m m.
  Proof.
    exact (clear_rows_up_to_as_left_matrix_internal mat k p).
  Defined.

  Lemma clear_rows_up_to_matrix_invertible
    {m n : nat}
    (iter : ⟦ S m ⟧%stn)
    (k : (⟦ m ⟧%stn))
    (mat : Matrix F m n)
    (p : n > 0)
    : @matrix_inverse F _  (clear_rows_up_to_as_left_matrix mat iter p).
  Proof.
    unfold clear_rows_up_to_as_left_matrix.
    set (pre := gauss_clear_column_as_left_matrix iter mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
    induction pr1_ as [| pr1_ IH].
    - simpl. apply identity_matrix_is_inv.
    - unfold clear_rows_up_to_as_left_matrix,
             clear_rows_up_to_as_left_matrix_internal.
      rewrite nat_rect_step.
      apply inv_matrix_prod_is_inv.
      + apply clear_row_matrix_invertible; try assumption.
      + apply IH.
  Defined.

  (* Inputting a matrix and transforming it into an upper-triangular matrix by
     elementary matrix operations or equivalent *)
  Definition gauss_clear_all_row_segments
    { m n : nat }
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    refine ((gauss_clear_rows_up_to mat (m,,_))).
    exact (natgthsnn m).
  Defined.

  Definition gauss_clear_all_column_segments_by_left_mult
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    : Matrix F m m.
  Proof.
    refine (clear_rows_up_to_as_left_matrix mat (m,,_) p).
    exact (natgthsnn m).
  Defined.

  (* TODO: remove this for the version from RowOps *)
  Definition gauss_add_row_comp1
    { m n : nat }
    ( mat : Matrix F m n )
    ( r1 r2 : ⟦ m ⟧%stn )
    (s : F)
    (c : ⟦ n ⟧%stn)
  : (gauss_add_row mat r1 r2 s) r2 c = op1 (mat r2 c) (op2 s (mat r1 c)).
  Admitted.

  (* The clear column step operation does clear the target entry (mat (k j)) *)
  (* TODO fix double work being done here - work on step' or use previous lemma *)
  Lemma gauss_clear_column_step_inv1 {m n : nat}
        (r_pivot : ⟦m⟧%stn) (c_pivot : ⟦ n ⟧%stn)
        (r : (⟦ m ⟧%stn)) (mat : Matrix F m n)
        (p_1 : mat r_pivot c_pivot != 0%ring)
        (p_2 : r ≠ r_pivot)
    : (gauss_clear_column_step r_pivot c_pivot r mat) r c_pivot = 0%ring.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    (* destruct (fldchoice0 _) as [contr_eq0 | neq0].
    { contradiction p_1. }*)
    destruct (stn_eq_or_neq r r_pivot) as [p | ?].
    { rewrite p in p_2. apply isirrefl_natneq in p_2. contradiction. }
    rewrite add_row_mat_elementary.
    2: { apply issymm_natneq; assumption. }
    rewrite gauss_add_row_comp1.
    set (a := (mat r c_pivot)).
    set (b := (mat r_pivot c_pivot)).
    rewrite <- (@ringlmultminus F).
    rewrite ringassoc2.
    etrans. { apply maponpaths, maponpaths, fldmultinvlax'; assumption. }
    rewrite (@rigrunax2 F).
    apply ringrinvax1.
  Qed.

  Lemma gauss_clear_column_step_inv3
    {m n : nat} (k_i : stn m) 
    (k_j : (⟦ n ⟧%stn)) (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n) (j : ⟦ m ⟧%stn)
    (j' : stn n) (p : r < j)
    : (gauss_clear_column_step k_i k_j j mat) r j' = mat r j'.
  Proof.
    assert (p': r ≠ j). {apply issymm_natneq.  apply natgthtoneq. assumption. }
    rewrite (gauss_clear_column_step_inv2 k_i k_j r mat j  p').
    apply idpath.
  Defined.


  Lemma gauss_clear_column_step_inv5
    {m n : nat} (mat : Matrix F m n)
    (i : (⟦ m ⟧)%stn)
    (k_i : (⟦ m ⟧)%stn) (k_j : stn n)
    (r : stn m) (c : stn n)
    : mat k_i c = 0%ring -> (gauss_clear_column_step k_i k_j i mat) r c = mat r c.
  Proof.
    intros kj_0.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    (*destruct (fldchoice0 _) as [eq0 | contr]; 
      try apply idpath; contradiction.*)
    destruct (stn_eq_or_neq _ _); try apply idpath;
      try contradiction.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq]; try reflexivity.
    simpl.
    rewrite eq.
    rewrite kj_0.
    rewrite (@ringmultx0 F).
    rewrite (@ringrunax1 F).
    reflexivity.
  Defined.


  Lemma gauss_clear_column_step_inv6
    {m n : nat} (mat : Matrix F m n)
    (i : (⟦ m ⟧)%stn)
    (k_i : (⟦ m ⟧)%stn) (k_j : stn n)
    : mat k_i k_j = 0%ring -> (gauss_clear_column_step k_i k_j i mat) = mat.
  Proof.
    intros kj_0.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    (*destruct (fldchoice0 _) as [eq0 | contr]; 
      try apply idpath; contradiction.*)
    destruct (stn_eq_or_neq _ _); try apply idpath;
      try contradiction.
    unfold gauss_add_row.
    apply funextfun; intros i_2.
    apply funextfun; intros i_3.
    destruct (stn_eq_or_neq _ _) as [eq | neq]; try reflexivity.
    simpl.
    rewrite eq.
    unfold fldmultinv'.
    rewrite (fldchoice0_left _ kj_0).
    rewrite (@ringmultx0 F).
    rewrite ringinvunel1.
    rewrite (@ringmult0x F).
    rewrite (@ringrunax1 F).
    reflexivity.
  Defined.

  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (r : ⟦ m ⟧%stn)
    (r_gt_n' : r ≥ iter)
    : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    (*destruct (fldchoice0 _) as [? | neq0]; try apply idpath.*)
    destruct iter as [n' p].
    induction n' as [| n' IH]; try reflexivity.
    rewrite nat_rect_step.
    destruct (natgthorleh n' k_i). 2: { apply idpath. }
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    (*destruct (fldchoice0 _) as [? | ?]; try apply idpath; try apply IH; try
      apply (istransnatgeh _ _ _ (r_gt_n') (natgthtogeh _ _ (natgthsnn n'))).*)
    destruct (stn_eq_or_neq _ _).
    { unfold gauss_clear_column, gauss_clear_column_step.
      unfold gauss_clear_column in IH.
      apply IH.
      apply natgthtogeh; assumption.
    }
    unfold gauss_clear_column in IH.
    rewrite gauss_add_row_inv0. 2: {apply natlthtoneq. assumption. }
    rewrite IH. { apply idpath. }
    apply natgthtogeh.
    apply r_gt_n'.
  Defined.

  (* if the target row r ≤  the pivot row k,
     mat r is not changed bybac the clearing procedure. *)
  Lemma gauss_clear_column_inv3
        { m n : nat } (k_i : (⟦ m ⟧%stn)) (k_j : stn n) (r : stn m)
        (iter : ⟦ S m ⟧%stn) (p' : r ≤ k_i)
        (mat : Matrix F m n)
        : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    (*destruct (fldchoice0 _) as [? | neq0]; try apply idpath.*)
    destruct iter as [n' p].
    induction n' as [| n' IH]; try reflexivity.
    unfold gauss_clear_column.
    apply funextfun. intros q.
    rewrite nat_rect_step.
    destruct (natgthorleh _ _); try reflexivity.
    rewrite gauss_clear_column_step_inv3.
    2 : {refine (natgthgehtrans _ _ _ h _); assumption. }
    unfold gauss_clear_column in IH.
    rewrite IH.
    reflexivity.
  Defined.

  (* Proving the column clearing procedure works on one row at a time *)
  (* TODO - not admit, fix some variable naming*)
  Lemma gauss_clear_column_inv1
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    : ∏ r : (⟦ m ⟧%stn), r < iter -> k_i < r ->
    ((gauss_clear_column  mat k_i k_j iter) r = (gauss_clear_column_step' k_i k_j r mat) r).
  Proof.
    unfold gauss_clear_column.
    (* destruct (fldchoice0 _) as [? | neq0]; try apply idpath.
    { intros. rewrite <- gauss_clear_column_step_eq. 
      apply pathsinv0. rewrite gauss_clear_column_step_inv6; try reflexivity; assumption. } *)
    destruct iter as [n' p].
    revert mat k_i k_j p (*neq0*).
    induction n' as [| n' IHn'].
    - intros mat (*?*) ? ? ? r r_le_0.
      contradiction (negnatgth0n r r_le_0).
    - intros mat k_i k_j p (*neq0*) r r_le_sn k_le_r.
      assert (p' : n' < S m). {apply (istransnatlth _ _ _ (natgthsnn n') p). }
      set (IHnp := IHn'  mat k_i k_j p').
      assert (eq' : p' = istransnatlth n' (S n') (S m) (natlthnsn n') p).
      { apply propproperty. }
      destruct (natlehchoice r (n')) as [? | eq]. {assumption. }
      + assert (le: r ≤ n'). { apply natlthtoleh in h. assumption. }
        unfold gauss_clear_column.
        rewrite nat_rect_step.
        unfold gauss_clear_column in IHnp.
        destruct (natgthorleh _ _) as [le' | gt].
        2: { assert (absurd : n' ≤ r).
             { apply natgthtogeh in k_le_r.
               apply (istransnatleh gt k_le_r). }
               apply fromempty.
               apply natgehtonegnatlth in absurd.
               contradiction.
        }
        rewrite (gauss_clear_column_step_inv2).
        2 : { apply natgthtoneq in h. apply issymm_natneq. apply h. }
        rewrite <- IHnp; try reflexivity; try assumption.
        rewrite eq'; reflexivity.
      + rewrite <- gauss_clear_column_step_eq.
        rewrite gauss_clear_column_step_eq.
        unfold gauss_clear_column.
        rewrite nat_rect_step.
        unfold gauss_clear_column_step'.
        (*rewrite (fldchoice0_right _ neq0).*)
        destruct (natgthorleh _ _).
        2: { unfold gauss_clear_column_step.
             destruct (stn_eq_or_neq _ _); try reflexivity.
             assert (absurd : n' ≤ r).
             { apply natgthtogeh in k_le_r.
               rewrite eq; apply isreflnatgeh. }
             rewrite <- eq in *.
             apply natlehneggth in h.
             contradiction.
        }
        assert (stn_eq : n',, p = r).
        { apply subtypePath_prop. change n' with (pr1 (make_stn _ n' p')) in eq.
          unfold stntonat in eq. simpl. unfold make_stn in eq. simpl in eq. 
          rewrite <- eq; reflexivity. }
        rewrite stn_eq in *.
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
        { rewrite contr_eq in k_le_r. contradiction (isirreflnatgth _ k_le_r). }
        replace (gauss_clear_column_step k_i k_j r _ r)
          with (gauss_clear_column_step k_i k_j r mat r).
        { rewrite gauss_clear_column_step_eq. unfold gauss_clear_column_step'.
            destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
            { rewrite contr_eq in k_le_r. contradiction (isirreflnatgth _ k_le_r). }
            apply idpath.
        }
        assert (commute :
          gauss_clear_column_step k_i k_j (n',, p) (gauss_clear_column mat k_i k_j
            (n',, p')) r
          =  gauss_clear_column (gauss_clear_column_step k_i k_j (n',, p) mat) k_i k_j
            (n',, p') r).
        { do 2 rewrite gauss_clear_column_step_eq.
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _).
          { cbn. reflexivity. }
          unfold gauss_add_row.
          rewrite gauss_clear_column_inv0; simpl.
          2 : { apply (natlthnsn). }
          generalize p. generalize p'.
          rewrite <- eq.
          intros q q'; simpl.
          rewrite eq in *.
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: { contradiction (isirrefl_natneq _ contr_neq). }
          apply pathsinv0.
          etrans.
          { rewrite (gauss_clear_column_inv0).
            - apply idpath.
            - simpl. rewrite eq.
              apply natlthnsn.
          }
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: { contradiction (isirrefl_natneq _ contr_neq). }
          apply funextfun. intros y.
          apply maponpaths.
          apply maponpaths_12.
          - apply maponpaths.
            apply maponpaths.
            assert (eq'': mat k_i k_j = (gauss_clear_column mat k_i k_j (stntonat m r,, q) k_i k_j)).
            { rewrite gauss_clear_column_inv3; try reflexivity; apply isreflnatleh. }
            assert (fldmultinv'_eq : forall e1 e2 : F, (*forall p1 : e1 != 0%ring,
              forall p2: e2 != 0%ring,*) e1 = e2 -> fldmultinv' e1 = fldmultinv' e2).
            { admit. }
            apply fldmultinv'_eq. assumption.
          - rewrite gauss_clear_column_inv3; try reflexivity; apply isreflnatleh.
        }
        set (f := @gauss_clear_column_inv0).
        rewrite <- (f m n k_i k_j (n' ,, p')).
        2: { rewrite eq. apply isreflnatleh. }
        rewrite stn_eq in commute.
        rewrite <- commute.
        unfold gauss_clear_column.
        (*rewrite (fldchoice0_right _ neq0).*)
        assert (peq: p' = (istransnatlth n' (S n') (S m) (natgthsnn n') p)).
        { apply proofirrelevance, propproperty. }
        rewrite peq.
        reflexivity.
  Admitted. (* TODO inv lemma *)

  (* Invariant stating that the clearing procedure does clear all the target entries (r, k) for r > k. *)
  (* TODO use this more *)
  Lemma gauss_clear_column_inv7
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn) (mat : Matrix F m n)
    (p' : mat k_i k_j != 0%ring)
    : ∏ r : (⟦ m ⟧%stn), r < iter -> r > k_i
    -> ((gauss_clear_column mat k_i k_j iter) r k_j = 0%ring).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv1  k_i k_j (n' ,, p) mat r r_le_n').
    rewrite <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 k_i k_j r mat);
      try reflexivity; try assumption.
    - apply natgthtoneq. assumption.
    - apply r_gt_k.
  Defined.

  Lemma gauss_clear_column_inv8
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn) (mat : Matrix F m n)
    (p' : mat k_i k_j != 0%ring)
    : ∏ r : (⟦ m ⟧%stn), r < iter -> r > k_i
    -> ((gauss_clear_column mat k_i k_j iter) r k_j = 0%ring).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv1  k_i k_j (n' ,, p) mat r r_le_n').
    rewrite <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 k_i k_j r mat);
      try reflexivity; try assumption.
    - apply natgthtoneq. assumption.
    - apply r_gt_k.
  Defined.

  Lemma gauss_clear_column_inv9
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn) (mat : Matrix F m n)
    (p' : mat k_i k_j != 0%ring)
    : ∏ r : (⟦ m ⟧%stn), ∏ c : (⟦ n ⟧%stn), (mat k_i c = 0%ring)
    -> ((gauss_clear_column mat k_i k_j iter) r c = mat r c).
  Proof.
    destruct iter as [n' p].
    intros r c eq0. (*r_le_n' r_gt_k.*)
    (*rewrite (gauss_clear_column_inv0  k_i k_j (n' ,, p) mat r (*r_le_n')*)); try assumption.*)
    unfold gauss_clear_column.
    induction n' as [| n' IH]. { simpl; reflexivity. }
    rewrite nat_rect_step.
    destruct (natgthorleh _ _); try reflexivity.
    rewrite <- (IH (istransnatlth _ _ _ (natgthsnn n') p)).
    rewrite gauss_clear_column_step_inv5; try reflexivity.
    pose (eq := @gauss_clear_column_inv3).
    unfold gauss_clear_column in eq.
    set (lt := (istransnatlth n' (S n') (S m) (natgthsnn n') p)).
    change n' with (pr1 (make_stn _ n' lt)).
    change lt with (pr2 (make_stn _ n' lt)).
    rewrite eq; try assumption.
    apply isreflnatleh.
  Defined.

  (* if the iterator n' ≤   the pivot index k,
     applying the clearing procedure leaves mat invariant. *)
  Lemma gauss_clear_column_inv2
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn)) (iter : ⟦ S m ⟧%stn)
    (p' : S iter ≤ k_i)
    (mat : Matrix F m n) (kk_ne_0 : mat k_i k_j != 0%ring)
    : ((gauss_clear_column mat k_i k_j iter) = mat ).
  Proof.
    intros.
    unfold gauss_clear_column.
    (*rewrite (fldchoice0_right _ kk_ne_0).*)
    destruct iter as [iter p].
    apply funextfun. intros i.
    intros.
    induction iter as [|iter  IHn].
    - simpl.
      reflexivity.
    - assert (lt: iter < S m). { apply (istransnatgth _ _ _ p (natgthsnn iter) ). }
      assert (le : S iter ≤ k_i). { apply (istransnatgeh _ _ _ p' (natgehsnn (S iter) )  ). }
      set (IHn' := IHn lt le).
      rewrite <- IHn'.
      unfold gauss_clear_column.
      rewrite nat_rect_step.
      destruct (natgthorleh _ _).
      { clear IHn'. apply fromempty. apply natgehsntogth in lt.
        apply natgehsntogth in le.
        apply isasymmnatgth in le; try assumption; contradiction.
      }
      unfold gauss_clear_column in IHn.
      rewrite  IHn; try assumption; reflexivity.
  Defined.


  (* Expresses the property that a matrix is partially upper triangular -
     in the process of being constructed as upper triangular.
     mat =
     [ 1 0 0 1
       0 1 1 1
       0 0 1 1
       0 0 1 1]  - fulfills  gauss_columns_cleared mat (1,, 1 < 4).

    Additionally expresses the property that any entry i j with i > k_i is 0.

  TODO maybe not useful anymore. *)
  (* Definition gauss_columns_cleared { n : nat } (mat : Matrix F n n)
             (k_i k_j : ⟦ n ⟧%stn) := ∏ i j : ⟦ n ⟧%stn,
              j < k_j ->
              k_i < i ->
              mat i j = 0%ring. *)



  (* Proving that if the input matrix is  _lower triangular_, it will remain so after gcc. *)
  Lemma gauss_clear_column_inv5
    { m n : nat } (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : stn n)
    (iter : ⟦ S m ⟧%stn)
    (lt : @is_lower_triangular F m n mat)
    : @is_lower_triangular F m n (gauss_clear_column mat k_i k_j iter).
  Proof.
    intros.
    unfold gauss_clear_column.
    (*destruct (fldchoice0 _); try assumption.*)
    unfold is_lower_triangular.
    unfold gauss_clear_column.
    destruct iter as [iter ?].
    induction iter as [| iter IHiter].
    { intros i j i_lt_j. simpl.
      apply (lt _ _ i_lt_j). }
    intros i j i_lt_j.
    rewrite nat_rect_step.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (natgthorleh _ _) as [gt | le].
    2: { apply lt.  assumption. }
    destruct (stn_eq_or_neq  _ _) as [eq | ?].
    { rewrite <- eq in gt. apply isirreflnatgth in gt. contradiction. }
    (*destruct (fldchoice0 _); try assumption.
    {  apply IHiter; try assumption. }*)
    set (q := nat_rect _ _ _ _).
    set (p := istransnatlth _ _ _ _).
    unfold gauss_add_row.
    apply issymm_natneq in h.
    destruct (stn_eq_or_neq i (iter,, pr2)) as [eq | neq].
    - simpl.
      rewrite IHiter.
      2: { rewrite eq in i_lt_j.
           simpl in i_lt_j. simpl.
           rewrite <- i_lt_j.
           reflexivity. }
      replace (q _ k_i j) with (@ringunel1 F).
      2: {unfold q.
          rewrite IHiter; try reflexivity.
          rewrite eq in i_lt_j.
          refine (istransnatgth _ _ _ _ _).
          - apply i_lt_j.
          - apply gt.
      }
      rewrite (@rigmultx0 F).
      rewrite (@riglunax1 F).
      apply idpath.
    - simpl.
      rewrite  IHiter; try reflexivity; try assumption.
  Defined.

  (* 0 in pivot row -> corresponding col is unchanged after gcc *)
  Lemma gauss_clear_column_inv6
    { m n : nat }  (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : stn n)
    (iter : ⟦ S m ⟧%stn) (j : ⟦ n ⟧%stn)
    (p : mat k_i j = 0%ring)
    : ∏ i : ⟦ m ⟧%stn, gauss_clear_column mat k_i k_j iter i j = mat i j.
  Proof.
    unfold gauss_clear_column.
    (*destruct (fldchoice0 _); try reflexivity.*)
    destruct iter as [iter ?].
    induction iter.
    { intros i. simpl. reflexivity. }
    intros i.
    rewrite nat_rect_step.
    rewrite  gauss_clear_column_step_eq.
    destruct (stn_eq_or_neq (iter,, pr2) (*j*) k_i) as [eq | ?].
    - rewrite <- eq.
      destruct (natgthorleh _ _) as [contr | ?].
      { apply isirreflnatgth in contr. contradiction. }
      reflexivity.
    - assert (obv : iter < S m). {exact (istransnatlth iter (S iter) (S m) (natlthnsn iter) pr2). }
      rewrite <- (IHiter (istransnatlth iter (S iter) (S m) (natlthnsn iter) pr2)).
      rewrite <- gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct ( natgthorleh _ _).
      2: { rewrite IHiter. reflexivity. }
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _); try reflexivity.
      (*destruct (fldchoice0 _); try reflexivity.
      destruct (fldchoice0 _); try reflexivity.*)
      unfold gauss_add_row.
      destruct (stn_eq_or_neq _ _) as [eq | ?];
        try apply coprod_rect_compute_1; try apply coprod_rect_compute_2.
      + rewrite coprod_rect_compute_1.
        do 3 rewrite IHiter.
        rewrite p.
        rewrite <- eq.
        rewrite (@rigmultx0 F).
        rewrite (@rigrunax1 F).
        reflexivity.
      + rewrite coprod_rect_compute_2.
        reflexivity.
  Defined.

  (* 1 : any leading entry is strictly to the right of a previous leading entry
     2 : any zero row is below any non-zero row *)
  Definition is_row_echelon {m n : nat} (mat : Matrix F m n) :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    (∏ j_1 j_2 : ⟦ n ⟧%stn,
         (*leading_entry_compute F (mat i_1) = (just j_2)*)
         is_leading_entry F (mat i_1) j_2
      -> i_1 < i_2 -> j_1 ≤ j_2 -> mat i_2 j_1 = 0%ring)
   × ((mat i_1 = const_vec 0%ring) -> (i_1 < i_2) -> (mat i_2 = const_vec 0%ring)).

  Definition is_row_echelon_partial_1
    {m n : nat} (mat : Matrix F m n) (p : n > 0) (row_sep : ⟦ S m ⟧%stn) :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    ∏ j_1 j_2 : ⟦ n ⟧%stn,
     i_1 < row_sep
    (*-> leading_entry_compute F (mat i_1) = (just j_2)*)
    -> is_leading_entry F (mat i_1) j_2
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%ring.

  Definition is_row_echelon_partial_2
    {m n : nat} (mat : Matrix F m n) (iter : ⟦ S m ⟧%stn) :=
    ∏ (i_1 i_2 : ⟦ m ⟧%stn),
    i_1 < iter
    -> (mat i_1 = const_vec 0%ring)
    -> i_1 < i_2
    -> mat i_2 = const_vec 0%ring.

  Definition is_row_echelon_partial
    {m n : nat} (mat : Matrix F m n) (p : n > 0) (iter : ⟦ S m ⟧%stn)
    := is_row_echelon_partial_1 mat p iter × is_row_echelon_partial_2 mat iter.

  Lemma is_row_echelon_from_partial
    {m n : nat} (mat : Matrix F m n) (p : n > 0)
    : (is_row_echelon_partial mat p (m,, natgthsnn m)) -> is_row_echelon mat.
  Proof.
    unfold is_row_echelon, is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    intros H ? ?; intros; use tpair.
    { intros j_1 j_2 X. refine (pr1 (H) i_1 i_2 j_1 _ _ _ );
      try apply X; try assumption. exact (pr2 i_1). }
    simpl; intros.
    refine ((pr2 H) i_1 i_2 _ _ _ ); try assumption.
    exact (pr2 i_1).
  Defined.

  Lemma gauss_clear_row_inv0
    {m n : nat} (mat : Matrix F m n) (row : ⟦ m ⟧%stn) (iter : ⟦ S n ⟧%stn)
    (p : n > 0)
    : ∏ i : ⟦ m ⟧%stn, i < row -> (gauss_clear_row mat ) row i = mat i.
  Proof.
    unfold gauss_clear_row.
    destruct (natchoice0 n) as [contr_eq | gt]. { rewrite contr_eq in p.
      contradiction (isirreflnatgth _ p). }
    intros i lt.
    destruct (@select_uncleared_column _ _ _ mat row gt) as [some | none];
      try reflexivity.
    destruct some as [piv_c some].
    simpl.
    rewrite gauss_clear_column_inv3; try reflexivity; try assumption.
    2: { apply natgthtogeh. assumption. }
    apply funextfun; intros ?.
    rewrite (gauss_switch_row_inv0 mat); try reflexivity.
    { apply natlthtoneq. assumption. }
    apply natlthtoneq.
    refine (natlthlehtrans _ _ _ _ _).
    {apply lt. }
    apply (pr1 (pr2 (pr2 some))).
  Defined.

  Lemma gauss_clear_row_inv1
    {m n : nat} (mat : Matrix F m n) (p : n > 0) (row : ⟦ m ⟧%stn)
    : ∏ i_1 : ⟦ m ⟧%stn,
       (gauss_clear_row mat i_1) i_1 = const_vec 0%ring
    -> ∏ i_2 : ⟦ m ⟧%stn, i_1 < i_2
    -> mat i_2 = const_vec 0%ring.
  Proof.
    intros i_1 eqconst0 i_2 i1_lt_j2.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | gt]. { rewrite contr_eq in p.
      contradiction (isirreflnatgth _ p). }
    destruct (@select_uncleared_column _ _ _ mat i_1 gt) as [some | none];
      try destruct some as [piv_c some].
    2: { simpl; simpl in eqconst0.
         apply funextfun; intros j'; rewrite none; try assumption; try reflexivity.
         {apply natlthtoleh. unfold lower_left_zero in none. assumption. }
         apply (pr2 j').
    }
    simpl.
    revert eqconst0; simpl.
    rewrite gauss_clear_column_inv3.
    2: {apply isreflnatleh. }
    unfold gauss_clear_column_step'.
    unfold gauss_switch_row.
    rewrite (stn_eq_or_neq_left (idpath i_1)).
    simpl; intros.
    assert (eqz  : (λ j : (⟦ m ⟧)%stn, mat (pr1 (pr2 some)) piv_c) (i_2) = 0%ring).
    {rewrite (const_vec_eq _ 0%ring); try assumption; try reflexivity. }
    contradiction (pr1 (pr2 (pr2 (pr2 some)))).
  Defined.

  (* TODO this proof can be cleaned up considerably - many things are repeated,
     some perhaps not once but twice or more. *)
     Lemma gauss_clear_row_inv2
     { m n : nat } (mat : Matrix F m n) (p : n > 0)
     (row_sep : (⟦ S m ⟧%stn)) (p' : row_sep < m)
     :  is_row_echelon_partial_1 mat p
         (pr1 row_sep,, istransnatlth (pr1 row_sep) m (S m) (p') (natgthsnn m))
     -> is_row_echelon_partial_1 (gauss_clear_row mat (pr1 row_sep,, p')) p
         (S (pr1 row_sep),, p').
   Proof.
     intros H1.
     unfold is_row_echelon_partial_1 in *.
     unfold gauss_clear_rows_up_to.
     intros i_1 i_2 j_1 j_2 i1_lt H2.
     intros i1_lt_i2 j1_lt_j2.
     revert H2.
     unfold gauss_clear_row.
     clear p.
     destruct (natchoice0 n) as [contr_eq | p]. { apply fromstn0. rewrite contr_eq; assumption. }
     destruct (select_uncleared_column _ _) as [some | none]; simpl.
     2: { intros isle.
          destruct (natlehchoice i_1 (pr1 row_sep)) as [gt | eq]; try assumption.
          { rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption. }
          rewrite none; intros; try reflexivity; try assumption.
          2: {exact (pr2 (j_1)). }
          apply natgthtogeh.
          simpl.
          rewrite <- eq; assumption.
     }
     unfold exists_first_uncleared in some.
     intros is_le.
     rewrite gauss_clear_column_inv3 in is_le.
     2: { apply natlthsntoleh; assumption. }
     destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq]. { apply natlthsntoleh; assumption.  }
     { rewrite gauss_switch_row_inv0 in is_le.
        3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt (pr1 (pr2 (pr2 (pr2 some))))). }
        2: { apply natlthtoneq; assumption. }
        rewrite gauss_clear_column_inv6.
        { rewrite gauss_switch_row_inv2.
          - rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
          - rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
            rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
            refine (natlthlehtrans _ _ _ lt (pr1 (pr2 (pr2 (pr2 some))))).
        }
        rewrite gauss_switch_row_inv2.
          + rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
          + rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
            rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
            refine (natlthlehtrans _ _ _ lt (pr1 (pr2 (pr2 (pr2 some))))).
    }
    destruct (natgthorleh (pr1 some) j_1).
    { rewrite gauss_clear_column_inv6; try reflexivity; try assumption.
       
      - unfold gauss_switch_row.
        destruct (stn_eq_or_neq _ _) as [eq' | neq]; simpl.
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
          { rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption. 
            apply (pr1 (pr2 (pr2 (pr2 some)))). }
          rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption.
          apply (isreflnatleh).
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
        { rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption. 
          apply (pr1 (pr2 (pr2 (pr2 some)))). } 
          rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption.
          unfold stntonat in *; simpl.
          rewrite <- eq.
          apply natgthtogeh; assumption.
       - rewrite gauss_switch_row_inv2.  
         + rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption.
           apply isreflnatleh.
         + rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption.
           2: { apply isreflnatleh. }
           rewrite (pr2 (pr2 (pr2 (pr2 (pr2 some))))); try reflexivity; try assumption.
           apply (pr1 (pr2 (pr2 (pr2 some)))).
    }
    destruct (natlehchoice (pr1 some) j_1) as [gt | eq']; try assumption.
    2:
    { replace j_1 with (pr1 some).
      2: { rewrite (@subtypePath_prop _ _ _ _ eq'); reflexivity. }
      rewrite gauss_clear_column_inv7; try reflexivity; try assumption.
      - unfold gauss_switch_row.
        rewrite stn_eq_or_neq_refl; simpl.
        apply (pr1 (pr2 (pr2 (pr2 (pr2 some))))). 
      - exact (pr2 i_2).
      - unfold stntonat in *. simpl. rewrite <- eq; assumption.
    }
    contradiction (pr1 (pr2 (pr2 (pr2 (pr2 some))))).
    destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq']. { apply natlthsntoleh; assumption.  }
    - rewrite gauss_switch_row_inv0 in is_le.
      3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt (pr1 (pr2 (pr2 (pr2 some))))). }
      2: { apply natlthtoneq; assumption. }
      refine (H1 _ _ _ _ _ _ _ _).
      + apply lt.
      + apply is_le.
      + refine (natlthlehtrans _ _ _ lt (pr1 (pr2 (pr2 (pr2 some))))). 
      + refine (istransnatleh _  j1_lt_j2); assumption.
    - rewrite eq in *.
      assert (is_le' : is_leading_entry F (mat (pr1 (pr2 (pr2 some)))) j_2).
      { unfold is_leading_entry, gauss_switch_row in *.
        destruct (stn_eq_or_neq _ _) as [? | ?];
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl in is_le;
          try apply is_le.
        - simpl in contr_neq. rewrite <- eq in contr_neq; (contradiction (isirrefl_natneq _ contr_neq)).
        - simpl in contr_neq. rewrite <- eq in contr_neq; (contradiction (isirrefl_natneq _ contr_neq)).
      }
      unfold is_leading_entry in is_le'.
      rewrite (pr2 (is_le')); try reflexivity.
      refine (natlthlehtrans _ _ _ gt j1_lt_j2).
  Defined.

  (* TODO : is_row_echelon_partial_2  (gauss_clear_rows_up_to mat p row_sep) row_sep. *)
  Lemma gauss_clear_rows_up_to_inv0
    { m n : nat } (mat : Matrix F m n) (row_sep : (⟦ S m ⟧%stn)) (p : n > 0)
   : ∏ i_1 : ⟦ m ⟧%stn, i_1 < row_sep
  -> (gauss_clear_rows_up_to mat row_sep) i_1 = const_vec 0%ring
  -> ∏ i_2 : ⟦ m ⟧%stn, i_1 < i_2
  -> (gauss_clear_rows_up_to mat row_sep) i_2 = const_vec 0%ring.
  Proof.
    unfold is_row_echelon_partial_2.
    intros i_1 i1_lt_rowsep le_nought.
    unfold gauss_clear_rows_up_to in *.
    destruct row_sep as [row_sep lt].
    induction row_sep as [| row_sep IH]. {simpl. contradiction (negnatgth0n i_1 i1_lt_rowsep). }
    rename  i1_lt_rowsep into i1_lt_srowsep.
    set (lt' := (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) lt)).
    unfold gauss_clear_rows_up_to in *.
    rewrite nat_rect_step in *.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | gt]. { rewrite contr_eq in p.
      contradiction (isirreflnatgth _ p). }
    revert le_nought.
    destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq]. {apply natlthsntoleh. assumption. }
    - destruct (select_uncleared_column _ _) as [some | none].
      2: { intros; simpl;
           rewrite IH; try reflexivity; try assumption.
      }
      intros ? ? i1_lt_i2.
      unfold exists_first_uncleared in some.
      destruct (natgthorleh i_2 row_sep) as [i2_gt_rowsep | i2_le_rowsep].
      + rewrite gauss_switch_row_inv1 in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought. 2: { apply natlthtoleh. assumption. }
          rewrite gauss_clear_column_inv1; try assumption.
          2: {apply (pr2 i_2). }
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
          { contradiction (isirreflnatgth row_sep). rewrite contr_eq in *. assumption. }
          rewrite gauss_add_row_inv1; try assumption.
          -- rewrite gauss_switch_row_inv1.
             ++ rewrite IH; try assumption; try reflexivity.
             ++ rewrite IH; try reflexivity; try assumption.
                rewrite IH; try reflexivity; try assumption.
                apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
          -- rewrite gauss_switch_row_inv1; try reflexivity; try assumption.
             ++ rewrite IH; try assumption; try reflexivity.
             ++ rewrite IH; try assumption; try reflexivity.
                rewrite IH; try assumption; try reflexivity.
                apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh. assumption. }
          rewrite gauss_switch_row_inv0 in le_nought.
          3: { apply natlthtoneq.
               apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
          }
          2: { apply natlthtoneq. assumption. }
          rewrite IH; try assumption; try reflexivity.
          rewrite IH; try assumption; try reflexivity.
          apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
      + rewrite gauss_switch_row_inv1 in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natgthtogeh in i1_lt_i2. apply (istransnatleh i1_lt_i2 i2_le_rowsep). }
          rewrite gauss_clear_column_inv3; try assumption.
          rewrite gauss_switch_row_inv1; try assumption.
          -- rewrite IH; try assumption; try reflexivity.
          -- rewrite IH; try reflexivity; try assumption.
             rewrite IH; try reflexivity; try assumption.
             apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh in i1_lt_rowsep. assumption. }
          rewrite gauss_switch_row_inv0 in le_nought.
          3: { apply natlthtoneq.
               apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
          }
          2: {apply natlthtoneq.  apply (natlthlehtrans _ _ _ i1_lt_i2 i2_le_rowsep). }
          rewrite IH; try assumption; try reflexivity.
          rewrite IH; try assumption; try reflexivity.
          apply (natgehgthtrans _ _ _ (pr1 (pr2 (pr2 (pr2 (some))))) i1_lt_rowsep).
    - intros.
      unfold gauss_clear_row in *.
      destruct (select_uncleared_column _ _) as [col | no_col].
      2: { apply funextfun; intros j_2.
           assert (le : row_sep ≤ i_2). {apply natgthtogeh. rewrite <- eq. assumption. }
           apply no_col; try assumption.
           apply (pr2 j_2).
      }
      set (p' :=  (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) lt)).
      unfold leading_entry_compute in le_nought.
      (*contradiction (pr1 (pr2 (pr2 (pr2 (contr)))) ).*)
      contradiction (pr1 (pr2 (pr2 (pr2 (pr2 col)))) ).
      refine (const_vec_eq _ _ _ _).
      rewrite <- le_nought.
      unfold gauss_switch_row.
      rewrite gauss_clear_column_inv3.
      2: { rewrite eq. apply isreflnatleh. }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _).
      + destruct (stn_eq_or_neq _ _) as [? | contr_neq].
        2: { contradiction (nat_neq_to_nopath contr_neq). }
        reflexivity.
      + destruct (stn_eq_or_neq _ _) as [? | contr_neq].
        2: { contradiction (nat_neq_to_nopath contr_neq). }
        reflexivity.
  Defined.

  (* TODO clean this up *)
  Lemma gauss_clear_rows_up_to_inv1
    { m n : nat } (mat : Matrix F m n) (p : n > 0) (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to mat row_sep) p row_sep.
  Proof.
    pose ( H:= @gauss_clear_row_inv2).
    unfold gauss_clear_rows_up_to.
    destruct row_sep as [row_sep p''].
    induction row_sep.
    { simpl. intros ? ? ? ? contr.
      contradiction (negnatlthn0 n contr). }
    rewrite nat_rect_step.
    set (inner := nat_rect _ _ _ _).
    set (inner' := inner (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) p'')).
    set (rowstn := make_stn m row_sep p'').
    change row_sep with (pr1 rowstn).
    assert (lt' : row_sep < S m). {apply (istransnatlth _ _ _ (natgthsnn row_sep) p''). }
    set (H' := H m n inner' p (row_sep,, lt') p'').
    apply H'.
    change (pr1 (row_sep,, lt')) with row_sep.
    assert (eq : (istransnatlth row_sep m (S m) p'' (natgthsnn m))
                 = (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) p'')).
    { apply proofirrelevance. apply propproperty. }
    rewrite eq.
    apply IHrow_sep.
  Defined.

  Lemma gauss_clear_rows_up_to_inv2
    { m n : nat } (mat : Matrix F m n) (p : n > 0) (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_2
        (gauss_clear_rows_up_to mat row_sep) row_sep.
  Proof.
    pose ( H:= @gauss_clear_rows_up_to_inv0).
    unfold is_row_echelon_partial_2.
    unfold gauss_clear_rows_up_to in H.
    intro i_1; intros.
    rewrite <- (H _ _ _ row_sep p i_1 X X0 i_2); try assumption.
    destruct row_sep as [row_sep p''].
    reflexivity.
  Defined.

  Lemma is_row_echelon_1_eq
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to mat (m,, natgthsnn m)) p (m,, natgthsnn m)
    -> ∏ i_1 i_2 : ⟦ m ⟧%stn,
       ∏ j_1 j_2 : ⟦ n ⟧%stn,
       i_1 < i_2
    -> leading_entry_compute F (gauss_clear_rows_up_to mat (m,, natgthsnn m) i_1)
       = just j_1
    -> leading_entry_compute F (gauss_clear_rows_up_to mat (m,, natgthsnn m) i_2)
       = just j_2
    -> j_1 < j_2.
  Proof.
    unfold is_row_echelon_partial_1.
    intros H1.
    intros i_1 i_2 j_1 j_2 lt.
    destruct (natgthorleh j_2 j_1) as [gt | ?]. {intros; apply gt. }
    unfold leading_entry_compute; intros H2 H3.
    pose (H4 := @leading_entry_compute_internal_correct1 F n
                  _ (n,, natgthsnn n) _ H3).
    contradiction (pr1 H4).
    destruct (natlehchoice j_2 j_1) as [lt' | eq]. {assumption. }
    - rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity;
        try exact (pr2 i_1).
      apply leading_entry_compute_correct1; assumption.
    - rewrite  eq in *.
      rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity.
      {exact (pr2 i_1). }
      2: { rewrite eq; apply (isreflnatleh). }
      apply leading_entry_compute_correct1; assumption.
  Defined.

  Lemma gauss_clear_rows_up_to_inv3
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon
        (gauss_clear_rows_up_to mat (m,, natgthsnn m)).
  Proof.
    pose (H := @is_row_echelon_from_partial m _
      (gauss_clear_rows_up_to mat (m,, natgthsnn m)) p).
    apply H.
    unfold is_row_echelon_partial.
    use tpair.
    - apply gauss_clear_rows_up_to_inv1.
    - apply gauss_clear_rows_up_to_inv2; assumption.
  Defined.

  Lemma row_echelon_partial_to_upper_triangular_partial
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (iter : ⟦ S m ⟧%stn)
    : @is_row_echelon_partial m n mat p iter
   -> @is_upper_triangular_partial F m n iter mat.
  Proof.
    unfold is_row_echelon_partial, is_upper_triangular_partial.
    destruct iter as [iter p'].
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    induction iter as [| iter IH]. {simpl. intros ? ? ? ? contr. contradiction (nopathsfalsetotrue contr). }
    intros isre.
    destruct isre as [re_1 re_2].
    intros i j lt lt'.
    simpl in p'.
    assert (iter_lt_sn : iter < S m). {apply (istransnatlth _ _ _ p' (natgthsnn m)). }
    destruct (natlehchoice i iter) as [? | eq]. {apply natlthsntoleh; assumption. }
    - destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute F (mat i))) as [t | none].
      + destruct t as [t eq].
        rewrite (IH iter_lt_sn); try reflexivity; try assumption.
        use tpair.
        * intros i_1 i_2 j_1 j_2  i1_lt_iter H ? ?.
          rewrite (re_1 i_1 i_2 j_1 j_2); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
        * simpl.
          intros i_1 i_2 i1_lt_iter ? ?.
          rewrite (re_2 i_1 i_2); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
      + pose (H := @leading_entry_compute_internal_correct2 F n _ _ none).
        rewrite H; try reflexivity.
        exact (pr2 (dualelement j)).
    - unfold stntonat in eq.
      assert (eq' : i = (iter,,  p')).
      { apply subtypePath_prop; apply eq. }
      destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute F (mat i))) as [t | none].
      + destruct t as [t jst].
        destruct (natlthorgeh j t) as [j_lt_t | contr_gt].
        * pose (H := @leading_entry_compute_internal_correct1 F n _ (n,, natgthsnn n)  _ jst).
          rewrite (pr2 H); try reflexivity; try assumption.
        * pose (H1 := @leading_entry_compute_internal_correct1 F n _ (n,, natgthsnn n)  _ jst).
          destruct (natchoice0 i) as [contr0 | ?].
          { apply fromempty; refine  (negnatgth0n _ _). rewrite contr0. apply lt. }
          destruct (prev_stn i) as [u u_lt]; try assumption.
          destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute F (mat u))) as [prev | none_prev].
          -- destruct prev as [prev eq''].
             unfold leading_entry_compute in prev.
             pose (H2 := @leading_entry_compute_internal_correct1 F n _ (n,, natgthsnn n) _ eq'').
             contradiction (pr1 H2).
             rewrite (IH iter_lt_sn); try reflexivity; try assumption.
             use tpair.
             ** intros i_1 i_2 j_1 j_2 i1_lt_iter H' ? ?.
                rewrite (re_1 i_1 i_2 j_1 j_2); try assumption; try reflexivity.
                apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
             ** simpl.
                intros i_1 i_2 i1_lt_iter ? ?.
                rewrite (re_2 i_1 i_2); try assumption; try reflexivity.
                apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
             ** destruct (natgthorleh u prev); try assumption.
                contradiction (pr1 H1).
                rewrite (re_1 u i t prev); try assumption; try reflexivity; try assumption.
                --- apply natgehsntogth.
                    rewrite u_lt.
                    rewrite eq'.
                    apply natgehsnn.
                --- apply natgehsntogth.
                     rewrite u_lt.
                     rewrite eq'.
                     apply (isreflnatleh).
                --- destruct (natgthorleh t prev); try assumption.
                    apply (istransnatleh contr_gt).
                    refine (istransnatleh _ h0).
                    apply natlehsntolth.
                    apply natlthsntoleh.
                    rewrite u_lt.
                    apply lt.
             ** apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
            -- rewrite (re_2 u i ); try assumption; try reflexivity.
             ++ simpl; apply natlthtolths. rewrite <- eq.
                try apply (natlehlthtrans _ _ _ contr_gt lt ).
                apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
             ++ pose (H := @leading_entry_compute_internal_correct2 F n _ (n,, natgthsnn n) none_prev).
                apply funextfun; intros j'; rewrite (H j'); try reflexivity.
                exact (pr2 (dualelement j')).
             ++ try apply (natlehlthtrans _ _ _ contr_gt lt ).
                apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
      + pose (H := @leading_entry_compute_internal_correct2 F n _ _ none).
        rewrite H; try reflexivity.
        exact (pr2 (dualelement j)).
  Defined.

  Lemma row_echelon_to_upper_triangular
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    : @is_row_echelon m n mat
  -> @is_upper_triangular F m n mat.
  Proof.
    intros H.
    unfold is_upper_triangular.
    intros.
    rewrite (row_echelon_partial_to_upper_triangular_partial mat p (m,, natgthsnn m));
      try reflexivity; try assumption.
    2: {exact (pr2 i). }
    unfold is_row_echelon in H.
    unfold is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    use tpair.
    - intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite (H1 j_1 j_2); try assumption; reflexivity.
    - simpl.
      intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite H2; try assumption; reflexivity.
  Defined.

  (* TODO clear up... *)
  Lemma clear_column_eq_matrix_def { m n : nat } (iter : ⟦ S m ⟧%stn)
     (k_i : (⟦ m ⟧%stn)) (k_j : (⟦ n ⟧%stn)) (mat : Matrix F m n) :
     ((gauss_clear_column_as_left_matrix iter mat k_i k_j) ** mat )
   =  gauss_clear_column mat k_i k_j iter.
  Proof.
    intros.
    (* rewrite <- gauss_clear_column_eq'. *)
    destruct iter as [iter p].
    assert (p' : m > 0).
    { apply stn_implies_ngt0; assumption. }
    induction iter as [| iter IH]; try apply matlunax2.
    - unfold gauss_clear_column.
      unfold gauss_clear_column in IH.
      unfold gauss_clear_column_as_left_matrix.
      unfold gauss_clear_column_as_left_matrix in IH.
      rewrite nat_rect_step.
      rewrite nat_rect_step.
      rewrite  gauss_clear_column_step_eq.
      destruct (natgthorleh iter k_i).
      2: { rewrite matlunax2.
           rewrite IH.
           induction iter as [| iter IH'].
           - simpl. apply idpath.
           - rewrite nat_rect_step.
             destruct (natgthorleh iter k_i).
             + apply natgehsntogth in h.
               apply fromempty. apply (isasymmnatgth _ _  h h0).
             + reflexivity.
      }
      rewrite matrix_mult_assoc.
      rewrite <- IH.
      set (x := nat_rect _ _ _ _).
      try rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _) as [eq | neq].
      { apply fromempty. apply neggth_logeq_leh in h; try assumption.
        rewrite <- eq. apply isreflnatgeh.  }
      rewrite add_row_mat_elementary.
      2 : {apply issymm_natneq. apply natgthtoneq. assumption. }
      apply pathsinv0.
      apply maponpaths.
      etrans.
      { unfold x.
        set (x' := ((nat_rect _ _ _ ) iter )).
        set (x'' := x' (istransnatlth iter (S iter) (S m) (natgthsnn iter) p)).
        replace (fldmultinv' (@matrix_mult F _  _ x'' _ mat k_i k_j)%ring)
          with (fldmultinv' (mat k_i k_j)%ring).
        - reflexivity.
        - clear IH; induction iter as [| iter IH'].
          {apply fromempty. apply  negnatgth0n in h; assumption. }
          unfold x'', x'.
          rewrite nat_rect_step.
          destruct (natgthorleh iter _).
          2 : {rewrite matlunax2.
               set (f := @gauss_clear_column_as_left_matrix_inv0 m ).
               unfold gauss_clear_column_as_left_matrix in f.
               symmetry.
               assert (obv: S iter < S m). { apply (istransnatlth _ _ _ p (natgthsnn (S m)) ). }
               set (f' := @gauss_clear_column_as_left_matrix_inv1 m).
               unfold gauss_clear_column_as_left_matrix in f'.
               pose (f'' := f' _ (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
                  (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))
                  mat k_i k_j k_i (isreflnatleh k_i)).
               rewrite f''.
               reflexivity.
          }
          set (f := @gauss_clear_column_as_left_matrix_inv1 m n).
          unfold gauss_clear_column_as_left_matrix in f.
          assert (obv: S iter < S m). { apply (istransnatlth _ _ _ p (natgthsnn (S m)) ). }
          rewrite (IH' obv); try assumption.
          2: {apply natgthtoneq. assumption. }
          pose (f' := f (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter) obv))).
          rewrite f'. 2: {apply isreflnatleh. }
          rewrite matrix_mult_assoc.
          rewrite add_row_mat_elementary. 2: {apply issymm_natneq. apply natgthtoneq; assumption. }
          rewrite gauss_add_row_inv0.
          (*3: { apply natgthtoneq; assumption.  } *)
          2: { apply natgthtoneq. assumption. }
          clear f'.
          set (f' := @gauss_clear_column_as_left_matrix_inv1 m n).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
          (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))
            mat k_i k_j k_i (isreflnatleh k_i)).
          rewrite f''.
          reflexivity.
      }
      induction iter as [| iter IH'].
      + {apply fromempty. apply negnatgth0n in h. assumption. }
      + unfold x.
        rewrite nat_rect_step.
        destruct (natgthorleh _ _) as [eq | neq'].
        2: {rewrite matlunax2.
          set (f' := @gauss_clear_column_as_left_matrix_inv0 m n).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
          (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))).
          rewrite f''; try reflexivity.
          apply natlehnsn.
        }
        rewrite matrix_mult_assoc.
        rewrite add_row_mat_elementary.
        2: {apply natgthtoneq in eq. apply issymm_natneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply issymm_natneq.
            apply natgthtoneq.
            apply natgthsnn. }
        unfold x in IH.
        set (f := @gauss_clear_column_as_left_matrix_inv0 m n).
        unfold gauss_clear_column_as_left_matrix  in f.
        set (f' := @gauss_clear_column_as_left_matrix_inv0 m n).
        unfold gauss_clear_column_as_left_matrix in f'.
        pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
        (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))).
        rewrite f''; try apply idpath.
        apply natlehnsn.
  Defined.

  Lemma clear_row_eq_matrix_def { m n : nat }
     (mat : Matrix F m n) (r : ⟦ m ⟧%stn) (p : n > 0):
     ((gauss_clear_row_as_left_matrix mat r p) ** mat )
   =  gauss_clear_row mat r.
  Proof.
    intros.
    unfold gauss_clear_row, gauss_clear_row_as_left_matrix.
    destruct (natchoice0 n) as [contr_eq | gt].
    { apply fromempty. rewrite contr_eq in p. contradiction (isirreflnatgth _ p). }
    assert (eq : forall m n : nat, m < n -> n > m).
    {intros. assumption. }
    assert (eq' : p = gt).
    { apply propproperty. }
    rewrite eq'.
    destruct ((select_uncleared_column F mat r _)).
    2: {apply matlunax2. }
    rewrite matrix_mult_assoc.
    rewrite switch_row_mat_elementary.
    rewrite clear_column_eq_matrix_def.
    reflexivity.
  Defined.

  Lemma gauss_clear_rows_up_to_as_matrix_eq  { m n : nat } (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (p : n > 0) :
    ((@clear_rows_up_to_as_left_matrix_internal m n mat iter p) ** mat)
      = (gauss_clear_rows_up_to mat iter).
  Proof.
    intros.
    unfold clear_rows_up_to_as_left_matrix,
           gauss_clear_rows_up_to,
           clear_rows_up_to_as_left_matrix_internal,
           gauss_clear_rows_up_to.
    destruct iter as [iter p'].
    induction iter as [| iter IH ]. {simpl. rewrite matlunax2. apply idpath. }
    do 2 rewrite nat_rect_step.
    rewrite <- IH.
    pose (@clear_row_eq_matrix_def m n mat (iter,, p') p).
    rewrite <- (clear_row_eq_matrix_def _ _ p).
    rewrite <- matrix_mult_assoc.
    rewrite IH.
    reflexivity.
  Defined.

  Lemma gauss_clear_rows_up_to_matrix_invertible { m n : nat } (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (p : n > 0) :
    (@matrix_inverse F m (@clear_rows_up_to_as_left_matrix m n mat iter p)).
  Proof.
    destruct iter as [iter lt].
    induction iter as [| iter IH].
    { unfold clear_rows_up_to_as_left_matrix,
             clear_rows_up_to_as_left_matrix_internal.
      simpl; apply identity_matrix_is_inv. }
    unfold clear_rows_up_to_as_left_matrix,
    clear_rows_up_to_as_left_matrix_internal.
    rewrite nat_rect_step.
    apply inv_matrix_prod_is_inv.
    - apply clear_row_matrix_invertible.
    - apply IH.
  Defined.

  Local Definition flip_fld_bin
    (e : F) : F.
  Proof.
    destruct (fldchoice0 e).
    - exact 1%ring.
    - exact 0%ring.
  Defined.

  Local Definition flip_fld_bin_vec
    {n : nat} (v : Vector F n) := λ i : (stn n), flip_fld_bin (v i).

  Definition diagonal_all_nonzero_compute
    {n : nat} (v : Vector F n)
    : coprod (forall j : (stn n), (v j) != 0%ring)
             (∑ i : (stn n), (v i) = 0%ring).
  Proof.
    pose (H1 := leading_entry_compute F (flip_fld_bin_vec v)).
    destruct (@maybe_stn_choice F n H1) as [some | none].
    - right.
      use tpair. {apply some. }
      simpl.
      pose (H2 := @leading_entry_compute_internal_correct1
        F _ (flip_fld_bin_vec v) (n,, natgthsnn n) _ (pr2 some)).
      destruct H2 as [H2 H3].
      unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in *.
      destruct (fldchoice0 (v (pr1 some))).
      2: { contradiction. }
      assumption.
    - left.
      intros j.
      pose (H3 := @leading_entry_compute_internal_correct2
        F _ (flip_fld_bin_vec v) (n,, natgthsnn n ) none j).
      rewrite <- H3; try apply (pr2 (dualelement j)).
      clear H3.
      destruct (fldchoice0 (v j)) as [eq | neq];
        unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in *.
      + destruct (fldchoice0 _); try assumption.
        rewrite eq.
        intros contr_neq.
        contradiction (nonzeroax _ (pathsinv0 contr_neq)).
      + destruct (fldchoice0 (v j)) as [contr_eq | ?]; try assumption.
        rewrite contr_eq in neq; contradiction.
  Defined.

  Lemma gaussian_elimination_inv0 {m n : nat} {A : Matrix F m n}
  : ∑ (A' : Matrix F m m), (@matrix_inverse F m A') × (@is_row_echelon m n (A' ** A)).
  Proof.
    destruct (natchoice0 n) as [eq0 | gt].
    { use tpair; try assumption.
      - apply (@identity_matrix F m).
      - simpl.
        use tpair.
        + apply identity_matrix_is_inv.
        + simpl.
          rewrite matlunax2.
          unfold is_row_echelon. intros i j.
          use tpair.
          * intros ?. apply fromstn0. rewrite eq0. assumption.
          * intros ?. intros lt.
            unfold const_vec.
            apply funextfun; intros ?.
            apply fromstn0. rewrite eq0. assumption.
    }
    use tpair.
    - exact (@clear_rows_up_to_as_left_matrix m n A (m,, natgthsnn m) gt).
    - simpl.
      use tpair.
      + apply gauss_clear_rows_up_to_matrix_invertible.
      + simpl.
        rewrite gauss_clear_rows_up_to_as_matrix_eq; try assumption.
        pose (H2 := @gauss_clear_rows_up_to_inv3 m n A gt (m,, natgthsnn m)).
        apply H2; assumption.
  Defined.

End Gauss.


Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.
  Local Notation Σ := (iterop_fun 0%hz op1).


  Local Notation "A ** B" := (@matrix_mult hz _ _ A _ B) (at level 80).

  (* Such code might go intro Matrix.v *)
  Definition is_smithnf { m n : nat } (A : Matrix I m n) :
    ∑ (S : Matrix I m m), ∑ (T : Matrix I n n),
    @is_diagonal I m n (S ** A ** T) ×
    ∏ (i j : ⟦ min n m ⟧%stn), i < j ->
    hzdiv (A (minabstn_to_bstn i) (minabstn_to_astn i))
    (A (minabstn_to_bstn j) (minabstn_to_astn i)).
  Abort.

  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.


End SmithNF.


Section SmithNFOps.


End SmithNFOps.


Section SmithNFAlgs.

End SmithNFAlgs.
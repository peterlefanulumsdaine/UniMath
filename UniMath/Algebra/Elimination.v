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
Require Import UniMath.NumberSystems.RationalNumbers.

Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Tactics.Nat_Tactics.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.PAdics.z_mod_p.

(*Local Definition R := pr1hSet natcommrig.*)
Context { R : rig }.
Local Definition F := hq.

(* The first few sections contain Definitions and Lemmas that
   should be moved further up the project tree *)



Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation  Σ := (iterop_fun 0%hq op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).


Section Misc.

  Definition min' (n m : nat) : nat.
  Proof.
    induction (natgtb n m).
    - exact m.
    - exact n.
  Defined.

End Misc.


Section PrelStn.

 (* TODO: look for other places this can simplify proofs! and upstream? *)
  Lemma stn_neq_or_neq_refl {n} {i : ⟦ n ⟧%stn} : stn_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    unfold stn_eq_or_neq.

    destruct (nat_eq_or_neq i i).
    2 : {admit. } (* i ≠ i, i in stn*)
    rewrite coprod_rect_compute_1.
    apply maponpaths.
    (* Why can't we use e.g. unitl3 ? *)
    remember p as p'. clear Heqp'.
    apply subtypePath_prop in p.
    set (fst := pr1 i).
    assert (X : fst = fst). { apply idpath. }
    assert (X = p').
  Admitted.

   (* TODO: naming ? upstream?  Certainly rename p, p0. *)
  Lemma stn_eq_or_neq_left : ∏ {n : nat} {i j: (⟦ n ⟧)%stn} (p : (i = j)),
                              stn_eq_or_neq i j = inl p.
  Proof.
    intros ? ? ? p. rewrite p. apply stn_neq_or_neq_refl.
  Defined.

  Lemma stn_eq_or_neq_right : ∏ {n : nat} {i j : (⟦ n ⟧)%stn} (p : (i ≠ j)),
    stn_eq_or_neq i j = inr p.
  Proof.
    intros ? ? ? p. unfold stn_eq_or_neq.
    destruct (nat_eq_or_neq i j).
    - apply fromempty. rewrite p0 in p.
       apply isirrefl_natneq in p.
       assumption.
    -  apply isapropcoprod.
       + apply stn_ne_iff_neq in p. apply isdecpropfromneg.  assumption.
       (*apply stn_ne_iff_neq in p.*)
       + apply negProp_to_isaprop.
       + intros i_eq_j.
         rewrite i_eq_j in p.
         apply isirrefl_natneq in p.
         apply fromempty. assumption.
  Defined.

  Local Definition truncate_pr1 { n : nat } ( f : ⟦ n ⟧%stn → hq) ( k : ⟦ n ⟧%stn ) : ( ⟦ n ⟧%stn → hq).
  Proof.
    intros.
    induction (natgtb X k).
    - exact (f X).
    - exact (f k).
  Defined.

  Lemma stn_implies_nneq0 { n : nat } (i : ⟦ n ⟧%stn) : n ≠ 0.
  Proof.
    induction (natchoice0 n) as [T | F].
    - rewrite <- T in i.
      apply weqstn0toempty in i. apply fromempty. assumption.
    - change (0 < n) with (n > 0) in F.
      destruct n.
      + apply isirreflnatgth in F. apply fromempty. assumption.
      + apply natgthtoneq in F. reflexivity.
  Defined.

  Lemma stn_implies_ngt0 { n : nat} (i : ⟦ n ⟧%stn) : n > 0.
  Proof.
    exact (natneq0to0lth n (stn_implies_nneq0 i)).
  Defined.

  Definition decrement_stn_by_m { n : nat } ( i : (⟦ n ⟧)%stn ) (m : nat) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgehchoice m 0).
    - assert ( p :  ((pr1 i) - m) < n).
        {  unfold stn in i. set (p0 := pr2 i). assert (pr1 i < n).
           - exact (pr2 i).
           - assert ((pr1 i - m <= ( pr1 i))). {apply (natminuslehn ). }
              apply (natlehlthtrans (pr1 i - m) (pr1 i) ).
              + assumption.
              + assumption.
        }
      exact (pr1 i - m,, p).
    - exact i.
    - reflexivity.
  Defined.

  Local Definition mltntommin1ltn { n m : nat } (p : m < n) : (m - 1 < n).
  Proof.
    apply natlthtolthm1. assumption.
  Defined.


  Definition set_stn_vector_el { n : nat } (vec : Vector (⟦ n ⟧%stn) n) (idx : ⟦ n ⟧%stn) (el : (⟦ n ⟧%stn)) : Vector (⟦ n ⟧%stn) n.
  Proof.
  intros i.
  induction (stn_eq_or_neq i idx).
  + exact el.
  + exact (vec i).
  Defined.

  Definition nat_lt_minmn_to_stnm_stnn {m n : nat} (i : nat) (p : i < min' m n) : ⟦ m ⟧%stn × ⟦ n ⟧%stn.
  Proof.
   (* unfold min in p. *)
    assert (min n n = n).
      { unfold min.  induction n. reflexivity. unfold natgtb. destruct n. { reflexivity. }

    assert (i < n).
    (* cbn in p. *)
    induction (natgehchoice m n) as [MGT | NGE].
      - unfold min in p.

  Abort.

  (*
  Definition decrement_stn_by_m { n : nat } ( i : (⟦ n ⟧)%stn ) (m : nat) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgehchoice m 0).
    - assert ( p :  ((pr1 i) - m) < n).
        {  unfold stn in i. set (p0 := pr2 i). assert (pr1 i < n).
           - exact (pr2 i).
           - assert ((pr1 i - m <= ( pr1 i))). {apply (natminuslehn ). }
              apply (natlehlthtrans (pr1 i - m) (pr1 i) ).
              + assumption.
              + assumption.
        }
      exact (pr1 i - m,, p).
    - exact i.
    - reflexivity.
  Defined.
  *)

  Definition stnn_to_stn_sminusn1 { n : nat } ( i : (⟦ n ⟧)%stn ) : ((⟦ S (n - 1) ⟧)%stn).
  Proof.
    intros.
    induction (natgehchoice n 0).
    3 : { exact (natgehn0 n). }
    2 : { apply stn_implies_ngt0 in i.
          apply natgthtoneq in i.
          rewrite b in i.
          contradiction i.
    }
    assert (e : n = S (n - 1)). (* Small proof taken verbatim from stnsum. *)
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0. apply minusplusnmm. assumption.
    }
    rewrite <- e.
    assumption.
  Defined.

  (* TODO this should just be a matter of rewriting using above ? *)
  Definition stn_sminusn1_to_stnn { n : nat }  (i : (⟦ S (n - 1) ⟧)%stn) (p : n > 0) : (⟦ n ⟧%stn).
  Proof.
    intros.
    induction (natgehchoice (S (n - 1)) 0). (*(natgehchoice (S (n - 1)) 0). *)
      3 : { exact (natgehn0 n ). }
      2 : { rewrite b in i.
            apply (stn_implies_ngt0) in i.
            apply isirreflnatgth in i.
            apply fromempty. assumption.
      }
    assert (e : n = S (n - 1)). (* Small proof taken verbatim from stnsum. *)
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0. rewrite minusplusnmm.
      - apply idpath.
      - apply p. }
    rewrite <- e in i.
    assumption.
  Defined.


End PrelStn.


Section Matrices.


  Context { R : rig }.

  Definition matunel2 { n : nat } := @identity_matrix R n.

  Local Notation  Σ := (iterop_fun rigunel1 op1).


  (* Identical to transport_stnsum but with Σ , R*)
  Lemma transport_rigsum {m n : nat} (e: m = n) (g: ⟦ n ⟧%stn -> R) :
     Σ g =  Σ (λ i, g (transportf stn e i)).
  Proof.
    intros.
    induction e.
    apply idpath.
  Defined.


  (* Is there some tactical way to re-use previous proofs
     with a few changes? *)
  Lemma rigsum_eq {n : nat} (f g : ⟦ n ⟧%stn -> R) : f ~ g ->  Σ f =  Σ g.
  Proof.
    intros h.
    induction n as [|n IH].
    - apply idpath.
    - rewrite 2? iterop_fun_step. 2: { apply riglunax1. }
                                  2: { apply riglunax1. }
      induction (h lastelement).
      apply (maponpaths (λ i, op1 i (f lastelement))).
      apply IH.
      intro x.
      apply h.
  Defined.

  Lemma rigsum_step {n : nat} (f : ⟦ S n ⟧%stn -> R) :
    Σ f = op1 (Σ (f ∘ (dni lastelement))) (f lastelement).
  Proof.
    intros.
    apply iterop_fun_step.
    apply riglunax1.
  Defined.


  Lemma rigsum_left_right :
  ∏ (m n : nat) (f : (⟦ m + n ⟧)%stn → R),
   Σ f =  op1 (Σ (f ∘ stn_left m n)) (Σ (f ∘ stn_right m n)).
  Proof.
    intros.
    induction n as [| n IHn].
    (*unfold stn_left. unfold stn_right.*)
    { change (Σ  _) with (@rigunel1 R) at 3.
      set (a := m + 0). assert (a = m). { apply natplusr0. } (* In the stnsum case,
                                                                this can affect ⟦ m ⟧
                                                                and zeroes elsewhere *)
      assert (e := ! natplusr0 m).
      rewrite (transport_rigsum e).
      unfold funcomp.
      rewrite  rigrunax1.
      apply maponpaths. apply pathsinv0.
      apply funextfun. intros i.
      rewrite <- stn_left_0.
      reflexivity.
    }
    rewrite rigsum_step.
    assert (e : S (m + n) = m + S n).
    { apply pathsinv0. apply natplusnsm. }
    rewrite (transport_rigsum e).
    rewrite rigsum_step.
    rewrite <- rigassoc1. apply map_on_two_paths.
    { rewrite IHn; clear IHn. apply map_on_two_paths.
      { apply rigsum_eq; intro i. unfold funcomp.
        apply maponpaths. apply subtypePath_prop.
        rewrite stn_left_compute. induction e.
        rewrite idpath_transportf. rewrite dni_last.
        apply idpath. }
      { apply rigsum_eq; intro i. unfold funcomp.
        apply maponpaths. apply subtypePath_prop.
        rewrite stn_right_compute. unfold stntonat. induction e.   (* we have stn_right instead of stn_left? *)
        rewrite idpath_transportf. rewrite 2? dni_last.
        apply idpath. } }
    unfold funcomp. apply maponpaths. apply subtypePath_prop.
    induction e. apply idpath.
  Defined.

  (* stnsum_dni with
     stnsum -> Σ
     transport_stnsum -> transport_rigsum
     stnsum_left_right -> rigsum_left_right
     natplusassoc -> rigassoc1*)
  Lemma rigsum_dni {n : nat} (f : ⟦ S n ⟧%stn -> R) (j : ⟦ S n ⟧%stn ) :
    Σ f = op1 (Σ (f ∘ dni j)) (f j).
Proof.
  intros.
  induction j as [j J].
  assert (e2 : j + (n - j) = n).
  { rewrite natpluscomm. apply minusplusnmm. apply natlthsntoleh. exact J. }
  assert (e : (S j) + (n - j) = S n).
  { change (S j + (n - j)) with (S (j + (n - j))). apply maponpaths. exact e2. }
  intermediate_path (Σ  (λ i, f (transportf stn e i))).
  - apply (transport_rigsum e).
  - rewrite (rigsum_left_right (S j) (n - j)); unfold funcomp.
    apply pathsinv0. rewrite (transport_rigsum e2).
    rewrite (rigsum_left_right j (n-j)); unfold funcomp.
    rewrite (rigsum_step (λ x, f (transportf stn e _))); unfold funcomp.
    apply pathsinv0.
    rewrite rigassoc1. rewrite (@rigcomm1 R (f _) ). rewrite  <- rigassoc1. (* natpluss to @ R ... *)
    apply map_on_two_paths.
    + apply map_on_two_paths.
      * apply rigsum_eq; intro i. induction i as [i I].
        apply maponpaths. apply subtypePath_prop.
        induction e. rewrite idpath_transportf. rewrite stn_left_compute.
        unfold dni,di, stntonat; simpl.
        induction (natlthorgeh i j) as [R'|R'].
        -- unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [a|b].
           ++ apply idpath.
           ++ contradicts R' (natlehneggth b).
        -- unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [V|V].
           ++ contradicts I (natlehneggth R').
           ++ apply idpath.
      * apply rigsum_eq; intro i. induction i as [i I]. apply maponpaths.
        unfold dni,di, stn_right, stntonat; repeat rewrite transport_stn; simpl.
        induction (natlthorgeh (j+i) j) as [X|X].
        -- contradicts (negnatlthplusnmn j i) X.
        -- apply subtypePath_prop. simpl. apply idpath.
    + apply maponpaths.
      rewrite transport_stn; simpl.
      apply subtypePath_prop.
      apply idpath.
Defined.


(* Should be n not S n *)
  Lemma pulse_function_sums_to_point_rig { n : nat }  (f : ⟦ S n ⟧%stn -> R) :
  ∏ (i : ⟦ S n ⟧%stn ), (∏ (j : ⟦ S n ⟧%stn), ((i ≠ j) -> (f j = 0%rig))) ->  (Σ f = f i).
  Proof.
    intros i j.  (*impj0.*)
    rewrite (rigsum_dni f i).
    rewrite zero_function_sums_to_zero. (* TODO rephrase in terms of stnsum_const *)
    { rewrite riglunax1. apply idpath. }
    apply funextfun.
    intros k.
    unfold funcomp.

    replace (const_vec 0%rig k) with (@rigunel1 R). 2: { reflexivity. }
    assert (i_neq_dni : i ≠ dni i k) . {exact (dni_neq_i i k). }
    - intros. destruct (stn_eq_or_neq i (dni i k) ).
        + apply (stnneq_iff_nopath i (dni i k)) in p.
          apply weqtoempty. intros. apply p. assumption.
          exact (dni_neq_i i k). (* Move up *)
        + apply j. exact h.
  Defined.


(* TODO: possibly write special case [v ∧ (pulse j a) = a * (v j)]. *)

  Definition is_pulse_function { n : nat } ( i : ⟦ n ⟧%stn )  (f : ⟦ n ⟧%stn -> R) :=
   ∏ (j: ⟦ n ⟧%stn), (i ≠ j) -> (f j = 0%rig).
    (*(∏ (j : ⟦ n ⟧%stn), ((i ≠ j) -> (f j = 0%rig))) ->  (Σ f = f i).*) (* TODO : use us this one ?) *)

  Lemma stn_inhabited_implies_succ {n:nat} (i : ⟦ n ⟧%stn)
    : ∑ m, n = S m.
  Proof.
    destruct n as [ | m].
    - destruct i as [i le_i_0].
      destruct (nopathsfalsetotrue le_i_0).
    - exists m. apply idpath.
  Defined.

  Lemma pulse_function_sums_to_point_rig' { n : nat } ( i : ⟦ n ⟧%stn ) {f : ⟦ n ⟧%stn -> R}
    (p : is_pulse_function i f) : (Σ f = f i).
  Proof.
    destruct (stn_inhabited_implies_succ i) as [n' e_n_Sn'].
    destruct (!e_n_Sn').
    apply pulse_function_sums_to_point_rig.
    assumption.
  Defined.

  (* ~ point of interest ~ *)
  Lemma pulse_function_sums_to_point_rig'' { n : nat }  (f : ⟦ n ⟧%stn -> R) (p : n > 0) :
  ∏ (i : ⟦ n ⟧%stn ),  (∏ (j : ⟦ n ⟧%stn), ((i ≠ j) -> (f j = 0%rig))) ->  (Σ f = f i).
  Proof.
    intros i.
    destruct (stn_inhabited_implies_succ i) as [n' e_n_Sn'].
    destruct (!e_n_Sn').
    apply pulse_function_sums_to_point_rig.
  Defined.

  (* TODO: upstream - Vector equivalent of drop_el for "vecs"? *)
  Definition drop_el_vector { n : nat } (f : ⟦ S n ⟧%stn -> R) (i : ⟦ S n ⟧%stn) :
    ⟦ n ⟧%stn -> R.
  Proof.
    intros X.
    induction (natlthorgeh X i) as [X_le_i | X_geq_i].
    - assert (e : X < S n ).
      { set (p := pr2 X).
        apply (istransnatgth (S n) n X (natgthsnn n) (pr2 X)).
      }
      exact (f ((pr1  X),, e)).

    - assert (e :S ( X ) < S n ).
      { set (p := pr2 X).
        apply p. }
      exact (f (S X,, e)).
  Defined.

  (* Used to be in PAdics *)
  Lemma minussn1 ( n : nat ) : ( S n ) - 1 ≥ n.
  Proof.
    intros. destruct n. apply idpath.
    assert (e : (S (S n)) > (S n)).
    { apply natgthsnn. }
    apply natgthtogehm1 in e. assumption.
  Defined.


  (* TODO : This proof is a shambles ! And should be covered by inhabited lemma above. *)
  Definition drop_idx_vector { n : nat } ( i : ⟦ S n ⟧%stn ) ( drop : ⟦ S n ⟧%stn ) (p : n > 0) :
    ⟦ n ⟧%stn.
  Proof.
    intros.
    induction (natlthorgeh i drop) as [i_le_drop | i_geq_drop].
    - assert (e: drop ≤ n).
      { apply (pr2 drop). }
      assert (e': i < n). {
        apply (natlthlehtrans i drop (n) ).
        + assumption.
        + assumption. }
      exact (pr1 i,, e').
    -
      assert (e: (pr1 i) < S n). {exact (pr2 i). }
      assert ((pr1 i) - 1 < n). {
      apply natltminus1 in e.
      change (S n) with (1 + n) in e.
      replace (1 + n - 1) with (n + 1 - 1) in e.
      2: { rewrite plusminusnmm. rewrite natpluscomm.
           rewrite plusminusnmm. reflexivity.
      }
      rewrite plusminusnmm in e.
      assert ( e': (pr1 i < n + 1)).
      { intros.
        apply natlehtolthsn  in e.
        rewrite natpluscomm.
        change (1 + n) with (S n).
        assumption.
      }

      induction (natlthorgeh (pr1 i) n) as [i_le_n | i_geq_n].
      + apply natlthtolthm1 in i_le_n. assumption.
      +
      - apply natlthp1toleh  in e'.
        apply (isantisymmnatgeh) in e'.
        2 : {assumption. }
        symmetry in e'.
        rewrite e'.
        rewrite <- e'.
        apply natminuslthn.
        { assumption. }
        reflexivity.
      }
      exact (i - 1,, X).
  Defined.


  (* TODO: standardize name according to conventions *)
  (* And clean up the shambles proof ...*)
  Lemma nlesn_to_nminus1_len { n m : nat} (e : m < S n) (p : n > 0) : m - 1 < n.
  Proof.
    intros.
      apply natltminus1 in e.
      change (S n) with (1 + n) in e.
      replace (1 + n - 1) with (n + 1 - 1) in e.
      2: { rewrite plusminusnmm. rewrite natpluscomm.
           rewrite plusminusnmm. reflexivity.
      }
      rewrite plusminusnmm in e.
      assert ( e': (m < n + 1)).
      { intros.
        apply natlehtolthsn  in e.
        rewrite natpluscomm.
        change (1 + n) with (S n).
        assumption.
      }

      induction (natlthorgeh (m) n) as [i_le_n | i_geq_n].
      + apply natlthtolthm1 in i_le_n. assumption.
      +
      - apply natlthp1toleh  in e'.
        apply (isantisymmnatgeh) in e'.
        2 : {assumption. }
        symmetry in e'.
        rewrite e'.
        rewrite <- e'.
        apply natminuslthn.
        { assumption. }
        reflexivity.
  Defined.

  Lemma dnisum_dropsum : ∏ (n : nat) (f : (⟦ S n ⟧)%stn → R) (j : (⟦ S n ⟧)%stn),
                         Σ ((drop_el_vector f j)) = Σ ((f ∘ (dni j) )).
  Proof.
    intros.
    apply maponpaths.
    unfold funcomp, dni, di.  unfold drop_el_vector.
    apply funextfun. intros k.
    destruct (natlthorgeh k j).
    - do 2 rewrite coprod_rect_compute_1.
      unfold natgthtogths.
      apply maponpaths.
      reflexivity.
    - do 2 rewrite coprod_rect_compute_2.
      apply idpath.
  Defined.

  Lemma rigsum_drop_el : ∏ (n : nat) (f : (⟦ S n ⟧)%stn → R) (j : (⟦ S n ⟧)%stn),
    Σ f = (Σ ((drop_el_vector f j)) + f j)%ring.
  Proof.
    intros.
    rewrite (rigsum_dni f j).
    rewrite dnisum_dropsum.
    apply idpath.
  Defined.

  (* TODO Is that eq or weq? *)
  Lemma empty_sum_eq_0  (v1 : Vector R 0) : Σ v1 = 0%rig.
  Proof.
    apply zero_function_sums_to_zero.
    apply funextfun. intros i.
    apply fromempty. apply weqstn0toempty.
    assumption.
  Defined.

  Lemma sum_pointwise_op1 { n : nat } (v1 v2 : Vector R n) : Σ (pointwise n op1 v1 v2) = (Σ v1 + Σ v2)%rig.
  Proof.
    unfold "^".
    induction n.
    - rewrite zero_function_sums_to_zero.
      + assert (p1: Σ v1 = 0%rig). { apply (empty_sum_eq_0 v1). }
        assert (p2: Σ v2 = 0%rig). { apply (empty_sum_eq_0 v2). }
        rewrite p1, p2.
        rewrite riglunax1. apply idpath.
      + unfold const_vec.
        apply funextfun. intros i.
        apply fromempty. apply weqstn0toempty in i.
        assumption.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      unfold funcomp. rewrite replace_dni_last.
      rewrite <- rigassoc1.
      rewrite eqlen_vec_sums_mergeable. (* todo not the best name*)
      rewrite (rigassoc1 R _ _  (v1 _) ).
      rewrite <- (rigcomm1 _ (v1 _)).
      rewrite (rigassoc1 R _ _ (v2 _)).
      rewrite  (rigassoc1 R (v1 _ ) _ _).
      rewrite <- (rigassoc1 R _ (v1 _) _).
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      unfold funcomp.
      rewrite replace_dni_last.
      reflexivity.
  Defined.

  Lemma idrow_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn) :
    Σ (@identity_matrix R n i) = 1%rig.
  Proof.
    assert (p : n > 0). {destruct n.       (* TODO once not everywhere *)
                         - apply weqstn0toempty in i.
                           contradiction.
                         - apply natgthsn0. }

    rewrite (pulse_function_sums_to_point_rig'' _ p i). (*TODO less versions of this, remove rig in name *)
                                                        (* and p should be obtained inside pf sums... *)
    - unfold identity_matrix.
      rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
      apply idpath.
    - unfold identity_matrix.
      intros ? i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      apply idpath.
  Defined.

    (* factored approach:
       lemma that ∑ (v1 ^ v2) = ∑ v1 + ∑ v2
       lemma for ∑ (a ^ v) = a * ∑ v
       lemma that ∑ (standard_basis_vector n i) = 1
     (where (standard_basis_vector n i) = (identity_matrix i)) *)
  Lemma two_pulse_function_sums_to_point_rig { n : nat }
        (* TODO: can we use “n” not “S n” *)
      (f : ⟦ n ⟧%stn -> R) (p : n > 0)
      (i : ⟦ n ⟧%stn) (j : ⟦ n ⟧%stn) (ne_i_j : i ≠ j)
      (X : forall (k: ⟦ n ⟧%stn), (k ≠ i) -> (k ≠ j) -> (f k = 0%rig))
    : (Σ f = f i + f j)%rig.
  Proof.

    assert (H : f = pointwise n op1  (scalar_lmult_vec (f i) (identity_matrix i))
                    (scalar_lmult_vec (f j) (identity_matrix j))).
    { unfold "^".
      apply funextfun. intros k.
      unfold identity_matrix, scalar_lmult_vec, "^", const_vec.
      destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k].
      - rewrite coprod_rect_compute_1.
        destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + (* contradiction i ≠ j *)
          rewrite i_eq_k in ne_i_j.
          rewrite j_eq_k in ne_i_j.
          apply isirrefl_natneq in ne_i_j. contradiction.
        + rewrite coprod_rect_compute_2.
          rewrite rigmultx0.
          rewrite rigrunax1.
          rewrite rigrunax2.
          rewrite i_eq_k.
          reflexivity.
      - rewrite coprod_rect_compute_2.
        rewrite rigmultx0.
        rewrite riglunax1.
        destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + rewrite coprod_rect_compute_1.
          rewrite rigrunax2.
          rewrite j_eq_k.
          apply idpath.
        + rewrite coprod_rect_compute_2.
          rewrite rigmultx0.
          apply X.
          * apply issymm_natneq. assumption.
          * apply issymm_natneq. assumption.
    }

    rewrite H.
    rewrite sum_pointwise_op1.  (*TODO rename to something sensible*)
    unfold scalar_lmult_vec, const_vec.

    rewrite <- (sum_is_ldistr _ (identity_matrix i)).
    rewrite <- (sum_is_ldistr _ (identity_matrix j)).
    rewrite idrow_sums_to_1, rigrunax2.
    rewrite idrow_sums_to_1, rigrunax2.


    unfold pointwise. (* TODO: this is just a result of excessive unfolds and
                               some lemma(s) should be stated using
                               const_vec etc *)
    replace (@identity_matrix R n i j) with (@rigunel1 R).  (* TODO: used so often should be generalized *)
    2 : { unfold identity_matrix.
          rewrite (stn_eq_or_neq_right ne_i_j), coprod_rect_compute_2.
          reflexivity.
    }
    replace (@identity_matrix R n j i) with (@rigunel1 R).
    2 : { unfold identity_matrix.
          apply issymm_natneq in ne_i_j.
          rewrite (stn_eq_or_neq_right ne_i_j), coprod_rect_compute_2.
          reflexivity.
    }
    do 2 rewrite rigmultx0.
    rewrite riglunax1, rigrunax1.
    unfold identity_matrix.
    do 2 rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
    do 2 rewrite rigrunax2.
    apply idpath.

  Defined.
  (*  ~ point of interest ~ *)
  (* TODO remove and change mentions to the non apostrophesized version *)
  Lemma two_pulse_function_sums_to_points_rig' { n : nat }  (f : ⟦ n ⟧%stn -> R) (p : n > 0) :
    ∏ (i j: ⟦ n ⟧%stn ), (∏ (k: ⟦ n ⟧%stn), ((k ≠ i) -> (k ≠ j) ->
   (f k = 0%rig))) ->  (Σ f = op1 (f i) (f j)).
  Proof.
  Admitted.

  Lemma id_math_row_is_pf { n : nat }  : ∏ (r : ⟦ n ⟧%stn), (is_pulse_function r (identity_matrix r) ).
  Proof.
    unfold is_pulse_function.
    intros r i r_neq_j.
    unfold identity_matrix.
    destruct (stn_eq_or_neq r i) as [T | F].
    - rewrite T in r_neq_j.
      apply isirrefl_natneq in r_neq_j. apply fromempty. assumption.
    - rewrite coprod_rect_compute_2.
      reflexivity.
  Defined.

    (* Is n ≥ 1 necessary ? *)
  Definition vector_n_to_vector_snm1 { n : nat } (v : Vector R n) (p : n ≥ 1) : (Vector R (S ( n - 1 ))).
  Proof.
    unfold Vector in v.
    unfold Vector.
    change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
    rewrite minusplusnmm. 2 : {exact p. }
    exact v.
  Defined.


  (* This should be trivially true but how do we correctly formulate / prove it ? *)
  (* TODO: inline? *)
  Lemma isirrefl_rigunel1_to_empty {X} (x:X) : (x != x) -> ∅.
  Proof.
    intros H; apply H, idpath.
  Defined.

  Lemma matlunel2 : ∏ (n : nat) (mat : Matrix R n n),
    (identity_matrix ** mat) = mat.
  Proof.
    intros.
    apply funextfun. intros i.
    apply funextfun. intros j.

    - unfold "**". unfold row. unfold "^".

      assert (X: is_pulse_function i (λ i0 : (⟦ n ⟧)%stn, op2 (identity_matrix i i0) (col mat j i0))).
      { unfold is_pulse_function.

        intros k i_neq_k.
        unfold identity_matrix.
        destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k'].
        - rewrite i_eq_k in i_neq_k.
          apply isirrefl_natneq in i_neq_k.
          apply fromempty. assumption.
        - rewrite coprod_rect_compute_2.
          apply rigmult0x.
      }
      set (f :=  (λ i0 : (⟦ n ⟧)%stn, op2 (identity_matrix i i0) (col mat j i0)) ).
      unfold f.
      rewrite (pulse_function_sums_to_point_rig' i X).
      unfold identity_matrix.
      destruct (stn_eq_or_neq i i).
      + rewrite coprod_rect_compute_1.
        apply riglunax2.
      + (*apply isirrefl_natneq in h. *)
        rewrite coprod_rect_compute_2.
        apply isirrefl_natneq in h.
        apply fromempty. assumption.

  Defined.


  Lemma matrunel2 : ∏ (n : nat) (mat : Matrix R n n),
    (mat ** identity_matrix) = mat.
  Proof.

  Admitted.

  Definition matrix_is_invertible {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix) × ((B ** A) = identity_matrix).

  (* TODO: name as e.g. [matrix_right_inverse] since gives choice of inverse? and similar vice versa below. *)
  Definition matrix_is_invertible_left {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix).

  Definition matrix_is_invertible_right {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((B ** A) = identity_matrix).



  (* The product of two invertible matrices being invertible *)
  Lemma inv_matrix_prod_is_inv {n : nat} (A : Matrix R n n)
    (A' : Matrix R n n) (pa : matrix_is_invertible A) (pb : matrix_is_invertible A') :
    (matrix_is_invertible (A ** A')).
  Proof.
    intros.
    use tpair. { exact ((pr1 pb) ** (pr1 pa)). }
    use tpair.
    - rewrite matrix_mult_assoc.
      rewrite <- (matrix_mult_assoc A' _ _).
      replace (A' ** pr1 pb) with (@identity_matrix R n).
      + rewrite matlunel2.
        replace (A ** pr1 pa) with (@identity_matrix R n).
        2 : { symmetry.
              set (p := (pr1 (pr2 pa))). rewrite p.
              reflexivity.
        }
        reflexivity.
      + rewrite <- matrunel2.
        replace (A' ** pr1 pb) with (@identity_matrix R n).
        { rewrite matlunel2.
          reflexivity. }
        set (p := pr1 (pr2 pb)). rewrite p.
        reflexivity.
    - simpl.
      rewrite <- matrix_mult_assoc.
      rewrite  (matrix_mult_assoc (pr1 pb) _ _).
      replace (pr1 pa ** A) with (@identity_matrix R n).
      2 : { symmetry. rewrite (pr2 (pr2 pa)). reflexivity. }
      replace (pr1 pb ** identity_matrix) with (pr1 pb).
      2 : { rewrite matrunel2. reflexivity. }
      rewrite (pr2 (pr2 pb)).
      reflexivity.
  Defined.

  Lemma identity_is_inv { n : nat } : matrix_is_invertible (@identity_matrix _ n).
  Proof.
    unfold matrix_is_invertible.
    use tpair. { exact identity_matrix. }
    use tpair.
    - apply matlunel2.
    - apply matlunel2.
  Defined.
  (*
  Definition eq_set_invar_by_invmatrix_mm { n : nat } ( A : Matrix R n n )
    (C : Matrix R n n)
    (x : Matrix R n 1) (b : Matrix R n 1) : (A ** x) = b -> ((C ** A) ** x) = (C ** b).
  Proof.

  Abort.
  *)

End Matrices.


Section MatricesF.

  Context { R : rig }.

  (* Not really a clamp but setting every element at low indices to zero.
     TODO Also should not be necessary with sensible selection of pivots *)
  Local Definition clamp_f {n : nat} (f : ⟦ n ⟧%stn -> hq) (cutoff : ⟦ n ⟧%stn) : (⟦ n ⟧%stn -> hq).
    intros i.
    induction (natlthorgeh i cutoff) as [LT | GTH].
    - exact 0%hq.
    - exact (f i).
  Defined.


  Definition zero_vector_hq (n : nat) : ⟦ n ⟧%stn -> hq :=
    λ i : ⟦ n ⟧%stn, 0%hq.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  (* This is not really a zero vector ... Serves the purpose of a placeholder however.
     TODO rename or change definition *)
  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros i.
    assumption.
  Defined.


  (* The following definitions set up helper functions on finite sets which are then used in formalizing Gaussian Elimination*)

  Definition max_hq (a b : hq) : hq.
    induction (hqgthorleh a b).
    - exact a.
    - exact b.
  Defined.

  Definition max_hq_one_arg (a : hq) : hq -> hq := max_hq a.

  (* This should exist somewhere *)
  Definition tl' { n : nat }  (vec: Vector F n) : Vector F (n - 1).
    induction (natgtb n 0).
     assert  ( b: (n - 1 <= n)). { apply (natlehtolehm1 n n). apply isreflnatleh. }
    + exact (λ i : (⟦ n - 1 ⟧%stn), vec (stnmtostnn (n - 1) n b i)).
    + exact (λ i : (⟦ n - 1 ⟧%stn), 0%hq). (* ? *)
  Defined.



  (* We can generalize this to just ordered sets *)
  Definition max_hq_index { n : nat } (ei ei' : hq × ⟦ n ⟧%stn) : hq × ⟦ n ⟧%stn.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact ei.
    - exact ei'.
  Defined.

  Definition max_hq_index_one_arg { n : nat } (ei : hq × ⟦ n ⟧%stn) : (hq × ⟦ n ⟧%stn) -> (hq × ⟦ n ⟧%stn)
    := max_hq_index ei.

  (* Some of the following lemmata are very specific and could be better without the general definition form, or we
     could write these as local definitions *)
  Definition max_argmax_stnhq {n : nat} (vec : Vector F n) (pn : n > 0) : hq × (⟦ n ⟧)%stn.
  Proof.
    set (max_and_idx := (foldleft (0%hq,,(0%nat,,pn)) max_hq_index (λ i : (⟦ n ⟧%stn), (vec i) ,, i))).
    exact (max_and_idx).
  Defined.



  (*TODO: This is mostly a repetition of the rig equivalent. Can we generalize ? *)
  Lemma zero_function_sums_to_zero_hq:
    ∏ (n : nat) (f : (⟦ n ⟧)%stn -> F),
    (λ i : (⟦ n ⟧)%stn, f i) = const_vec 0%hq ->
    (Σ (λ i : (⟦ n ⟧)%stn, f i) ) = 0%hq.
  Proof.
    intros n f X.
    rewrite X.
    unfold const_vec.
    induction n.
    - reflexivity.
    - intros. rewrite iterop_fun_step.
      + rewrite hqplusr0.
        unfold "∘".
        rewrite -> IHn with ((λ _ : (⟦ n ⟧)%stn, 0%hq)).
        reflexivity.
        reflexivity.
      + unfold islunit. intros.
        rewrite hqplusl0.
        apply idpath.
  Defined.


End MatricesF.


Section Unsorted.

  Definition abs_hq (e: F) : F.
  Proof.
    destruct (hqgthorleh e 0%hq) as [? | ?].
    - exact e.
    - exact (- e)%hq.
  Defined.

  Lemma abs_ge_0_hq : ∏ (e : F), (hqgeh (abs_hq e) 0)%hq.
  Proof.
    intros e.
    unfold abs_hq.
    destruct (hqgthorleh e 0%hq).
    - apply hqgthtogeh in h. assumption.
    - apply hqleh0andminus in h. assumption.
  Defined.

  Definition max_hq_index_bounded { n : nat } (k : ⟦ n ⟧%stn) (f : ⟦ n ⟧%stn -> F) (ei ei' : hq × (⟦ n ⟧%stn)): hq × (⟦ n ⟧%stn).
  Proof.
    set (hq_index := max_hq_index ei ei').
    induction (natlthorgeh (pr2 ei') k).
    - induction (natlthorgeh (pr2 ei) k ).
      + exact (f k,, k).
      + exact ei. (* This case should not occur in our use *)
    - induction (natlthorgeh (pr2 ei) k).
      + exact ei'.
      + exact (max_hq_index ei ei').

  Defined.



  Lemma max_hq_index_bounded_geq_k { n : nat } (k : ⟦ n ⟧%stn) (f : ⟦ n ⟧%stn -> F)
    (ei ei' : hq × (⟦ n ⟧%stn)): pr2 (max_hq_index_bounded k f ei ei') >= k.
  Proof.
    unfold max_hq_index_bounded.
    destruct (natlthorgeh (pr2 ei') k).
    - rewrite coprod_rect_compute_1.
      destruct (natlthorgeh (pr2 ei) k).
      + rewrite coprod_rect_compute_1. apply isreflnatleh.
      + rewrite coprod_rect_compute_2. assumption.
    - rewrite coprod_rect_compute_2.
      unfold max_hq_index.
      destruct (natlthorgeh (pr2 ei) k).
      + rewrite coprod_rect_compute_1.
        assumption.
      + rewrite coprod_rect_compute_2.
        destruct (hqgthorleh (pr1 ei) (pr1 ei')).
        * rewrite coprod_rect_compute_1.
          assumption.
        * rewrite coprod_rect_compute_2.
          assumption.
  Defined.

  (* TODO: indicate absolute value in naming *)
  Definition max_argmax_stnhq_bounded { n : nat } (vec : Vector F n) (pn : n > 0 ) (k : ⟦ n ⟧%stn) :=
  foldleft (0%hq,, (0,, pn)) (max_hq_index_bounded k vec) (λ i : (⟦ n ⟧)%stn, abs_hq (vec i),, i).



   Definition max_el' { n : nat } (v : Vector F n) (max' : F) : F.
   Proof.
     induction n as [ | m IH]. (* TODO naming *)
     {exact max'. }
     exact (max_hq max' (IH (@drop_el_vector F m v lastelement))). (* todo this or DNI ? *)
   Defined.

   Definition max_el { n : nat } (vec: Vector F n) := max_el' vec 0%hq.

  (* TODO at least rename
     it's in general not true if n = 0 (that's why we have k )*)
  Lemma some_lemma (m n : nat) (k : ⟦ n ⟧%stn) : n - 1 - m < n.
  Proof.
    { assert (p' : n - 1 < n).
      { apply natminuslthn.
        - destruct n.
          + destruct (weqstn0toempty k).
          + apply natgthsn0.
        - reflexivity.
      }
      destruct m.
      - rewrite minus0r. assumption.
      - apply (natlehlthtrans (n - 1 - S m) (n - 1) n ).
        + apply natminuslehn.
        + assumption.
    }
  Defined.

  (* ( i,, i < n) to (i-1,, i-1 < n *)
  Definition decrement_stn { n : nat } ( i : (⟦ n ⟧)%stn ) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgtb (pr1 i) 0).
    (*- assert ( p : ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }*)
    - assert ( p :  ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }
      exact ((pr1 i) - 1,, p).
    - exact i.
  Defined.


  Definition switch_vector_els { n : nat } (vec : Vector F n) (e1 e2 : ⟦ n ⟧%stn) : Vector F n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i e1).
    - exact (vec e2).
    - induction (stn_eq_or_neq i e2).
      + exact (vec e1).
      + exact (vec i).
  Defined.
End Unsorted.


Section Gauss.
  (* Gaussian elimination over the field of rationals *)

  (* TODO better (or any) comments for all these functions including assumptions*)

  (* TODO Carot operator is used similarly throughout the document, move out *)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Context { R : rig }.
  (* Gaussian elimination over the field of rationals *)


  Definition gauss_add_row { m n : nat } ( mat : Matrix F m n )
    ( s : F ) ( r1 r2 : ⟦ m ⟧%stn ) : ( Matrix F m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact ( op1 ( mat r1 j )  ( op2 s ( mat r2 j ))).
    - exact ( mat r1 j ).
  Defined.

  (* Is stating this as a Lemma more in the style of other UniMath work?*)
  Local Definition identity_matrix { n : nat } : ( Matrix F n n ).
  Proof.
    apply ( @identity_matrix hq ).
  Defined.


  (* Need again to restate several definitions to use the identity on rationals*)
  (*Local Notation Σ := (iterop_fun 0%hq op1).*)(*
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).*)

  (* TODO: replace with upstream version? *)
  Local Definition matrix_mult {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  (* Which by left multiplication corresponds to adding r1 to r2 *)
  (* TODO might want to induct on r1 = r2, that case is off-by-one by this formulation.
     (However is not used in any of the eliminations) *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (identity_matrix i) (const_vec s ^ identity_matrix r1)). (*induction (stn_eq_or_neq j r2).
      + exact (identity_matrix i j + identity_matrix ) .
      + exact (identity_matrix i j).*)
    - exact (identity_matrix i).
  Defined.

  Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) (s : F) : Matrix F m n :=
    (make_add_row_matrix r1 r2 s ) **  mat.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
    (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  (* These could really be m x n ...*)
  Definition make_scalar_mult_row_matrix { n : nat}
    (s : F) (r : ⟦ n ⟧%stn): Matrix F n n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
      - induction (stn_eq_or_neq i r).
        + exact s.
        + exact 1%hq.
      - exact 0%hq.
  Defined.

  Definition gauss_switch_row {m n : nat} (mat : Matrix F m n)
             (r1 r2 : ⟦ m ⟧%stn) : Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (identity_matrix r2).
    - induction (stn_eq_or_neq i r2).
      + exact (identity_matrix r1).
      + exact (identity_matrix i).
  Defined.


  Definition test_row_switch_statement {m n : nat} (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
  Proof.
    use funextfun; intros i.
    use funextfun; intros j.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq i r1) as [ e_ir1 | ne_ir1 ]; simpl.
    - destruct (stn_eq_or_neq r2 r1) as [ e_r1r2 | ne_r1r2 ]; simpl.
      + destruct e_ir1, e_r1r2. apply idpath.
      + destruct (stn_eq_or_neq r2 r2) as [ ? | absurd ]; simpl.
        * destruct e_ir1. apply idpath.
        * set (H := isirrefl_natneq _ absurd). destruct H.
    - destruct (stn_eq_or_neq i r2) as [ e_ir2 | ne_ir2 ]; simpl.
      + destruct e_ir2; simpl.
        destruct (stn_eq_or_neq r1 r1) as [ ? | absurd ]; simpl.
        * reflexivity.
        * destruct (stn_eq_or_neq r1 i) as [ e_ir1 | ne_ir1' ]; simpl.
        -- rewrite e_ir1. apply idpath.
        -- set (H := isirrefl_natneq _ absurd). destruct H.
      + reflexivity.
  Defined.


  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)
  Lemma matrix_scalar_mult_is_elementary_row_op {n : nat} (mat : Matrix F n n) (s : F) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros j.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    unfold "**". unfold "^". unfold col. unfold transpose. unfold row. unfold flip.
    unfold coprod_rect. unfold identity_matrix.
    destruct (stn_eq_or_neq i r) as [? | ?] ; simpl.
    - rewrite p.
      (* apply pulse_function_sums_to_point.*)
  Abort.



  Definition unit_vector { n : nat } (i : ⟦ n ⟧%stn) : Vector R n.
  Proof.
    intros j.
    induction (stn_eq_or_neq i j) as [T | F].
    - exact (1%rig).
    - exact (0%rig).
  Defined.

  Lemma weq_mat_vector {X : UU} { n : nat } : (Matrix X 1 n ) ≃ Vector X n.
    (*unfold Matrix. unfold Vector.*)
  Abort.




  (* TODO : F should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : hqneq s 0%hq ) :
    @matrix_is_invertible F n (make_scalar_mult_row_matrix s i ).
  Proof.
    (*unfold matrix_is_invertible.
    unfold make_scalar_mult_row_matrix.*)
    use tpair.
    { exact (make_scalar_mult_row_matrix (hqmultinv s ) i). }
    use tpair.
    - apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq k l) as [T' | F'].
      + (*rewrite T.*)
        unfold gauss_scalar_mult_row.
        unfold identity_matrix.
        unfold make_scalar_mult_row_matrix.
        unfold Matrix.matrix_mult.
        unfold row. unfold col. unfold transpose. unfold "^". unfold flip.
        unfold Matrix.identity_matrix.
        destruct (stn_eq_or_neq l i).
        * destruct (stn_eq_or_neq l l).
          2 : { apply isirrefl_natneq in h.
                apply fromempty. assumption. }
          -- rewrite T'. rewrite p.
             destruct (stn_eq_or_neq i i).
             ++ do 2 rewrite coprod_rect_compute_1.
                rewrite (@pulse_function_sums_to_point_rig' F n l).
                rewrite p.
                destruct (stn_eq_or_neq i i).
                ** do 3 rewrite coprod_rect_compute_1.
                   apply (hqisrinvmultinv). assumption.
                ** do 2 rewrite coprod_rect_compute_2.
                   apply isirrefl_natneq in h.
                   apply fromempty. assumption.
                ** unfold is_pulse_function.
                   intros q l_neq_q.
                   rewrite <- p.
                   destruct (stn_eq_or_neq l q) as [l_eq_q' | l_neq_q'].
                   --- rewrite l_eq_q' in l_neq_q.
                       apply isirrefl_natneq in l_neq_q.
                       apply fromempty. assumption.
                   --- rewrite coprod_rect_compute_2.
                       apply rigmult0x.
             ++ remember h as h'. clear Heqh'.
                apply isirrefl_natneq in h.
                apply fromempty. assumption.
        * rewrite <- T' in h.
          destruct (stn_eq_or_neq k i).
          -- rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq k l).
             ++ rewrite coprod_rect_compute_1.
                rewrite(@pulse_function_sums_to_point_rig' F n k).
                ** destruct (stn_eq_or_neq k l).
                   --- rewrite coprod_rect_compute_1.
                       destruct (stn_eq_or_neq k k).
                       +++ rewrite coprod_rect_compute_1.
                           destruct (stn_eq_or_neq k i).
                           *** rewrite coprod_rect_compute_1.
                               apply hqisrinvmultinv.
                               assumption.
                           *** rewrite coprod_rect_compute_2.
                               rewrite p in h0.
                               apply isirrefl_natneq in h0.
                               apply fromempty. assumption.
                       +++ remember h0 as h0'. clear Heqh0'.
                           apply isirrefl_natneq in h0.
                           apply fromempty. assumption.
                   --- rewrite  coprod_rect_compute_2.
                       rewrite <- p0 in h0.
                       apply isirrefl_natneq in h0.
                       apply fromempty. assumption.
                ** rewrite p in h.
                   apply isirrefl_natneq in h.
                   apply fromempty. assumption.
             ++ remember h0 as h0'. clear Heqh0'.
                rewrite T' in h0.
                apply isirrefl_natneq in h0.
                apply fromempty. assumption.
          --
            rewrite coprod_rect_compute_2.
            destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l] .
            2 : { remember k_neq_l as k_neq_l'.
                  clear Heqk_neq_l'.
                  rewrite T' in k_neq_l.
                  apply isirrefl_natneq in k_neq_l.
                  apply fromempty. assumption. }
            rewrite coprod_rect_compute_1.
            rewrite (@pulse_function_sums_to_point_rig' F n k).
            ++ destruct (stn_eq_or_neq k k) as [k_eq_k | k_neq_k].
               2 : { rewrite coprod_rect_compute_2.
                     apply isirrefl_natneq in k_neq_k.
                     apply fromempty. assumption.
               }
               destruct (stn_eq_or_neq k l) as [ ? | cntr].
               2 : { rewrite coprod_rect_compute_2.
                     rewrite k_eq_l in cntr.
                     apply isirrefl_natneq in cntr.
                     apply fromempty. assumption.
               }
               do 2rewrite coprod_rect_compute_1.
               destruct (stn_eq_or_neq k i) as [cntr | k_neq_i].
               { rewrite cntr in h. apply isirrefl_natneq in h.
                 apply fromempty. assumption.
               }
               rewrite coprod_rect_compute_2.
               apply riglunax2.
            ++ unfold is_pulse_function.
               intros q l_neq_q.
               rewrite <- k_eq_l.
               destruct (stn_eq_or_neq l q) as [l_eq_q' | l_neq_q'].
               --- rewrite k_eq_l in l_neq_q.
                   rewrite l_eq_q' in l_neq_q.
                   apply isirrefl_natneq in l_neq_q.
                   apply fromempty. assumption.
               --- destruct (stn_eq_or_neq q k) as [ ? | ? ].
                 +++
                   rewrite coprod_rect_compute_1.
                   rewrite p in l_neq_q.
                   apply isirrefl_natneq in l_neq_q.
                   apply fromempty. assumption.
                 +++ rewrite coprod_rect_compute_2.
                     destruct (stn_eq_or_neq k q).
                     *** rewrite coprod_rect_compute_1.
                         apply rigmultx0.
                     *** rewrite coprod_rect_compute_2.
                         apply rigmultx0.
      + unfold make_scalar_mult_row_matrix.
        unfold Matrix.identity_matrix.
        destruct (stn_eq_or_neq k l) as [cntr | dup ].
        { rewrite cntr in F'. (* really should have a one_liner *)
          apply isirrefl_natneq in F'.
          apply fromempty. assumption.
        }
        rewrite coprod_rect_compute_2.
        unfold Matrix.matrix_mult.
        unfold col. unfold row. unfold "^".
        unfold transpose. unfold flip.
        destruct (stn_eq_or_neq k i) as [k_eq_i | k_neq_i] .
        * rewrite coprod_rect_compute_1.
          rewrite (@pulse_function_sums_to_point_rig' F n i).
          -- destruct (stn_eq_or_neq k i) as [ ? | cntr ].
             rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq i i) as [? | cntr ].
             ++ destruct (stn_eq_or_neq i l) as [i_eq_l | i_neq_l].
                **
                  do 2 rewrite coprod_rect_compute_1.
                  rewrite <- k_eq_i in i_eq_l.
                  rewrite i_eq_l in F'.
                  apply isirrefl_natneq in F'.
                  apply fromempty. assumption.
                ** rewrite coprod_rect_compute_2.
                   apply rigmultx0.
             ++ rewrite coprod_rect_compute_2.
                apply isirrefl_natneq in cntr.
                apply fromempty. assumption.
             ++ rewrite coprod_rect_compute_2.
                rewrite k_eq_i in cntr.
                apply isirrefl_natneq in cntr.
                apply fromempty. assumption.
          -- unfold is_pulse_function.
             intros q i_neq_q.
             rewrite k_eq_i.
             destruct (stn_eq_or_neq q i ) as [q_eq_i | q_neq_i] .
             ++ rewrite q_eq_i in i_neq_q.
                apply isirrefl_natneq in i_neq_q.
                apply fromempty. assumption.
             ++ destruct (stn_eq_or_neq i q) as [i_eq_q | i_neq_q'].
                { rewrite i_eq_q in i_neq_q.
                  apply isirrefl_natneq in i_neq_q.
                  apply fromempty. assumption.
                }
                do 2 rewrite coprod_rect_compute_2.
                destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
                ** apply rigmult0x.
                ** apply rigmult0x.
      * rewrite coprod_rect_compute_2.
        rewrite (@pulse_function_sums_to_point_rig' F n k).
        -- destruct (stn_eq_or_neq k k) as [? | cntr].
           2 : { rewrite coprod_rect_compute_2.
                 apply isirrefl_natneq in cntr.
                 apply fromempty. assumption.
           }
           destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l] .
           { rewrite k_eq_l in F'.  apply isirrefl_natneq in F'.
             apply fromempty. assumption.
           }
           rewrite coprod_rect_compute_2. rewrite coprod_rect_compute_1.
           apply rigmultx0.

        -- unfold is_pulse_function.
           intros j k_neq_j.
           destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j'].
           { rewrite k_eq_j in k_neq_j. apply isirrefl_natneq in k_neq_j.
             apply fromempty. assumption.
           }
           destruct (stn_eq_or_neq j l) as [j_eq_l | j_neq_l].
           ++ rewrite coprod_rect_compute_1.
             rewrite coprod_rect_compute_2.
             apply rigmult0x.
           ++ apply rigmult0x.
    - simpl.
      (* Here in the second half, we try to be slightly more efficient *)
      unfold make_scalar_mult_row_matrix.
      unfold Matrix.identity_matrix.
      unfold matrix_mult.
      unfold Matrix.matrix_mult.
      unfold row. unfold col. unfold transpose. unfold flip.
      unfold "^".
      apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq k i) as [ k_eq_i | k_neq_i ].
      +
        destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l ].
        * rewrite coprod_rect_compute_1.
          rewrite <- k_eq_l.
          rewrite <- k_eq_i.
          rewrite (pulse_function_sums_to_point_rig' k).
          -- rewrite stn_neq_or_neq_refl.
            do 3 rewrite coprod_rect_compute_1.
            apply (hqislinvmultinv).
            assumption.
          -- unfold is_pulse_function.
             intros q k_neq_q.
             rewrite (stn_eq_or_neq_right k_neq_q).
             rewrite coprod_rect_compute_2.
             apply rigmult0x.
        * rewrite coprod_rect_compute_2.
          rewrite (pulse_function_sums_to_point_rig' k). (* Didn't we just do this ? *)
          -- rewrite (stn_eq_or_neq_right k_neq_l).
             rewrite coprod_rect_compute_2.
             rewrite (stn_neq_or_neq_refl).
             rewrite coprod_rect_compute_1.
             rewrite rigmultx0. apply idpath.
          -- unfold is_pulse_function.
             intros q k_neq_q.
             rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q'].
             ++ rewrite k_eq_q in k_neq_q.
                apply isirrefl_natneq in k_neq_q.
                contradiction.
             ++ rewrite coprod_rect_compute_2.
                apply rigmult0x.
      + rewrite (pulse_function_sums_to_point_rig' k).
        * rewrite (stn_neq_or_neq_refl).
          rewrite (stn_eq_or_neq_right k_neq_i).
          rewrite coprod_rect_compute_1.
          do 2 rewrite coprod_rect_compute_2.
          destruct (stn_eq_or_neq k l).
          -- do 2 rewrite coprod_rect_compute_1.
             rewrite rigrunax2. apply idpath.
          -- do 2 rewrite coprod_rect_compute_2.
             rewrite rigmultx0. apply idpath.
        * unfold is_pulse_function.
          intros q k_neq_q.
          rewrite (stn_eq_or_neq_right k_neq_q). rewrite coprod_rect_compute_2.
          destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
          -- apply rigmult0x.
          -- apply rigmult0x.
  Defined.

  (*
  Lemma test { n : nat } (n : ⟦ n ⟧%stn ) (f : ⟦ n ⟧%stn -> R) is_pulse_function (dni
  *)

  (*
  Lemma sum_over_coprod_rect : ∏ (A B : UU) (P : A ⨿ B → UU) (f : ∏ a : A, P (inl a))
(g : ∏ b : B, P (inr b)) (a : A), (iterop_fun 0%rig op1) (coprod_rect P f g (inl a)) = (iterop_fun 0%rig op1) f a.
   *)

  (* ~ point of interest ~ *)
  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s : F ) (p : (s != 0)%hq)
    (p' : n > 0) :
    @matrix_is_invertible F n (make_add_row_matrix r1 r2 s ).
  Proof.
    unfold matrix_is_invertible.
    unfold make_add_row_matrix.
    use tpair.
    {
      induction (stn_eq_or_neq r1 r2) as [? | ?].
      - exact (make_add_row_matrix r1 r2 (hqmultinv s)).
      - exact (make_add_row_matrix r1 r2 (- s)%hq).
    }
    unfold make_add_row_matrix, identity_matrix, Matrix.identity_matrix.
    unfold matrix_mult, Matrix.matrix_mult, col, "^", transpose, flip, row.
    use tpair.
    - apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq r1 r2) as [r1_eq_r2 | r1_neq_r2].
      + rewrite coprod_rect_compute_1.
        destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l].
        * rewrite coprod_rect_compute_1.
          rewrite k_eq_l.
          rewrite (pulse_function_sums_to_point_rig' k).
          -- rewrite k_eq_l.
             rewrite <- r1_eq_r2. (*
             rewrite stn_neq_or_neq_refl.
             rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq l r1) as [l_eq_r1 | l_neq_r1].
             ++ do 4 rewrite coprod_rect_compute_1.
                apply hqisrinvmultinv.
                exact p.
             ++ do 2 rewrite coprod_rect_compute_2.
                apply riglunax2.
          -- rewrite k_eq_l.
             rewrite <- r1_eq_r2.
             unfold is_pulse_function. intros ? l_neq_j.
             rewrite (stn_eq_or_neq_right l_neq_j).
             rewrite coprod_rect_compute_2.
             destruct (stn_eq_or_neq j l) as [abs | ? ]. (* this should not be the best way.
                                              How do we go from l ≠ j to  j ≠ l? in < 3 lines?*)
             { rewrite abs in l_neq_j.
                 apply isirrefl_natneq in l_neq_j.
                 contradiction. }
             ++ rewrite coprod_rect_compute_2.
                destruct (stn_eq_or_neq j r1) as [j_eq_r1 | j_neq_r1].
                ** rewrite j_eq_r1.
                   do 2 rewrite coprod_rect_compute_1.
                   rewrite j_eq_r1 in l_neq_j.
                   rewrite  (stn_eq_or_neq_right l_neq_j).
                   rewrite coprod_rect_compute_2.
                   apply rigmult0x.
                ** do 2 rewrite coprod_rect_compute_2.
                   destruct (stn_eq_or_neq l r1) as [? | ?].
                   --- rewrite coprod_rect_compute_1.
                       apply rigmult0x.
                   --- rewrite coprod_rect_compute_2.
                       apply rigmult0x.
        * rewrite coprod_rect_compute_2.
          apply zero_function_sums_to_zero. (* k != l, but r1 = r2 *)
          apply funextfun. intros q.
          change (const_vec 0%rig q) with 0%hq.
          destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
          -- rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq l r2) as [l_eq_r2 | l_neq_r2].
             ++ rewrite coprod_rect_compute_1. (* TODO indentation on doubles *)
                rewrite l_eq_r2 in k_neq_l.
                rewrite <- r1_eq_r2 in k_neq_l.
                rewrite (stn_eq_or_neq_right k_neq_l).
                rewrite coprod_rect_compute_2.
                rewrite q_eq_r1.
                rewrite (stn_eq_or_neq_right k_neq_l).
                rewrite coprod_rect_compute_2.
                apply rigmult0x.
             ++ rewrite coprod_rect_compute_2.
                destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
                ** rewrite coprod_rect_compute_1.
                   rewrite q_eq_r1 in q_eq_l.
                   rewrite <- q_eq_l in k_neq_l.
                   rewrite (stn_eq_or_neq_right k_neq_l).
                   rewrite coprod_rect_compute_2.
                   rewrite <- q_eq_r1 in k_neq_l.
                   rewrite (stn_eq_or_neq_right k_neq_l).
                   rewrite coprod_rect_compute_2.
                   apply rigmult0x.
                ** rewrite coprod_rect_compute_2.
                   apply rigmultx0.
          -- rewrite coprod_rect_compute_2.
             destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
             ++ rewrite coprod_rect_compute_1.
                destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
                ** rewrite coprod_rect_compute_1.
                   rewrite r1_eq_r2 in q_neq_r1.
                   rewrite (stn_eq_or_neq_right q_neq_r1).
                   rewrite coprod_rect_compute_2.
                   rewrite <- q_eq_l in k_neq_l.
                   rewrite (stn_eq_or_neq_right k_neq_l).
                   rewrite coprod_rect_compute_2.
                   apply rigmult0x.
                ** rewrite coprod_rect_compute_2.
                   rewrite <- q_eq_l in k_neq_l.
                   rewrite (stn_eq_or_neq_right k_neq_l).
                   rewrite coprod_rect_compute_2.
                   apply rigmult0x.
             ++ rewrite coprod_rect_compute_2.
                destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
                ** rewrite coprod_rect_compute_1.
                   apply rigmultx0.
                ** apply rigmultx0.
      + (* r1 ≠ r2*)
        rewrite coprod_rect_compute_2.
        destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l].
        * rewrite coprod_rect_compute_1.
          rewrite (pulse_function_sums_to_point_rig' k).
          -- destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
             ++ do 2 rewrite coprod_rect_compute_1.
                rewrite k_eq_l in k_eq_r1.
                rewrite <- k_eq_r1 in r1_neq_r2.
                rewrite (stn_eq_or_neq_right r1_neq_r2).
                rewrite coprod_rect_compute_2.
                rewrite (stn_eq_or_neq_left k_eq_l).
                rewrite coprod_rect_compute_1.
                rewrite (stn_neq_or_neq_refl ).
                rewrite coprod_rect_compute_1.
                rewrite <- k_eq_l in r1_neq_r2.
                rewrite (stn_eq_or_neq_right r1_neq_r2).
                rewrite coprod_rect_compute_2.
                apply riglunax2.
             ++ do 2 rewrite coprod_rect_compute_2.
                rewrite (stn_neq_or_neq_refl).
                rewrite coprod_rect_compute_1.
                rewrite (stn_eq_or_neq_left k_eq_l).
                rewrite coprod_rect_compute_1.
                apply riglunax2.
          -- unfold is_pulse_function.
             intros ? k_neq_j.
             destruct (stn_eq_or_neq j r1) as [j_eq_r1 | j_neq_r1].
             ++ rewrite coprod_rect_compute_1.
                destruct (stn_eq_or_neq l r2) as [l_eq_r2 | l_neq_r2].
                ** rewrite coprod_rect_compute_1.
                   rewrite l_eq_r2 in k_eq_l.
                   rewrite <- k_eq_l in r1_neq_r2.
                   rewrite j_eq_r1 in k_neq_j.
                   rewrite (stn_eq_or_neq_right k_neq_j).
                   rewrite coprod_rect_compute_2.
                   rewrite <- j_eq_r1 in k_neq_j.
                   rewrite (stn_eq_or_neq_right k_neq_j).
                   rewrite coprod_rect_compute_2.
                   apply rigmult0x.
                ** rewrite coprod_rect_compute_2.
                   rewrite k_eq_l in k_neq_j.
                   apply issymm_natneq in k_neq_j.
                   rewrite (stn_eq_or_neq_right k_neq_j).
                   rewrite coprod_rect_compute_2.
                   apply rigmultx0.
             ++ rewrite coprod_rect_compute_2.
                rewrite k_eq_l in k_neq_j.
                apply issymm_natneq in k_neq_j.
                rewrite (stn_eq_or_neq_right k_neq_j).
                rewrite coprod_rect_compute_2.
                apply rigmultx0.
        * rewrite coprod_rect_compute_2. (* The one case
                                            with non-zero values possible in 2 columns. *)
          destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
          --
            (*rewrite (pulse_function_sums_to_point_rig' r2).*)
            destruct (stn_eq_or_neq l r2) as [l_eq_r2 | l_neq_r2].

              (*rewrite (pulse_function_sums_to_point_rig' l). *) *)

  Abort.

  (* TODO worst one yet? We can trivially halve it since the first destruct is completely symmetrical *)


  (* TODO worst one yet? We can trivially halve it since the first destruct is completely symmetrical *)
  Lemma switch_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s : F ) ( ne : hqneq s 0%hq ) :
    @matrix_is_invertible F n (make_gauss_switch_row_matrix n r1 r2).
  Proof.
    intros.
    use tpair.
    { exact (make_gauss_switch_row_matrix n r1 r2). }
    set (lft := @stn_eq_or_neq_left n).
    set (rht := @stn_eq_or_neq_right n).
    set (irfl := @stn_neq_or_neq_refl n).
    set (cpl := coprod_rect_compute_1).
    set (cpr := coprod_rect_compute_2).
    unfold make_gauss_switch_row_matrix, identity_matrix, Matrix.identity_matrix.
    unfold matrix_mult, Matrix.matrix_mult, row, col, "^", transpose, flip.
    use make_dirprod.
    - apply funextfun. intros i.
      apply funextfun. intros j.
      destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1];
        destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2];
        destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
      (* some cases should be impossible, so shouldn’t need algebra? *)
      + rewrite i_eq_r1, i_eq_r2, i_eq_j.
        do 2 rewrite cpl.
        -- rewrite (pulse_function_sums_to_point_rig' i).
           ++ rewrite (lft _ _ i_eq_r1), cpl. (* TODO these 2 are unnecessarily long *)
              rewrite i_eq_j in i_eq_r2.
              symmetry in i_eq_r2. (*TODO *)
              rewrite (lft _ _ i_eq_r2), cpl.
              rewrite <- i_eq_j in i_eq_r2.
              rewrite (lft _ _  i_eq_r2), cpl.
              apply rigrunax2.
           ++ unfold is_pulse_function.
              intros q i_neq_q.
              rewrite i_eq_r1 in i_neq_q.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              rewrite <- i_eq_r1 in i_neq_q.
              rewrite i_eq_r2 in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              rewrite <- i_eq_j.
              rewrite i_eq_r2.
              rewrite (rht _ _ i_neq_q), cpr.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
      + rewrite (pulse_function_sums_to_point_rig' i).
        ++
          rewrite cpr.
          rewrite (lft _ _ i_eq_r1), cpl.
          rewrite cpl.
          rewrite <- i_eq_r2, (rht _ _ i_neq_j).
          rewrite coprod_rect_compute_2, stn_neq_or_neq_refl, cpl.
          apply rigmultx0.
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           rewrite <- i_eq_r1.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr.
           rewrite <- i_eq_r2.
           rewrite (rht _ _ i_neq_q), cpr.
           destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
           ** do 2 rewrite cpl.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
           ** rewrite cpr, cpl.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
      + (* Shouldn't this be zero function ? *)
        do 2 rewrite cpl.

        rewrite (pulse_function_sums_to_point_rig' r2).
        ** rewrite (stn_neq_or_neq_refl), cpl.
           rewrite <- i_eq_j.
           apply issymm_natneq in i_neq_r2.
           rewrite <- i_eq_r1.
           rewrite (rht _ _ i_neq_r2), cpr, cpl.
           rewrite stn_neq_or_neq_refl, cpl.
           apply riglunax2.
        ** unfold is_pulse_function.
           intros q r2_neq_q.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           --- rewrite cpl.
               rewrite (rht _ _ r2_neq_q), cpr.
               apply rigmult0x.
           --- rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               rewrite (rht _ _ r2_neq_q), cpr.
               rewrite <- i_eq_j, i_eq_r1.
               rewrite (rht _ _ q_neq_r1), cpr.
               apply rigmultx0.
      + do 2 rewrite cpr.
        rewrite cpl.
        apply zero_function_sums_to_zero.
        apply funextfun. intros q.
        destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
        --- rewrite cpl.
            apply issymm_natneq in i_neq_r2.
            destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
            +++ rewrite cpl.
                rewrite r2_eq_j, q_eq_r1, <- i_eq_r1.
                apply issymm_natneq in i_neq_j.
                rewrite (rht _ _ i_neq_j), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                rewrite q_eq_r1, <- i_eq_r1.
                rewrite (rht _ _ i_neq_r2), cpr.
                apply rigmult0x.
        --- rewrite cpr.
            destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
            +++ rewrite cpl.
                rewrite <- i_eq_r1.
                rewrite (rht _ _ i_neq_j), cpr.
                rewrite q_eq_r2.
                rewrite  stn_neq_or_neq_refl, cpl.
                apply rigmultx0.
            +++ rewrite cpr.
                apply issymm_natneq in q_neq_r2.
                rewrite (rht _ _ q_neq_r2), cpr.
                apply rigmult0x.
      + rewrite  i_eq_r2, i_eq_j.
        do 2 rewrite cpl.
        rewrite (pulse_function_sums_to_point_rig' r1).
        ++ rewrite <- i_eq_j, <- i_eq_r2.
           do 2 rewrite (stn_neq_or_neq_refl), cpl.
           rewrite cpr.
           rewrite (stn_neq_or_neq_refl), cpl.
           apply riglunax2.
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr, cpr.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr.
           apply rigmult0x.
      + rewrite (pulse_function_sums_to_point_rig' i).
        ++ do 2 rewrite cpr.
           rewrite (rht _ _ i_neq_r1), cpr.
           rewrite cpl.
           apply issymm_natneq in i_neq_r1.
           rewrite (rht _ _ i_neq_r1), cpr.
           apply rigmult0x.
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           rewrite cpr, cpl.
           apply issymm_natneq in i_neq_r1.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           ** rewrite cpl.
              rewrite <- i_eq_r2.
              rewrite (rht _ _ i_neq_j), cpr.
              apply rigmultx0.
           ** rewrite cpr.
              rewrite <- i_eq_r2.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply issymm_natneq in q_neq_r1.
              rewrite (rht _ _ q_neq_r1), cpr.
              apply rigmult0x.
      + (* Shouldn't this be zero function ? *)
        rewrite cpl.
        rewrite (pulse_function_sums_to_point_rig' i).
        ** rewrite (rht _ _ i_neq_r1).
           do 3 rewrite cpr.
           rewrite (stn_neq_or_neq_refl), cpl.
           rewrite (rht _ _ i_neq_r2), cpr.
           rewrite (lft _ _ i_eq_j), cpl.
           apply riglunax2.
        ** unfold is_pulse_function.
           intros q r2_neq_q.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           --- rewrite cpl.
               rewrite <- i_eq_j, cpr, cpr.
               apply issymm_natneq in i_neq_r2.
               rewrite (rht _ _ i_neq_r2), cpr.
               apply rigmultx0.
           --- rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               do 2 rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               rewrite (rht _ _ r2_neq_q), cpr.
               apply rigmult0x.
      + do 2 rewrite cpr.
        rewrite cpr.
        apply zero_function_sums_to_zero.
        apply funextfun. intros q.
        destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
        --- rewrite cpl.
            apply issymm_natneq in i_neq_r2.
            destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
            +++ rewrite cpl.
                rewrite q_eq_r1.
                rewrite (rht _ _ i_neq_r1), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                apply rigmultx0.
        --- rewrite cpr.
            destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
            +++ rewrite cpl.
                rewrite q_eq_r2.
                rewrite (rht _ _ i_neq_r2), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                apply issymm_natneq in q_neq_r2.
                destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
                ---- rewrite cpl.
                     rewrite q_eq_j.
                     rewrite (rht _ _ i_neq_j), cpr.
                     apply rigmult0x.
                ---- rewrite cpr.
                     apply rigmultx0.
    - apply funextfun. intros i.
      apply funextfun. intros j.
      destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
      + destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
        * destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
          rewrite i_eq_r1, i_eq_r2, i_eq_j.
          do 2 rewrite cpl.
          -- rewrite (pulse_function_sums_to_point_rig' i).
             ++ rewrite (lft _ _ i_eq_r1), cpl. (* TODO these 2 are unnecessarily long *)
                rewrite i_eq_j in i_eq_r2.
                symmetry in i_eq_r2. (*TODO *)
                rewrite (lft _ _ i_eq_r2), cpl.
                rewrite <- i_eq_j in i_eq_r2.
                rewrite (lft _ _  i_eq_r2), cpl.
                apply rigrunax2.
             ++ unfold is_pulse_function.
                intros q i_neq_q.
                rewrite i_eq_r1 in i_neq_q.
                apply issymm_natneq in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr.
                rewrite <- i_eq_r1 in i_neq_q.
                rewrite i_eq_r2 in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr.
                rewrite <- i_eq_j.
                rewrite i_eq_r2.
                rewrite (rht _ _ i_neq_q), cpr.
                apply issymm_natneq in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr.
                apply rigmult0x.
          -- rewrite (pulse_function_sums_to_point_rig' i).
             ++
                rewrite cpr.
                rewrite (lft _ _ i_eq_r1), cpl.
                rewrite cpl.
                rewrite <- i_eq_r2, (rht _ _ i_neq_j).
                rewrite coprod_rect_compute_2, stn_neq_or_neq_refl, cpl.
                apply rigmultx0.
             ++ unfold is_pulse_function.
                intros q i_neq_q.
                rewrite <- i_eq_r1.
                apply issymm_natneq in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr.
                rewrite <- i_eq_r2.
                rewrite (rht _ _ i_neq_q), cpr.
                destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
                ** do 2 rewrite cpl.
                   apply issymm_natneq in i_neq_q.
                   rewrite (rht _ _ i_neq_q), cpr.
                   apply rigmult0x.
                ** rewrite cpr, cpl.
                   apply issymm_natneq in i_neq_q.
                   rewrite (rht _ _ i_neq_q), cpr.
                   apply rigmult0x.
        * (* Shouldn't this be zero function ? *)
          destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
          ++ do 2 rewrite cpl.

             rewrite (pulse_function_sums_to_point_rig' r2).
             ** rewrite (stn_neq_or_neq_refl), cpl.
                rewrite <- i_eq_j.
                apply issymm_natneq in i_neq_r2.
                rewrite <- i_eq_r1.
                rewrite (rht _ _ i_neq_r2), cpr, cpl.
                rewrite stn_neq_or_neq_refl, cpl.
                apply riglunax2.
             ** unfold is_pulse_function.
                intros q r2_neq_q.
                destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
                --- rewrite cpl.
                    rewrite (rht _ _ r2_neq_q), cpr.
                    apply rigmult0x.
                --- rewrite cpr.
                    apply issymm_natneq in r2_neq_q.
                    rewrite (rht _ _ r2_neq_q), cpr.
                    rewrite <- i_eq_j, i_eq_r1.
                    rewrite (rht _ _ q_neq_r1), cpr.
                    apply rigmultx0.
          ++ do 2 rewrite cpr.
             rewrite cpl.
             apply zero_function_sums_to_zero.
             apply funextfun. intros q.
             destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
               --- rewrite cpl.
                   apply issymm_natneq in i_neq_r2.
                   destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
                   +++ rewrite cpl.
                       rewrite r2_eq_j, q_eq_r1, <- i_eq_r1.
                       apply issymm_natneq in i_neq_j.
                       rewrite (rht _ _ i_neq_j), cpr.
                       apply rigmult0x.
                   +++ rewrite cpr.
                       rewrite q_eq_r1, <- i_eq_r1.
                       rewrite (rht _ _ i_neq_r2), cpr.
                       apply rigmult0x.
               --- rewrite cpr.
                   destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
                   +++ rewrite cpl.
                       rewrite <- i_eq_r1.
                       rewrite (rht _ _ i_neq_j), cpr.
                       rewrite q_eq_r2.
                       rewrite  stn_neq_or_neq_refl, cpl.
                       apply rigmultx0.
                   +++ rewrite cpr.
                       apply issymm_natneq in q_neq_r2.
                       rewrite (rht _ _ q_neq_r2), cpr.
                       apply rigmult0x.
      + destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
        * destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
          -- rewrite  i_eq_r2, i_eq_j.
             do 2 rewrite cpl.
             rewrite (pulse_function_sums_to_point_rig' r1).
             ++ rewrite <- i_eq_j, <- i_eq_r2.
                do 2 rewrite (stn_neq_or_neq_refl), cpl.
                rewrite cpr.
                rewrite (stn_neq_or_neq_refl), cpl.
                apply riglunax2.
              ++ unfold is_pulse_function.
                intros q i_neq_q.
                apply issymm_natneq in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr, cpr.
                apply issymm_natneq in i_neq_q.
                rewrite (rht _ _ i_neq_q), cpr.
                apply rigmult0x.
          -- rewrite (pulse_function_sums_to_point_rig' i).
             ++ do 2 rewrite cpr.
                rewrite (rht _ _ i_neq_r1), cpr.
                rewrite cpl.
                apply issymm_natneq in i_neq_r1.
                rewrite (rht _ _ i_neq_r1), cpr.
                apply rigmult0x.
             ++ unfold is_pulse_function.
                intros q i_neq_q.
                rewrite cpr, cpl.
                apply issymm_natneq in i_neq_r1.
                destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
                ** rewrite cpl.
                   rewrite <- i_eq_r2.
                   rewrite (rht _ _ i_neq_j), cpr.
                   apply rigmultx0.
                ** rewrite cpr.
                   rewrite <- i_eq_r2.
                   apply issymm_natneq in i_neq_q.
                   rewrite (rht _ _ i_neq_q), cpr.
                   apply issymm_natneq in q_neq_r1.
                   rewrite (rht _ _ q_neq_r1), cpr.
                   apply rigmult0x.
        * (* Shouldn't this be zero function ? *)
          destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
          ++ rewrite cpl.
             rewrite (pulse_function_sums_to_point_rig' i).
             ** rewrite (rht _ _ i_neq_r1).
                do 3 rewrite cpr.
                rewrite (stn_neq_or_neq_refl), cpl.
                rewrite (rht _ _ i_neq_r2), cpr.
                rewrite (lft _ _ i_eq_j), cpl.
                apply riglunax2.
             ** unfold is_pulse_function.
                intros q r2_neq_q.
                destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
                --- rewrite cpl.
                    rewrite <- i_eq_j, cpr, cpr.
                    apply issymm_natneq in i_neq_r2.
                    rewrite (rht _ _ i_neq_r2), cpr.
                    apply rigmultx0.
                --- rewrite cpr.
                    apply issymm_natneq in r2_neq_q.
                    do 2 rewrite cpr.
                    apply issymm_natneq in r2_neq_q.
                    rewrite (rht _ _ r2_neq_q), cpr.
                    apply rigmult0x.
          ++ do 2 rewrite cpr.
             rewrite cpr.
             apply zero_function_sums_to_zero.
             apply funextfun. intros q.
             destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
               --- rewrite cpl.
                   apply issymm_natneq in i_neq_r2.
                   destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
                   +++ rewrite cpl.
                       rewrite q_eq_r1.
                       rewrite (rht _ _ i_neq_r1), cpr.
                       apply rigmult0x.
                   +++ rewrite cpr.
                       apply rigmultx0.
               --- rewrite cpr.
                   destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
                   +++ rewrite cpl.
                       rewrite q_eq_r2.
                       rewrite (rht _ _ i_neq_r2), cpr.
                       apply rigmult0x.
                   +++ rewrite cpr.
                       apply issymm_natneq in q_neq_r2.
                       destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
                       ---- rewrite cpl.
                            rewrite q_eq_j.
                            rewrite (rht _ _ i_neq_j), cpr.
                            apply rigmult0x.
                       ---- rewrite cpr.
                            apply rigmultx0.
  Defined.



  (* TODO: make R paramater/local section variable so that this can be stated *)
  (*
  Lemma matrix_scalar_multt_is_invertible { n : nat } (Mat : Matrix F n n) (s : F) (r : ⟦ n ⟧%stn) : matrix_is_invertible (make_scalar_mult_row_matrix s r).
  *)


  Lemma matrix_switch_row_is_elementary_row_op {n : nat} (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) :
    gauss_switch_row mat r1 r2 = ((make_gauss_switch_row_matrix n r1 r2) ** mat).
  Proof.
    intros.
  Abort.

  (* The following three lemmata test the correctness of elementary row operations, i.e. they do not affect the solution set. *)
  Lemma eq_sol_invar_under_scalar_mult {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_scalar_mult_row_matrix s r) ** A ** x)  = ((make_scalar_mult_row_matrix s r) ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_add {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_add_row_matrix r1 r2 s) ** A ** x)  = ((make_add_row_matrix r1 r2 s)  ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_switch {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_gauss_switch_row_matrix n r1 r2) ** A ** x)  = ((make_gauss_switch_row_matrix n r1 r2) ** (transpose b)).
  Proof.
    intros.
  Abort.






  (* Is it sufficient to prove this point, we might not need to verify the index corresponds to
     the maximum value ? *)
  (* ~ point of interest ~. How do we prove properties over folds ? *)
  Definition max_argmax_stnhq_bounded_geq_k  { n : nat } (vec : Vector F n) (pn : n > 0 ) (k : ⟦ n ⟧%stn) : pr2 (max_argmax_stnhq_bounded  vec pn k) ≥ k.
  Proof.
    intros.
    set (n' := 1).
    unfold max_argmax_stnhq_bounded.
    unfold max_hq_index_bounded.
    unfold foldleft.
    unfold nat_rect at 1.

    simpl.
  Admitted. (* A bit hard reasoning over fold - *)


  (* TODO : bound twice ? *)
  Definition select_pivot_row {n : nat} (mat : Matrix F n n) ( k : ⟦ n ⟧%stn )
    (pn : n > 0) : ⟦ n ⟧%stn.
   Proof.
     (*exact (pr2 (max_argmax_stnhq_bounded  ( ( λ i : (⟦ m ⟧%stn),  pr1 (max_argmax_stnhq ( ( mat) i) pn)) )  pm k ) ).*)
     exact (pr2 (max_argmax_stnhq_bounded ((transpose mat) k ) pn k)).
   Defined.



   (*
   (* iter starts at lastelement (n - 1) and goes to 0*)
   Definition argmax' { n : nat } (iter : nat) (v : Vector F n) (max' : F) (argmax' : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
   Proof.
     revert v max' argmax'.
     induction iter as [ | iter' IH]. (* TODO naming *)
     - intros v ? ?.
       induction (hqgehchoice max'(v firstelement)) as [g | l].
     intros v ? ?.
     set (argmax'' := decrement_stnn argmax').
     induction (hqgehchoice max' (v lastelement)) as [g | l].
     - IH
     -
     exact (max_hq max' (IH (@drop_el_vector F m v lastelement))). (* todo this or DNI ? *)
   Defined.

  Definition argmax { n : nat } (v : Vector F n) := argmax'
    *)
   (*
   Definition select_pivot_row' { n : nat } (mat: Matrix F n n) (k : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
   Proof.
     set (c := col mat k).
  *)

   (* Having an index variable k  0 .. n - 1,
     we want to certify that the selected pivot is >= k. *)
  Lemma pivot_idx_geq_k {n : nat} (mat : Matrix F n n) ( k : ⟦ n ⟧%stn )
    (pn : n > 0) : pr1 ( select_pivot_row mat k pn ) >= k.
  Proof.
    unfold select_pivot_row.
    unfold max_argmax_stnhq.
    unfold truncate_pr1.
    apply (max_argmax_stnhq_bounded_geq_k).
  Defined.

  (* Helper Lemma. Possibly unecessary. *)
  Local Definition opt_matrix_op {n : nat} (b : bool) (mat : Matrix F n n) (f : Matrix F n n -> Matrix F n n) : Matrix F n n.
  Proof.
    induction b.
    - exact (f mat).
    - exact mat.
  Defined.


  (* Stepwise Gaussian Elimination definitions *)

  (* We can probably assert at this point that m and n are > 0, as the base cases can be handled by caller *)
  (* Performed k times . *)
  (* We should be able to assert n, m > 0 wherever needed, by raa.*)
  Definition gauss_step  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n × ⟦ n ⟧%stn.
  Proof.
    assert (pn : (n > 0)). { exact (stn_implies_ngt0 k). }
    set (ik := (select_pivot_row mat k pn)). (* ≥ k *)
    use tpair. 2: {exact ik. }
    intros i j. (* lth S i ? *)
    destruct (natlthorgeh i (S k)) as [LT | GTH]. {exact ((mat i j)). }
    set (mat' := gauss_switch_row mat k ik).
    set (mat'' := gauss_scalar_mult_row mat' ((- 1%hq)%hq * (hqmultinv ( mat' k k )))%hq i).
    (*
    destruct (natgtb j k).
    - exact (((mat'' i j) + (mat'' i k) * (mat k j))%hq).
    - exact (mat'' i j).*)
    destruct (natlthorgeh j (S k)).
    - exact (mat'' i j).
    - exact (((mat'' i j) + (mat'' i k) * (mat'' k j))%hq).  (* mat'' or mat ?
                                                             This should be elementary row op ! *)
  Defined.


  Definition gauss_clear_column_step (n : nat) (k : (⟦ n ⟧%stn))
             (j : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    (*exact ((make_add_row_matrix k j (- (hqdiv (mat j k) (mat k k)))%hq
     ** mat)).*)
    exact ((make_add_row_matrix k j (- ( (mat j k) * hqmultinv (mat k k)))%hq
           ** mat)).
  Defined.

  Require Import UniMath.NumberSystems.Integers.

  Lemma hqldistr (x y z : hq) : paths (z * (x + y))%hq (z * x + z * y)%hq.
  Proof.
    intros.
    apply (rigldistr F x y z).
  Defined.

  Lemma hqrdistr (x y z : hq) : paths((x + y) * z)%hq (x * z + y * z)%hq.
  Proof.
    intros.
    apply (rigrdistr F x y z).
  Defined.


  Lemma hqminuscomm (x y : hq) : (x * - y)%hq = (- x * y)%hq.
    Proof.
  Admitted.


  Lemma hqmultcommminus (x y : hq) : paths (- x * y)%hq (- y * x)%hq.
    Proof.
  Admitted.

  (* The clear column step operation does clear the target row*)
  Lemma gauss_clear_column_step_inv1 (n : nat) (k : (⟦ n ⟧%stn))
        (j : (⟦ n ⟧%stn)) (k_neq_j : k ≠ j)  (mat : Matrix F n n) :
    (gauss_clear_column_step n k j mat) j k = 0%hq.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    unfold make_add_row_matrix, "**". (* TODO unfold matrix mult *)
    unfold row, col, transpose, flip, "^".
    assert (p : n > 0). { admit. }
    set (f := λ i, _).
    rewrite (@two_pulse_function_sums_to_points_rig' F n _ p k j). (*TODO fix ugly signature *)
    - unfold f.
      apply issymm_natneq in k_neq_j.
      rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
      unfold identity_matrix, Matrix.identity_matrix. (*TODO*)
      rewrite (stn_eq_or_neq_right k_neq_j), coprod_rect_compute_2.
      do 2 rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
      apply issymm_natneq in k_neq_j.
      rewrite (stn_eq_or_neq_right k_neq_j), coprod_rect_compute_2.
      rewrite (@rigrunax2 F), (@riglunax1 F), (@rigmultx0 F), (@rigrunax1 F).
      unfold const_vec.
      assert (p': mat k k != 0%hq). { admit. }
      etrans. { apply maponpaths. apply riglunax2. }
      rewrite <- hqmultcomm.
      set (c := 3).
      rewrite ( hqminuscomm (mat k k) _).
      rewrite <- hqmultassoc.
      rewrite hqmultcommminus.
      rewrite hqmultassoc.
      rewrite hqisrinvmultinv.
      2 : {exact p'. }
      rewrite hqmultr1.
      apply hqlminus.
    - intros i i_neq_k i_neq_j.
      unfold f.
      rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
      unfold identity_matrix, Matrix.identity_matrix. (*TODO *)
      apply issymm_natneq in i_neq_k.
      apply issymm_natneq in i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_k), coprod_rect_compute_2.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      rewrite hqplusl0.
      unfold const_vec.
      rewrite (rigmultx0 F (_)%hq).
      apply rigmult0x.
  Admitted. (*   remaining : n > 0     mat k k != 0%hq *)

  (* TODOs: several. This proof is terrible ? *)
  (* The clear column step operation only changes the target row*)
  Lemma gauss_clear_column_step_inv2 (n : nat) (k: (⟦ n ⟧%stn))
        (mat : Matrix F n n) (r : (⟦ n ⟧%stn)) : ∏ (j : ⟦ n ⟧%stn),
        (r ≠ j) -> (gauss_clear_column_step n k j mat) r j = mat r j.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    unfold make_add_row_matrix, "**".
    unfold "^", col, row, transpose, flip.
    assert (p : n > 0). { destruct n.
                          - apply weqstn0toempty in k.
                            contradiction.
                          - apply natgthsn0. }
    set (f := λ i : (⟦ n ⟧%stn), _).
    assert (b : Σ f = f r ). {
      apply (@pulse_function_sums_to_point_rig' F n r _).
      unfold is_pulse_function.
      intros q r_neq_k.
      unfold f.
      destruct (stn_eq_or_neq r j) as [r_eq_q | r_neq_q].
      - rewrite r_eq_q in X. (*TODO*)
        apply (isirrefl_natneq) in X.
        contradiction.
      - unfold identity_matrix, Matrix.identity_matrix. (* TODO *)
        rewrite coprod_rect_compute_2.
        rewrite (stn_eq_or_neq_right r_neq_k), coprod_rect_compute_2.
        apply rigmult0x.
    }
    rewrite b.
    unfold f.
    rewrite (stn_eq_or_neq_right X), coprod_rect_compute_2.
    unfold identity_matrix, Matrix.identity_matrix.
    rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
    apply (@riglunax2 F).
  Defined.

  (* iter from n -> 1, 0 return as we start with n - k (might = n)*)
  (* assumes we have the largest (non-zero) column-wise element at mat k k *)
  Definition gauss_clear_column ( n : nat ) (k : (⟦ n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    revert mat.
    induction (n - k) as [ | m gauss_clear_column_IH ]; intros mat. (*inv1 inv2.*)
    {exact mat. }
    set (piv := mat k k).
    (*set (pr1j := n - 1 - m). *)
    set (pr1j := n - 1 - m).
    assert (p: n - 1 - m < n).  (* TODO inline / refactor *)
    { apply (some_lemma m n k).  }
    set (j := make_stn n (pr1j) p).
    exact (gauss_clear_column_IH
               (gauss_clear_column_step n k j mat)).

  Defined.

  (* Now proving that the whole column is empty *)
  Lemma gauss_clear_column_invar { n : nat } (k j: (⟦ n ⟧%stn))
    (p : j > k) (mat : Matrix F n n) :
    (gauss_clear_column n j mat) k j = 0%hq.
  Proof.
    intros.
    unfold gauss_clear_column, nat_rect.
    unfold "**", "^", row, col, transpose, flip.
    - unfold gauss_clear_column_step.
      unfold make_add_row_matrix.
      (*destruct (natgthorleh (n - j) 0 ) as [nmj_gt_0 | nmj_le_0].
      2: { admit. } (*contradiction*)*)
      induction (natchoice0 (n - j)).
      +
  Abort.

  (* And proving no row < [ k ] is changed *)


  Lemma gauss_unchanged_invar { n : nat } (k r: ⟦ n ⟧%stn)
        (p : r < k) (mat : Matrix F n n) :
    (gauss_clear_column  n k  mat)  r = mat r.
  Proof.
    intros.
    unfold gauss_clear_column.
    unfold nat_rect.
  Abort.

  Fixpoint gauss_step_loop { n iter : nat } (k : (⟦ n ⟧%stn))
           (mat : Matrix F n n) { struct iter } : Matrix F n n.
  Proof.
    induction (natgehchoice n 0 ). 3: {apply natleh0n. } (* TODO should be a better induction *)
    2 : {exact mat. }
  Abort.


  Lemma gauss_step_upper_rows_invariant { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n):
    ∏ (k' : (⟦ n ⟧%stn)), k' < k -> (mat k') = (pr1 (gauss_step k mat) k').
  Proof.
    intros k' k'_lt_k.
    unfold gauss_step.
    apply pathsinv0.
    set (mat' := λ i j : (⟦ n ⟧%stn), _).
    assert (p : mat k' = mat' k').
    { unfold mat'.
      apply funextfun. intros q.
      destruct (natlthorgeh k' (S k)) as [k_lt_sk | k_ge_sk].
      - reflexivity.
      - apply pathsinv0.
        destruct (natlthorgeh q (S k)) as [sq_lt_sk | q_ge_sk].
        + clear mat'.
          apply natgehsntogth  in k_ge_sk.
          apply isasymmnatgth in k'_lt_k. 2 : {assumption. }
          contradiction.
        + clear mat'.
          apply natgehsntogth in k_ge_sk.
          apply isasymmnatgth in k'_lt_k. 2 : {assumption. }
          contradiction.
    }
    rewrite p.
    apply funextfun. intros q.
    reflexivity.
  Defined.

  Lemma gauss_step_clears_diagonal { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    (*∏ (i j: ⟦ n ⟧%stn), (i > k) -> ((n - k) > j) -> mat i j = 0%hq ->
    ∏ (i' j' : ⟦ n ⟧%stn), (i' >= k) -> ((n - k) >= j') -> (pr1 (gauss_step k mat)) i' j' = 0%hq.*)
    ∏ j : ⟦ n ⟧%stn, (j > k) -> (pr1 (gauss_step k mat)) j k = 0%hq.
  Proof.
    (*intros i j i_geq_k nmk_geq_j mat_ik_eq_0 i' j' i'_geq_k nmk_geq_j'.*)
    intros j j_gt_k.
    unfold gauss_step. simpl.
    destruct (natlthorgeh j (S k)) as [j_lt_sk | j_geh_sk].
    - apply natgthsntogeh in j_lt_sk.
      apply natgehtonegnatlth in j_lt_sk.
      contradicts j_gt_k j_lt_sk.
    - destruct (natlthorgeh k (S k)) as [k_lt_sk | k_geh_sk].
      + clear j_geh_sk. clear k_lt_sk.
        unfold gauss_scalar_mult_row, gauss_switch_row.
        do 2 rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
        assert (p: j ≠ k). {admit. } (*trivial *)
        rewrite (stn_eq_or_neq_right p), coprod_rect_compute_2.
        destruct (stn_eq_or_neq j (select_pivot_row mat k _)).
        * rewrite coprod_rect_compute_1.
          set (piv := select_pivot_row _ _ _).
          (* Not true ! Where did we go wrong ? *)

        simpl. admit.
        * admit.
      + admit.
  Abort. (* We want to show that the pivot selection selects a pivot >= k *)


  (* k  : 1 -> n - 1 *)
  Definition vec_row_ops_step { n : nat } (k pivot_ik: ⟦ n ⟧%stn)  (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    induction (natlthorgeh i k). 2 : {exact (vec i). }
    set (vec' := switch_vector_els vec pivot_ik k).
    assert (pr2stn1 : 0 < 1). { reflexivity. }
    set ( j := make_stn 1 0 pr2stn1).
    exact (  ((((vec' i)) + ((vec' k)) * (mat i k))%hq)).  (* Would like to verify this construction works*)
  Defined.



  (* This one especially needs to be checked for correctness (use of indices) *)
  Definition back_sub_step { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    induction (natlehchoice ((S (pr1 iter)) ) (n)) as [LT | GTH].
    - exact ((((vec i) - Σ (clamp_f vec i)) * (hqmultinv (mat i i)))%hq).
    - exact ((vec i) * (hqmultinv (mat i i)))%hq.
    - unfold stn in i.
      apply (pr2 iter).
  Defined.




  (* Now, three fixpoint definitions for three subroutines.
     Partial pivoting on "A", defining b according to pivots on A,
     then back-substitution. *)
  Definition gauss_iterate
     ( pr1i : nat ) { n : nat }
     (start_idx : ⟦ n ⟧%stn ) (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n)
    : (Matrix F n n) × (Vector (⟦ n ⟧%stn) n).
  Proof.
    revert mat pivots.
    induction pr1i as [ | m gauss_iterate_IH ]; intros mat pivots.
    { (* pr1i = 0 *) exact (mat,,pivots). }
    set (current_idx := decrement_stn_by_m start_idx (n - (S m))).
    set (idx_nat := pr1 current_idx).
    set (proof   := pr2 current_idx).
    set (mat_vec_tup := ((gauss_step current_idx mat))).
    set (mat' := pr1 mat_vec_tup).
    set (piv  := (pr2 mat_vec_tup)).
    set (pivots' := set_stn_vector_el pivots current_idx piv).
    exact (gauss_iterate_IH mat' pivots').
  Defined.

  Definition gauss_clears_diagonal : True.
    Proof.
  Abort.



  Fixpoint vec_ops_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
    let current_idx := decrement_stn_by_m start_idx (n - iter)  in
    match iter with
    | 0 => b
    | S m => vec_ops_iterate m start_idx (vec_row_ops_step current_idx (pivots current_idx) mat b) pivots mat
    end.

  Fixpoint back_sub_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
    let current_idx := decrement_stn_by_m start_idx (n - iter)  in
    match iter with
    | 0 => b
    | S m => back_sub_iterate m start_idx ( back_sub_step current_idx mat b) pivots mat
    end.


  (* The main definition using above Fixpoints, which in turn use stepwise definitions.*)
  Definition gaussian_elimination { n : nat } (mat : Matrix F n n) (b : Vector F n) (pn : n > 0) : Matrix F n n × Vector F n.
  Proof.
    set (A_and_pivots := gauss_iterate n (0,,pn) mat (zero_vector_stn n)).
    set (A  := pr1 A_and_pivots).
    set (pv := pr2 A_and_pivots).
    set (b'  := vec_ops_iterate 0 (0,,pn) b pv A).
    set (b'' := back_sub_iterate n (0,, pn) b' pv A).
    exact (A,, b').
  Defined.

  Definition gauss_solution_invar : True.
  Proof.
  Abort.


  (* Some properties on the above procedure which we would like to prove. *)

  Definition is_upper_triangular { m n : nat } (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < j -> mat i j = 0%hq.

  Lemma gauss_upper_trianglar : True.
  Proof.
  Abort.

  Definition is_upper_triangular_to_k { m n : nat} ( k : nat ) (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < k -> i < j -> mat i j = 0%hq.


  Lemma gauss_step_clears_row  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    is_upper_triangular_to_k (pr1 k) (pr1 (gauss_step k mat)).
  Proof.
    intros.
  Abort.

  Lemma A_is_upper_triangular { n : nat} ( temp_proof_0_lt_n : 0 < n ) (mat : Matrix F n n) :
    is_upper_triangular (pr1 (gauss_iterate 0 (0,, temp_proof_0_lt_n) mat (zero_vector_stn n))).
  Proof.
    intros.
  Abort.


  (* Reliance on pn, coercing matrices could be done away with. *)
  Lemma sol_is_invariant_under_gauss  {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n)  (pn : n > 0) (pn' : 1 > 0) :
    (A ** x) = (transpose b) -> ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** A ** x)  = ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** (transpose b)).
  Proof.
    intros.
  Abort.





  (* Determinants, minors, minor expansions ... *)

  (* TODO : Verify this is close to accurate ... *)
  Definition make_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix F (S n) (S n)) : Matrix F n n.
  Proof.
    intros i' j'.
    assert (bound_si : (S i') < (S n)). {exact (pr2 i'). }
    assert (bound_sj : (S j') < (S n)). {exact (pr2 j'). }
    set (stn_si := make_stn (S n) (S i') bound_si).
    set (stn_sj := make_stn (S n) (S j') bound_sj).
    induction (natgtb i'  (i - 1)).
    - induction (natgtb j' (j - 1)).
      + exact (mat (stnmtostnn n (S n) (natlehnsn n) i') (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat ((stnmtostnn n (S n) (natlehnsn n) i')) stn_sj).
    - induction (natgtb j' (j - 1)).
      + exact (mat stn_si  (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat stn_si stn_sj).
  Defined.


  (* TODO: need to figure out the recursive step ! *)
  (*
  Definition determinant_step { n : nat} (mat : Matrix F (S n) (S n)) : (Matrix F n n) × F.
  Proof.
    set (exp_row := 0).
    use tpair.
    - (* Minors *)
      intros i j.
      (* Carefully do induction on S n, not n. *)
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
(*
          assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                    - apply natlthnsn.
                                    - apply (istransnatgth n 1 0).
                                      + apply
G.
                                      + reflexivity.
                                   }
*)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].
          * exact 1%hq.
          * assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                       - apply natlthnsn.
                                       - apply (istransnatgth n 1 0).
                                         + apply G.
                                         + reflexivity.
                                     }
            assert (x' : 1 < (S n)). {apply (istransnatgth (S n) n 1).
                                       - apply natlthnsn.
                                       - apply G. }
            assert (pexp : exp_row < S n). { reflexivity. }
            assert (psj : (pr1 j) < S n). {  apply natlthtolths. exact (pr2 j). }.
            set (stn_0 := make_stn (S n) 0 x ).
            set (stn_1 := make_stn (S n) 1 x').
            set (cof := 1%hq). (* TODO : this is a dummy for (-1)^(i + j) *)
            exact (Σ (λ j : (⟦ S n ⟧%stn), cof * (mat (exp_row,, pexp) (j)))%hq).
    - (* Scalar terms *)
      intros i j.
      set (exp_row := 0).
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].

    induction (natgtb n 1) as [T | F].
    - induction (nat_eq_or_neq n 2) as [T' | F'].
      assert (x :  0 < (S n)). {rewrite T'. reflexivity.}.
      assert (x' : 1 < (S n)). {rewrite T'. reflexivity.}.
      set (stn_0 := make_stn (S n) 0 x).
      set (stn_1 := make_stn (S n) 1 x').
      + exact (1%hq,, (mat stn_0 stn_0) * (mat stn_1 stn_1) - (mat stn_0 stn_1) * (mat stn_1 stn_0))%hq).
      + set (cof := 1). (* TODO : this is a dummy for (-1)^(i + j) *)
        exact (Σ (λ j : (⟦ n ⟧%stn), cof * mat ( exp_row j) (determinant ( make_minor i j mat)))).  (* TODO *)
    - induction (nat_eq_or_neq n 0).
      + exact 0%hq.
      + assert (x :  0 < n). {apply natneq0togth0. assumption.}
        set (stn_0 := make_stn n 0 x).
        exact (mat stn_0 stn_0).
  Defined.
  *)

  (*How do we produce either a smaller matrix or scalar value? *)
  (*
  Fixpoint determinant_iter {n : nat} (mat : Matrix F (S n) (S n)) := Matrix F n n.
  *)


End Gauss.





Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.

  Local Notation Σ := (iterop_fun 0%hz op1).

  (* Does feel wasteful having to redefine this constantly - TODO coercions *)
  (* TODO standardize use of the following unfolded definition or use
     rows / cols here too *)
  Local Definition matrix_mult_hz {m n : nat} (mat1 : Matrix I m n)
    {p : nat} (mat2 : Matrix I n p) : (Matrix I m p) :=
    λ i j, Σ (λ k, (mat1 i k * mat2 k j))%hz.

  Local Notation "A ** B" := (matrix_mult_hz A B) (at level 80).

  Lemma minab_le_b (a b : nat) : min a b ≤ a.
  Proof.
  Admitted.
  Lemma minab_le_a (a b : nat) : min a b ≤ b.
  Proof.
  Admitted.

  Lemma minabstn_to_astn { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ a ⟧%stn.
  Proof.
  Admitted.

  Lemma minabstn_to_bstn { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ b ⟧%stn.
  Proof.
  Admitted.

  Definition mat_to_square_mat { m n : nat } (mat : Matrix I m n) : Matrix I (min m n) (min m n).
  Proof.
    intros.
    exact (λ i j : ⟦min m n⟧%stn, mat (minabstn_to_astn i) (minabstn_to_bstn j)).
  Defined.

  (* Such code might go intro Matrix.v *)
  Definition is_diagonal { m n : nat } (mat : Matrix I m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i != (stntonat _ j)) -> (mat i j) = 0%hz.

  Definition is_smithnf { m n : nat } (A : Matrix I m n) :
    ∑ (S : Matrix I m m), ∑ (T : Matrix I n n),
    is_diagonal  (S ** A ** T) ×
    ∏ (i j : ⟦ min n m ⟧%stn), i < j ->
    hzdiv (A (minabstn_to_bstn i) (minabstn_to_astn i))
    (A (minabstn_to_bstn j) (minabstn_to_astn i)).
  Abort.

  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.



End SmithNF.

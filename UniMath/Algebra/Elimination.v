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

Local Definition R := pr1hSet natcommrig.

Section Gauss.
  (* Gaussian elimination over the field of rationals *)

  Local Definition F := pr1hSet hq.


  Definition gauss_add_row {m n : nat} (mat : Matrix F m n)
             (r1 r2 : ⟦ m ⟧%stn) : (Matrix F m n).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (op1 (mat r1 j)  (mat r2 j)). (* Target row *)
    - exact (mat r1 j). (* Regular row (ID)*)
  Defined.


  (* Is stating this as a Lemma more in the style of other UniMath work?*)
  Local Definition identity_matrix {n : nat} : (Matrix F n n).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
    - exact 1%hq.
    - exact 0%hq.
  Defined.



  (* Need again to restate several definitions to use the identity on rationals*)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Local Definition matrix_mult {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  (* Can be defined inductively, directly, too.*)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn)  :=
    gauss_add_row (identity_matrix) r1 r2.

  Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) : Matrix F m n :=
    (make_add_row_matrix r1 r2) **  mat.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
             (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
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

  (*  This might be a non-trivial property to prove, especially in the current double induction-based formalization.*)
  Definition test_row_switch_statement {m n : nat} (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) := (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.


  (* Do we need to redefine this ? *)
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
    + exact (λ i : (⟦ n - 1 ⟧%stn), 0%hq). (* Zero length vector with placeholder *)
  Defined.


(*
  Fixpoint argmax_stnhq'  { n : nat } (vec' : Vector F n) (max' : F) (idx : nat) : nat :=
    match n with
    | 0 => idx (*max'*)
    | _ =>
      match (max_hq max' (argmax_stnhq'  (tl' vec' ) max' idx) )
      with | max' -> idx
           | _    ->
    end.
*)
  (* We can generalize this to just ordered sets *)

  (*Definition max_hq_index (e : F)  (i : nat) (e' : F) (i' : nat) : hq × nat.
*)Definition max_hq_index (ei ei' : hq × nat) : hq × nat.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact (ei).
    - exact (ei').
  Defined.

  Definition max_hq_index_one_arg (ei : hq × nat)  : hq × nat -> hq × nat
    := max_hq_index ei.

  Definition max_argmax_stnhq {n : nat} (vec : Vector F n) : hq × nat
    :=  (foldleft (0%hq ,, 0) (max_hq_index_one_arg) (λ i : (⟦ n ⟧%stn), (vec i) ,, (stntonat _ i))).

  Definition select_pivot_row {m n : nat} (mat : Matrix F n n) ( k : nat ) : nat
    := pr2 (max_argmax_stnhq  ( λ i : (⟦ n ⟧%stn),  pr1 (max_argmax_stnhq ( ((transpose mat) i))))).

  (* partial pivoting *)
  (*
  Definition gauss_step { m : nat } { n : nat } (h : (⟦ m ⟧%stn)) (k : (⟦ n ⟧%stn)) (mat : Matrix F m n) : Matrix F m n.
  induction
  *)

  (* TODO : this one has reversed, incorrect induction steps ... *)
  Definition make_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix F (S n) (S n)) : Matrix F n n.
  Proof.
    intros i' j'.
    assert (bound_n : n <= (S n)). { exact (natlehnsn n). }
    assert (bound_sn : (S n) <= (S n)). { change ((S n) <= (S n)) with (n <= n). apply isreflnatleh. }
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

  (* TODO recursive step *)
  (*
  Definition determinant { n : nat} (mat : Matrix F n n) : F.
  Proof.
    intros.
    set (exp_row := 0).
    induction (natgtb n 1).
    - induction (nat_eq_or_neq n 2).
      assert (x :  0 < n). {rewrite a. reflexivity.}.
      assert (x' : 1 < n). {rewrite a. reflexivity.}.
      set (stn_0 := make_stn n 0 x).
      set (stn_1 := make_stn n 1 x').
      + exact ((mat stn_0 stn_0) * (mat stn_1 stn_1) - (mat stn_0 stn_1) * (mat stn_1 stn_0))%hq.
      + set (cof := 1). (* TODO : this is a dummy for (-1)^(i + j) *)
        exact (Σ (λ j : (⟦ n ⟧%stn), cof * mat ( exp_row j) (determinant ( make_minor i j mat)))).  (* TODO *)
    - induction (nat_eq_or_neq n 0).
      + exact 0%hq.
      + assert (x :  0 < n). {apply natneq0togth0. assumption.}
        set (stn_0 := make_stn n 0 x).
        exact (mat stn_0 stn_0).
  Defined.
  *)

End Gauss.


Section SmithNF.
 (* Generalized elimination over the ring of integers *)



(* Such code might go intro Matrix.v *)
Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
  ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i != (stntonat _ j)) -> (mat i j) = 0%rig.


End SmithNF.

(*
Definition divisibility_over_diagonal {m n : nat} (mat : Matrix R m n) := *)

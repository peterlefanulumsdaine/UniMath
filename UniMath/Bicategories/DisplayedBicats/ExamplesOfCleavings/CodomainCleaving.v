Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

(**
The codomain displayed bicategory has a cleaving
Here we assume that every 2-cell is invertible
 *)
Section CodomainCleaving.
  Context (B : bicat).

  Definition cod_invertible_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : cod_disp_bicat B c₁}
             {t₂ : cod_disp_bicat B c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
             (Hαα : is_invertible_2cell (pr1 αα))
    : is_cartesian_2cell (cod_disp_bicat B) αα.
  Proof.
    intros h hh γ γα.
    cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply (cod_disp_bicat B) | ] ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         pose (maponpaths pr1 (pr2 φ₁)) as p₁ ;
         cbn in p₁ ;
         pose (maponpaths pr1 (pr2 φ₂)) as p₂ ;
         cbn in p₂ ;
         pose (r := p₁ @ !p₂) ;
         use (vcomp_rcancel _ Hαα) ;
         exact r).
    - simple refine ((_ ,, _) ,, _).
      + exact (pr1 γα • Hαα^-1).
      + abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite (pr2 γα) ;
           rewrite <- lwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- (pr2 αα) ;
           rewrite !vassocl ;
           rewrite rwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           apply id2_right).
      + abstract
          (use subtypePath ; [ intro ; apply cellset_property | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite vcomp_linv ;
           apply id2_right).
  Defined.

  Context (inv_B : locally_groupoid B)
          (pb_B : has_pb B).

  Definition cod_local_cleaving
    : local_cleaving (cod_disp_bicat B).
  Proof.
    intros x y hx hy f g hf hg.
    simple refine (_ ,, _).
    - simple refine (pr1 hf ,, pr2 hx ◃ hg • pr12 hf ,, _).
      cbn.
      is_iso.
      + apply inv_B.
      + apply (pr22 hf).
    - simple refine (_ ,, _).
      + simple refine (id2 _ ,, _).
        abstract
          (cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_right ;
           apply idpath).
      + simpl.
        apply cod_invertible_is_cartesian_2cell ; cbn.
        is_iso.
  Defined.

  (** Characterization of cartesian 1-cells *)
  Section PullbackToCartesian.
    Context {x y : B}
            {f : x --> y}
            {hx : cod_disp_bicat B x}
            {hy : cod_disp_bicat B y}
            (π : pr1 hx --> pr1 hy)
            (p : invertible_2cell (pr2 hx · f) (π · pr2 hy))
            (pb := make_pb_cone (pr1 hx) (pr2 hx) π p)
            (pb_sqr : has_pb_ump pb).

    Section Lift1CellConeMor.
      Context {z : B}
              {hz : cod_disp_bicat B z}
              {g : z --> x}
              (hg : hz -->[ g · f] hy).

      Let other_cone : pb_cone f (pr2 hy)
        := make_pb_cone
             (pr1 hz)
             (pr2 hz · g)
             (pr1 hg)
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell _ _ _)
                (pr2 hg)).

      Definition lift_1cell_to_pb_1cell
                 (Hg : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg)
        : pb_1cell other_cone pb.
      Proof.
        use make_pb_1cell.
        - exact (pr11 Hg).
        - use inv_of_invertible_2cell.
          exact (pr21 Hg).
        - use make_invertible_2cell.
          + exact (pr112 Hg).
          + apply inv_B.
        - abstract
            (pose (pr212 Hg) as q ;
             cbn ; cbn in q ;
             rewrite lwhisker_id2 in q ;
             rewrite id2_left in q ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn) ;
             rewrite !vassocr ;
             do 2 (use vcomp_move_L_Mp ; [ is_iso | ] ; cbn) ;
             exact q).
      Defined.

      Definition pb_1cell_to_lift_1cell
                 (Hg : pb_1cell other_cone pb)
        : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg.
      Proof.
        simple refine ((_ ,, _) ,, ((_ ,, _) ,, _)).
        - exact (pb_1cell_1cell Hg).
        - exact (inv_of_invertible_2cell (pb_1cell_pr1 Hg)).
        - exact (pr1 (pb_1cell_pr2 Hg)).
        - abstract
            (cbn ;
             pose (pb_1cell_eq Hg) as q ;
             cbn in q ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_R_pM ; [ is_iso | ] ; cbn) ;
             refine (maponpaths (λ z, z • _) q @ _) ; clear q ;
             rewrite !vassocl ;
             do 3 apply maponpaths ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
             rewrite !vassocr ;
             rewrite rassociator_lassociator ;
             rewrite id2_left, id2_right ;
             apply idpath).
        - use is_disp_invertible_2cell_cod.
          exact (pr2 (pb_1cell_pr2 Hg)).
      Defined.
    End Lift1CellConeMor.

    Definition is_pb_to_cartesian_lift_1cell
               {z : B}
               {hz : cod_disp_bicat B z}
               {g : B ⟦ z, x ⟧}
               (hg : hz -->[ g · f] hy)
      : lift_1cell_factor (cod_disp_bicat B) (π,, p) hg.
    Proof.
      apply pb_1cell_to_lift_1cell.
      apply (has_pb_ump_1 pb pb_sqr).
    Defined.

    Section Lift2CellConeCell.
      Context {c : B}
              {cc : cod_disp_bicat B c}
              {h h' : c --> x}
              {gg : cc -->[ h · f] hy}
              {gg' : cc -->[ h' · f] hy}
              {δ : h ==> h'}
              (σσ : gg ==>[ δ ▹ f] gg')
              (Lh : lift_1cell_factor (cod_disp_bicat B) (π,, p) gg)
              (Lh' : lift_1cell_factor (cod_disp_bicat B) (π,, p) gg').

      Definition lift_2cell_cone
        : UU
        := ∑ (α : pr11 Lh ==> pr11 Lh'),
           (pr121 Lh • (α ▹ pr2 hx) = (pr2 cc ◃ δ) • pr121 Lh')
           ×
           ((α ▹ π) • pr112 Lh' = pr112 Lh • pr1 σσ).

      Definition cone_cell_to_lift_2cell
                 (α : pr11 Lh ==> pr11 Lh')
                 (α_pr1 : pr121 Lh • (α ▹ pr2 hx) = (pr2 cc ◃ δ) • pr121 Lh')
                 (α_pr2 : (α ▹ π) • pr112 Lh' = pr112 Lh • pr1 σσ)
        : lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        simple refine ((α ,, α_pr1) ,, _).
        use subtypePath ; [ intro ; apply cellset_property | ].
        simpl.
        rewrite pr1_transportf.
        rewrite transportf_const.
        cbn.
        exact α_pr2.
      Defined.

      Definition lift_2cell_to_cone_cell
                 (α : lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh')
        : lift_2cell_cone.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact (pr11 α).
        - exact (pr21 α).
        - abstract
            (pose (maponpaths pr1 (pr2 α)) as q ;
             cbn ;
             simpl in q ;
             rewrite pr1_transportf in q ;
             rewrite transportf_const in q ;
             exact q).
      Defined.

      Definition cone_cell_weq_lift_2cell
        : lift_2cell_cone
          ≃
          lift_2cell_factor_type (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        use make_weq.
        - exact (λ z, cone_cell_to_lift_2cell (pr1 z) (pr12 z) (pr22 z)).
        - use gradth.
          + exact lift_2cell_to_cone_cell.
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply (cod_disp_bicat B) | ] ;
               use subtypePath ;
               [ intro ; apply cellset_property | ] ;
               apply idpath).
      Defined.

      Let cone : pb_cone f (pr2 hy)
        := make_pb_cone
             (pr1 cc) (pr2 cc · h') (pr1 gg')
             (comp_of_invertible_2cell
                (rassociator_invertible_2cell (pr2 cc) h' f)
                (pr2 gg')).

      Let cell₂ : pb_1cell cone pb := lift_1cell_to_pb_1cell _ Lh'.

      Local Definition cell₁ : pb_1cell cone pb.
      Proof.
        pose (lift_1cell_to_pb_1cell _ Lh) as lift.
        use make_pb_1cell.
        - exact lift.
        - exact (comp_of_invertible_2cell
                   (pb_1cell_pr1 lift)
                   (lwhisker_of_invertible_2cell
                      _
                      (δ ,, inv_B _ _ _ _ _))).
        - exact (comp_of_invertible_2cell
                   (pb_1cell_pr2 lift)
                   (pr1 σσ ,, inv_B _ _ _ _ _)).
        - abstract
            (cbn ;
             pose (pb_1cell_eq lift) as q ;
             cbn in q ;
             rewrite q ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- rwhisker_lwhisker_rassociator ;
             do 2 apply maponpaths_2 ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite !vassocr ;
             use vcomp_move_L_Mp ; [ is_iso | ] ; cbn ;
             exact (pr2 σσ)).
      Defined.

      Definition pb_2cell_to_cone_cell
                 (α : pb_2cell cell₁ cell₂)
        : lift_2cell_cone.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact α.
        - abstract
            (pose (pb_2cell_pr1 α) as q ;
             cbn in q ;
             refine (!(id2_right _) @ _) ;
             etrans ;
               [ apply maponpaths ;
                 refine (!_) ;
                 exact (vcomp_linv (pr221 Lh'))
               | ] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             refine (maponpaths (λ z, _ • z) q @ _) ;
             rewrite !vassocr ;
             rewrite vcomp_rinv ;
             apply id2_left).
        - exact (pb_2cell_pr2 α).
      Defined.

      Definition cone_cell_to_pb_2cell
                 (α : lift_2cell_cone)
        : pb_2cell cell₁ cell₂.
      Proof.
        use make_pb_2cell.
        - exact (pr1 α).
        - abstract
            (pose (pr12 α) as q ;
             cbn ;
             use vcomp_move_R_Mp ; [ is_iso | ] ;
             rewrite !vassocl ;
             use vcomp_move_L_pM ; [ is_iso | ] ;
             cbn ;
             exact q).
        - exact (pr22 α).
      Defined.

      Definition pb_2cell_weq_cone_cell
        : pb_2cell cell₁ cell₂ ≃ lift_2cell_cone.
      Proof.
        use make_weq.
        - exact pb_2cell_to_cone_cell.
        - use gradth.
          + exact cone_cell_to_pb_2cell.
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
          + abstract
              (intro ;
               use subtypePath ;
               [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
               apply idpath).
      Defined.

      Definition is_pb_to_cartesian_lift_2cell
        : lift_2cell_factor (cod_disp_bicat B) (π,, p) σσ Lh Lh'.
      Proof.
        use (iscontrweqf cone_cell_weq_lift_2cell).
        use (iscontrweqf pb_2cell_weq_cone_cell).
        apply pb_2cell_contr.
        apply pb_sqr.
      Defined.
    End Lift2CellConeCell.

    Definition is_pb_to_cartesian_1cell
      : cartesian_1cell (cod_disp_bicat B) (π ,, p).
    Proof.
      split.
      - exact @is_pb_to_cartesian_lift_1cell.
      - exact @is_pb_to_cartesian_lift_2cell.
    Defined.
  End PullbackToCartesian.

  Section CartesianToPullback.
    Context {x y : B}
            {f : x --> y}
            {hx : cod_disp_bicat B x}
            {hy : cod_disp_bicat B y}
            (π : pr1 hx --> pr1 hy)
            (p : invertible_2cell (pr2 hx · f) (π · pr2 hy))
            (Hp : cartesian_1cell (cod_disp_bicat B) (π,, p)).

    Let pb := make_pb_cone (pr1 hx) (pr2 hx) π p.

    Definition cartesian_1cell_pb_ump_1
      : pb_ump_1 pb.
    Proof.
      intro q.
      pose (pr1 Hp x (make_ar (pb_cone_pr1 q)) (id₁ _)
                (pb_cone_pr2 q ,, comp_of_invertible_2cell
                             (lwhisker_of_invertible_2cell
                                _
                                (lunitor_invertible_2cell _))
                             (pb_cone_cell q))) as w.
      pose (lift_1cell_to_pb_1cell π p _ w).
      cbn in p0.
      use make_pb_1cell.
      - exact p0.
      - pose (pb_1cell_pr1 p0).
        cbn.
        cbn in i.
        refine (comp_of_invertible_2cell i (runitor_invertible_2cell _)).
      - exact (pb_1cell_pr2 p0).
      - refine (pb_1cell_eq p0 @ _) ; cbn.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        apply lunitor_lwhisker.
    Defined.

    Section PbUMP2AndEq.
      Context {q : pb_cone f (pr2 hy)}
              (φ ψ : pb_1cell q pb).

      Let g : cod_disp_bicat B x := (make_ar (pb_cone_pr1 q)).
      Let χ : g -->[ id₁ x · f] hy
        := make_disp_1cell_cod
             (dX := g) (dY := hy)
             (pb_cone_pr2 q)
             (comp_of_invertible_2cell
                (lwhisker_of_invertible_2cell
                   _
                   (lunitor_invertible_2cell _))
                (pb_cone_cell q)).

      Local Definition pχ
        : χ ==>[ id₂ (id₁ x) ▹ f] χ.
      Proof.
        use make_disp_2cell_cod.
        - apply id2.
        - abstract
            (unfold coherent_homot ; cbn ;
             rewrite !id2_rwhisker, lwhisker_id2, id2_left, id2_right ;
             apply idpath).
      Defined.

      Local Definition lift_1cell_of_pb_1cell
            (ζ : pb_1cell q pb)
        : lift_1cell_factor (cod_disp_bicat B) (π,, p) χ.
      Proof.
        simple refine ((_ ,, _) ,, ((_ ,, _) ,, _)).
        - exact (pr1 ζ).
        - exact (comp_of_invertible_2cell
                   (runitor_invertible_2cell _)
                   (inv_of_invertible_2cell (pb_1cell_pr1 ζ))).
        - exact (pr1 (pb_1cell_pr2 ζ)).
        - abstract
            (cbn ;
             pose (pb_1cell_eq ζ) as r ;
             cbn in r ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             do 3 (use vcomp_move_R_pM ; [ is_iso | ]) ;
             cbn ;
             refine (maponpaths (λ z, z • _) r @ _) ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 2 apply maponpaths ;
             rewrite (maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite (maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite lunitor_lwhisker ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite rinvunitor_runitor ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             apply idpath).
        - apply is_disp_invertible_2cell_cod.
          apply (pb_1cell_pr2 ζ).
      Defined.

      Let lift_φ : lift_1cell_factor (cod_disp_bicat B) (π,, p) χ
        := lift_1cell_of_pb_1cell φ.
      Let lift_ψ : lift_1cell_factor (cod_disp_bicat B) (π,, p) χ
        := lift_1cell_of_pb_1cell ψ.

      Definition cartesian_ump_2
        : pb_2cell φ ψ.
      Proof.
        pose (pr2 Hp _ g (id₁ _) (id₁ _) χ χ (id2 _) pχ lift_φ lift_ψ) as l.
        use make_pb_2cell.
        - exact (pr111 l).
        - abstract
            (cbn ;
             pose (pr211 l) as d ;
             cbn in d ;
             rewrite lwhisker_id2, id2_left in d ;
             rewrite !vassocl in d ;
             pose (maponpaths (λ z, rinvunitor _ • z) d) as d' ;
             cbn in d' ;
             rewrite !vassocr in d' ;
             rewrite !rinvunitor_runitor, !id2_left in d' ;
             use vcomp_move_R_Mp ; [ apply (pb_1cell_pr1 ψ) | ] ; cbn ;
             use vcomp_move_L_pM ; [ apply (pb_1cell_pr1 φ) | ] ; cbn ;
             exact d').
        - abstract
            (pose (maponpaths pr1 (pr21 l)) as d ;
             simpl in d ;
             rewrite pr1_transportf in d ;
             rewrite transportf_const in d ;
             cbn in d ;
             rewrite id2_right in d ;
             exact d).
      Defined.


      Definition pb_2cell_to_lift
                 (r : pb_2cell φ ψ)
        : lift_2cell_factor_type
            (cod_disp_bicat B)
            (π ,, p)
            pχ
            lift_φ lift_ψ.
      Proof.
        simple refine ((_ ,, _) ,, _) ; cbn.
        - exact r.
        - abstract
            (pose (pb_2cell_pr1 r) as w ;
             cbn in w ;
             rewrite !vassocr ;
             use vcomp_move_L_Mp ; [ is_iso | ] ;
             cbn ;
             rewrite !vassocl ;
             refine (maponpaths (λ z, _ • (_ • z)) w @ _) ;
             rewrite vcomp_linv ;
             rewrite id2_right ;
             rewrite lwhisker_id2 ;
             rewrite id2_left ;
             apply idpath).
        - abstract
            (use subtypePath ; [ intro ; apply cellset_property | ] ;
             simpl ;
             rewrite pr1_transportf ;
             rewrite transportf_const ;
             cbn ;
             rewrite id2_right ;
             exact (pb_2cell_pr2 r)).
      Defined.

      Context (r₁ r₂ : pb_2cell φ ψ).

      Definition cartesian_ump_eq
        : r₁ = r₂.
      Proof.
        pose (pr2 Hp _ g (id₁ _) (id₁ _) χ χ (id2 _) pχ lift_φ lift_ψ) as l.
        pose (proofirrelevance
                _
                (isapropifcontr l)
                (pb_2cell_to_lift r₁)
                (pb_2cell_to_lift r₂)) as eq.
        use subtypePath.
        {
          intro ; apply isapropdirprod ; apply cellset_property.
        }
        exact (maponpaths (λ z, pr11 z) eq).
      Qed.
    End PbUMP2AndEq.

    Definition cartesian_1cell_to_is_pb
      : has_pb_ump pb.
    Proof.
      use make_has_pb_ump.
      - exact cartesian_1cell_pb_ump_1.
      - exact @cartesian_ump_2.
      - exact @cartesian_ump_eq.
    Defined.
  End CartesianToPullback.

  Definition cod_global_cleaving
    : global_cleaving (cod_disp_bicat B).
  Proof.
    intros x y hx f ; cbn in *.
    pose (pb_B _ _ _ f (pr2 hx)) as pb.
    pose (pr1 pb) as pb₁.
    pose (pr2 pb) as pb₂.
    simple refine ((_ ,, _) ,, (_ ,, _) ,, _) ; cbn.
    - exact pb₁.
    - exact (pb_cone_pr1 pb₁).
    - exact (pb_cone_pr2 pb₁).
    - exact (pb_cone_cell pb₁).
    - apply is_pb_to_cartesian_1cell.
      exact pb₂.
  Defined.

  Definition cod_cleaving_of_bicats
    : cleaving_of_bicats (cod_disp_bicat B).
  Proof.
    repeat split.
    - exact cod_local_cleaving.
    - exact cod_global_cleaving.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
  Defined.
End CodomainCleaving.

Definition cod_fibration_one_types
  : cleaving_of_bicats (cod_disp_bicat one_types).
Proof.
  use cod_cleaving_of_bicats.
  - exact one_type_2cell_iso.
  - exact has_pb_one_types.
Defined.

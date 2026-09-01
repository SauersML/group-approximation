import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0PathConnected
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI
import Mathlib

/-!
# Zeroth singular homology of path-connected spaces, general coefficients

General-coefficient (`R : CommRing`) version of the augmentation computation
`H₀(X; R) ≅ R` for nonempty path-connected `X`, mirroring the integral
development in `SingularH0.lean` / `SingularH0PathConnected.lean`. The mod-two
instance is the case `R = ZMod 2`, used for `H₁(Sⁿ; F₂) = 0`.

The point-simplex `pointSimplex` and path-simplex `pathSimplex` are
coefficient-independent, so they are reused from `SingularH0.lean`.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision
namespace H0Gen

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The augmentation `ε : C₀(X; R) → R` summing the coefficients. -/
noncomputable def aug (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularChainGroup R X 0 ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug R X).hom (chainGenerator R X 0 σ) = 1 := by
  have h :
      (Limits.Sigma.ι (fun _ : singularSimplices X 0 => ModuleCat.of R R) σ ≫
        Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R)) :
          ModuleCat.of R R ⟶ ModuleCat.of R R) = 𝟙 (ModuleCat.of R R) :=
    Limits.Sigma.ι_desc _ _
  change
    (ModuleCat.Hom.hom
      (Limits.Sigma.ι (fun _ : singularSimplices X 0 => ModuleCat.of R R) σ ≫
        Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R)))) 1 =
      (ModuleCat.Hom.hom (𝟙 (ModuleCat.of R R))) 1
  exact congrArg (fun g : ModuleCat.of R R ⟶ ModuleCat.of R R => g.hom 1) h

theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary R X 0).hom (chainGenerator R X 1 (pathSimplex p))
      = chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a) := by
  have h_faces :
      AlexanderWhitney.faceSimplex X 0 0 (pathSimplex p) = pointSimplex X b ∧
        AlexanderWhitney.faceSimplex X 0 1 (pathSimplex p) = pointSimplex X a := by
    constructor <;> refine singularSimplices_ext ?_
    · ext x
      simp +decide [AlexanderWhitney.faceSimplex, pointSimplex]
      simp +decide [singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
        pathSimplex]
      simp +decide [stdSimplexHomeomorphUnitInterval, stdSimplex.map]
      simp +decide [stdSimplexEquivIcc, SimplexCategory.δ]
      simp +decide [FunOnFinite.linearMap]
      simp +decide [Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite]
      simp +decide [Finsupp.sum_fintype, Finsupp.single_apply]
      simp +decide [Finset.filter_singleton, Finset.card_singleton]
    · ext x
      simp +decide [AlexanderWhitney.faceSimplex, pathSimplex, pointSimplex]
      simp +decide [singularSimplexAsContinuousMap, continuousMapAsSingularSimplex]
      simp +decide [stdSimplexHomeomorphUnitInterval, stdSimplex.map]
      simp +decide [stdSimplexEquivIcc]
      simp +decide [FunOnFinite.linearMap, SimplexCategory.δ]
      simp +decide [Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite]
      simp +decide [Finsupp.sum, Finsupp.single_apply]
      convert p.source using 1
      apply congrArg p
      apply Subtype.ext
      norm_num
      decide
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_two, h_faces.1, h_faces.2]
  norm_num [permSignCoeff]
  rw [sub_eq_add_neg]

theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary R X 0).hom :=
  ⟨chainGenerator R X 1 (pathSimplex p), boundary_pathSimplex p⟩

theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator R X 0 σ - chainGenerator R X 0 τ
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
  have h_eq :
      σ = pointSimplex X
          (singularSimplexAsContinuousMap X 0 σ (stdSimplex.vertex 0)) ∧
        τ = pointSimplex X
          (singularSimplexAsContinuousMap X 0 τ (stdSimplex.vertex 0)) := by
    constructor <;> apply singularSimplices_ext
    · ext x
      simp only [pointSimplex, singularSimplexAsContinuousMap,
        continuousMapAsSingularSimplex, Equiv.apply_symm_apply, ContinuousMap.const_apply]
      rw [delta0_subsingleton x (stdSimplex.vertex 0)]
    · ext x
      simp only [pointSimplex, singularSimplexAsContinuousMap,
        continuousMapAsSingularSimplex, Equiv.apply_symm_apply, ContinuousMap.const_apply]
      rw [delta0_subsingleton x (stdSimplex.vertex 0)]
  rw [h_eq.1, h_eq.2]
  exact chainGenerator_sub_mem_range_of_path (PathConnectedSpace.somePath _ _)

theorem aug_boundary (c : singularChainGroup R X 1) :
    (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
  have h_ind : ∀ c : singularChainGroup R X 1, (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
    intro c
    have h_c : c ∈ Submodule.span R (Set.range (fun τ : singularSimplices X 1 => chainGenerator R X 1 τ)) := by
      convert Submodule.mem_top ( x := c );
      ext; simp [chainGenerator_span_top]
    refine' Submodule.span_induction _ _ _ _ h_c <;> simp_all +decide [ Submodule.mem_span ];
    intro τ; rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two ] ;
    rw [ aug_generator, aug_generator, add_neg_cancel ];
  exact h_ind c

theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup R X 0) :
    c - (aug R X).hom c • chainGenerator R X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
  have h_span : c ∈ Submodule.span R (Set.range (chainGenerator R X 0)) := by
    rw [chainGenerator_span_top]; exact Submodule.mem_top
  induction h_span using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      rw [aug_generator, one_smul]
      exact chainGenerator_sub_mem_range (R := R) σ (pointSimplex X b)
  | zero => simp
  | add x y _ _ ihx ihy =>
      have h :
          x + y - (aug R X).hom (x + y) • chainGenerator R X 0 (pointSimplex X b) =
            (x - (aug R X).hom x • chainGenerator R X 0 (pointSimplex X b)) +
              (y - (aug R X).hom y • chainGenerator R X 0 (pointSimplex X b)) := by
        rw [map_add, add_smul]
        abel
      rw [h]
      exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih =>
      have h :
          r • x - (aug R X).hom (r • x) • chainGenerator R X 0 (pointSimplex X b) =
            r • (x - (aug R X).hom x • chainGenerator R X 0 (pointSimplex X b)) := by
        rw [map_smul, smul_eq_mul, smul_sub, smul_smul]
      rw [h]
      exact Submodule.smul_mem _ r ih

theorem prev_zero : (ComplexShape.down ℕ).prev 0 = 1 := by simp [ComplexShape.prev]

theorem aug_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex R Y).d 1 0 ≫ aug R Y = 0 := by
  change singularBoundary R Y 0 ≫ aug R Y = 0
  ext c
  exact aug_boundary c

/-- The augmentation descended to degree-0 homology `H₀(Y; R) → R`. -/
def H0aug (R : Type) [CommRing R] (Y : TopCat.{0}) :
    (singularChainComplex R Y).homology 0 ⟶ ModuleCat.of R R :=
  (singularChainComplex R Y).homologyι 0 ≫
    (singularChainComplex R Y).descOpcycles (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)

theorem H0aug_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f) 0
        ≫ H0aug R Z
      = H0aug R Y := by
  have h_comm :
      ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map f).f 0) ≫ aug R Z = aug R Y := by
    apply CategoryTheory.Limits.colimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (aug R Z).hom ((singularChainMap R f 0).hom
      (chainGenerator R Y 0 j.as)) = (aug R Y).hom (chainGenerator R Y 0 j.as)
    rw [singularChainMap_generator, aug_generator, aug_generator]
  unfold H0aug
  rw [HomologicalComplex.homologyι_naturality_assoc]
  rw [HomologicalComplex.opcyclesMap_comp_descOpcycles]
  simp only [h_comm]

instance isIso_homologyι_zero (Y : TopCat.{0}) :
    IsIso ((singularChainComplex R Y).homologyι 0) :=
  HomologicalComplex.isIso_homologyι (singularChainComplex R Y) 0 ((ComplexShape.down ℕ).next 0)
    rfl ((singularChainComplex R Y).shape _ _ (by simp [ComplexShape.next]))

theorem isIso_descOpcycles_aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso ((singularChainComplex R Y).descOpcycles (aug R Y) 1 prev_zero
      (aug_comp_boundary_eq_zero Y)) := by
  have h_bijective : Function.Bijective (HomologicalComplex.descOpcycles (singularChainComplex R Y) (aug R Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)).hom := by
    constructor;
    · intro x y hxy
      obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ( singularChainComplex R Y |>.pOpcycles 0 )).mp ( by infer_instance ) x
      obtain ⟨d, hd⟩ := (ModuleCat.epi_iff_surjective ( singularChainComplex R Y |>.pOpcycles 0 )).mp ( by infer_instance ) y
      have haug : (aug R Y).hom c = (aug R Y).hom d := by
        have hp := HomologicalComplex.p_descOpcycles (singularChainComplex R Y) (aug R Y)
          1 prev_zero (aug_comp_boundary_eq_zero Y)
        have hc' :
            (HomologicalComplex.descOpcycles (singularChainComplex R Y) (aug R Y)
              1 prev_zero (aug_comp_boundary_eq_zero Y)).hom
                ((singularChainComplex R Y).pOpcycles 0 c) = (aug R Y).hom c :=
          congrArg (fun g => g.hom c) hp
        have hd' :
            (HomologicalComplex.descOpcycles (singularChainComplex R Y) (aug R Y)
              1 prev_zero (aug_comp_boundary_eq_zero Y)).hom
                ((singularChainComplex R Y).pOpcycles 0 d) = (aug R Y).hom d :=
          congrArg (fun g => g.hom d) hp
        rw [hc] at hc'
        rw [hd] at hd'
        exact hc'.symm.trans (hxy.trans hd')
      have h_diff : c - d ∈ LinearMap.range (singularBoundary R Y 0).hom := by
        convert sub_aug_smul_basept_mem_range (R := R) (Classical.arbitrary Y) (c - d)
          using 1
        simp [haug]
      have h_zero : (singularChainComplex R Y |>.pOpcycles 0) c = (singularChainComplex R Y |>.pOpcycles 0) d := by
        obtain ⟨e, he⟩ := h_diff
        have h_zero : (singularChainComplex R Y |>.pOpcycles 0) (c - d) = 0 := by
          rw [← he]
          simp [← CategoryTheory.comp_apply, singularBoundary]
        rw [map_sub] at h_zero
        exact eq_of_sub_eq_zero h_zero
      exact hc.symm.trans (h_zero.trans hd)
    · intro r
      use (singularChainComplex R Y).pOpcycles 0 (r • chainGenerator R Y 0 (pointSimplex Y (Classical.arbitrary Y)));
      have hp := HomologicalComplex.p_descOpcycles (singularChainComplex R Y) (aug R Y)
        1 prev_zero (aug_comp_boundary_eq_zero Y)
      calc
        _ = (aug R Y).hom
            (r • chainGenerator R Y 0 (pointSimplex Y (Classical.arbitrary Y))) :=
          congrArg (fun g => g.hom
            (r • chainGenerator R Y 0 (pointSimplex Y (Classical.arbitrary Y)))) hp
        _ = r := by rw [map_smul, aug_generator, smul_eq_mul, mul_one]
  convert ( ConcreteCategory.isIso_iff_bijective _ ).mpr h_bijective

/-- **The augmentation is an isomorphism on `H₀` of a nonempty path-connected
space.** -/
instance isIso_H0aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso (H0aug R Y) := by
  have := isIso_descOpcycles_aug (R := R) Y
  unfold H0aug
  infer_instance

/-- The subspace augmentation on `H₀` of a subordinate-chain complex. -/
def subH0aug (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) :
    (subChainComplex R X S).homology 0 ⟶ ModuleCat.of R R :=
  (subspaceHomologyIso S 0).hom ≫ H0aug R (TopCat.of S)

instance isIso_subH0aug (X : TopCat.{0}) (S : Set X) [Nonempty S] [PathConnectedSpace S] :
    IsIso (subH0aug R X S) := by
  unfold subH0aug
  infer_instance

theorem subChainCorestrict_inclusion_square (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict R X S ≫ subChainInclusion S T h
      = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
          (setInclusionTopCat X S T h) ≫ subChainCorestrict R X T := by
  ext n c
  apply Subtype.ext
  change (singularChainMap R (sInclusion S) n).hom c =
    ((singularChainMap R (setInclusionTopCat X S T h) n ≫
      singularChainMap R (sInclusion T) n).hom c)
  rw [← singularChainMap_comp]
  rfl

theorem subH0aug_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0aug R X T
      = subH0aug R X S := by
  have h_chain :
      subChainInclusion S T h ≫ inv (subChainCorestrict R X T) =
        inv (subChainCorestrict R X S) ≫
          ((singularChainComplexFunctor (ModuleCat.{0} R)).obj
            (ModuleCat.of R R)).map (setInclusionTopCat X S T h) := by
    rw [← CategoryTheory.cancel_epi (subChainCorestrict R X S),
      ← CategoryTheory.cancel_mono (subChainCorestrict R X T)]
    simp [CategoryTheory.Category.assoc, subChainCorestrict_inclusion_square]
  change
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫
          HomologicalComplex.homologyMap (inv (subChainCorestrict R X T)) 0 ≫
        H0aug R (TopCat.of T) =
      HomologicalComplex.homologyMap (inv (subChainCorestrict R X S)) 0 ≫
        H0aug R (TopCat.of S)
  have h_aug := H0aug_natural (R := R) (setInclusionTopCat X S T h)
  rw [← CategoryTheory.Category.assoc, ← HomologicalComplex.homologyMap_comp,
    h_chain, HomologicalComplex.homologyMap_comp, CategoryTheory.Category.assoc,
    h_aug]

end H0Gen
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

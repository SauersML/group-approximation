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
open AffineBarycentricSubdivision

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace H0Gen

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The augmentation `ε : C₀(X; R) → R` summing the coefficients. -/
noncomputable def aug (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularChainGroup R X 0 ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug R X).hom (chainGenerator R X 0 σ) = 1 := by
  unfold aug;
  unfold chainGenerator;
  erw [ ModuleCat.hom_ofHom ];
  convert ( colimit.isColimit ( Discrete.functor fun x : singularSimplices X 0 => ModuleCat.of R R ) ).fac ( Cofan.mk ( ModuleCat.of R R ) fun x => 𝟙 ( ModuleCat.of R R ) ) ( Discrete.mk σ ) using 1;
  constructor <;> intro h <;> simp_all +decide [ CategoryTheory.Limits.colimit.isColimit ];
  · convert CategoryTheory.Limits.colimit.isColimit ( Discrete.functor fun _ : singularSimplices X 0 => ModuleCat.of R R ) |>.fac ( Cofan.mk ( ModuleCat.of R R ) fun _ => 𝟙 ( ModuleCat.of R R ) ) ⟨ σ ⟩ using 1;
  · convert congr_arg ( fun f => f 1 ) h using 1

theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary R X 0).hom (chainGenerator R X 1 (pathSimplex p))
      = chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a) := by
  rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ pathSimplex, pointSimplex ] ;
  -- By definition of `faceSimplex`, we know that `faceSimplex X 0 0 (pathSimplex p) = pointSimplex X b` and `faceSimplex X 0 1 (pathSimplex p) = pointSimplex X a`.
  have h_faces : AlexanderWhitney.faceSimplex X 0 0 (pathSimplex p) = pointSimplex X b ∧ AlexanderWhitney.faceSimplex X 0 1 (pathSimplex p) = pointSimplex X a := by
    constructor <;> refine singularSimplices_ext ?_;
    · ext x; simp +decide [ AlexanderWhitney.faceSimplex, pointSimplex ] ;
      simp +decide [ singularSimplexAsContinuousMap, continuousMapAsSingularSimplex, pathSimplex ];
      simp +decide [ TopCat.toSSetObjEquiv, TopCat.toSSet ];
      simp +decide [ Homeomorph.ulift, ConcreteCategory.homEquiv ];
      simp +decide [ Homeomorph.continuousMapCongr, TopCat.uliftFunctor ];
      simp +decide [ Equiv.ulift, TopCat.ofHom ];
      simp +decide [ stdSimplexHomeomorphUnitInterval, stdSimplex.map ];
      simp +decide [ stdSimplexEquivIcc, SimplexCategory.δ ];
      simp +decide [ FunOnFinite.linearMap ];
      simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite ];
      simp +decide [ Finsupp.sum_fintype, Finsupp.single_apply ];
      simp +decide [ Finset.filter_singleton, Finset.card_singleton ];
    · ext x; simp +decide [ AlexanderWhitney.faceSimplex, pathSimplex, pointSimplex ] ;
      simp +decide [ singularSimplexAsContinuousMap, continuousMapAsSingularSimplex ];
      simp +decide [ TopCat.toSSet, TopCat.toSSetObjEquiv ];
      simp +decide [ Homeomorph.ulift, ConcreteCategory.homEquiv, Equiv.ulift ];
      simp +decide [ Homeomorph.continuousMapCongr, TopCat.uliftFunctor ];
      simp +decide [ stdSimplexHomeomorphUnitInterval, stdSimplex.map ];
      simp +decide [ stdSimplexEquivIcc ];
      simp +decide [ FunOnFinite.linearMap, SimplexCategory.δ ];
      simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite ];
      simp +decide [ Finsupp.sum, Finsupp.single_apply ];
  exact h_faces.1.symm ▸ h_faces.2.symm ▸ by abel1;

theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator R X 0 (pointSimplex X b) - chainGenerator R X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary R X 0).hom :=
  ⟨chainGenerator R X 1 (pathSimplex p), boundary_pathSimplex p⟩

theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator R X 0 σ - chainGenerator R X 0 τ
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
  have h_eq : σ = pointSimplex X (singularSimplexAsContinuousMap X 0 σ (stdSimplex.vertex 0)) ∧ τ = pointSimplex X (singularSimplexAsContinuousMap X 0 τ (stdSimplex.vertex 0)) := by
    constructor <;> apply singularSimplices_ext <;> simp +decide [ pointSimplex ];
    · ext x; exact (by
      convert congr_arg ( singularSimplexAsContinuousMap X 0 σ ) ( delta0_subsingleton x ( stdSimplex.vertex 0 ) ) using 1);
    · ext x;
      convert congr_arg ( singularSimplexAsContinuousMap X 0 τ ) ( delta0_subsingleton x ( stdSimplex.vertex 0 ) ) using 1;
  rw [ h_eq.1, h_eq.2 ];
  exact chainGenerator_sub_mem_range_of_path ( PathConnectedSpace.somePath _ _ )

theorem aug_boundary (c : singularChainGroup R X 1) :
    (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
  have h_ind : ∀ c : singularChainGroup R X 1, (aug R X).hom ((singularBoundary R X 0).hom c) = 0 := by
    intro c
    have h_c : c ∈ Submodule.span R (Set.range (fun τ : singularSimplices X 1 => chainGenerator R X 1 τ)) := by
      convert Submodule.mem_top ( x := c );
      ext; simp [chainGenerator_span_top]
    refine' Submodule.span_induction _ _ _ _ h_c <;> simp_all +decide [ Submodule.mem_span ];
    intro τ; rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two, aug_generator ] ;
    rw [ aug_generator, aug_generator, add_neg_cancel ];
  exact h_ind c

theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup R X 0) :
    c - (aug R X).hom c • chainGenerator R X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary R X 0).hom := by
  have h_span : c ∈ Submodule.span R (Set.range (chainGenerator R X 0)) := by
    rw [chainGenerator_span_top]; exact Submodule.mem_top
  induction' h_span using Submodule.span_induction with c hc c₁ c₂ hc₁ hc₂ c hc ih;
  · obtain ⟨ σ, rfl ⟩ := hc;
    have := chainGenerator_sub_mem_range ( R := R ) σ ( pointSimplex X b );
    convert this using 1 ; simp +decide [ aug_generator ];
    erw [ H0Gen.aug_generator ] ; norm_num;
  · simp +decide [ ModuleCat.Hom.hom ];
  · convert Submodule.add_mem _ c hc using 1 ; simp +decide [ add_smul, sub_add_sub_comm ];
  · rename_i k hk;
    obtain ⟨ y, hy ⟩ := hk; use ih • y; simp +decide [ hy, mul_assoc, mul_left_comm, mul_comm ] ;
    simp +decide [ mul_assoc, mul_left_comm, smul_sub, smul_smul ]

theorem prev_zero : (ComplexShape.down ℕ).prev 0 = 1 := by simp [ComplexShape.prev]

theorem aug_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex R Y).d 1 0 ≫ aug R Y = 0 := by
  ext c;
  convert aug_boundary c using 1

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
  -- By definition of `H0aug`, we know that it is the composition of the augmentation map and the boundary map.
  simp [H0aug];
  unfold singularChainComplex; simp +decide [ aug ] ;
  convert rfl;
  convert CategoryTheory.Limits.colimit.hom_ext _;
  intro j; induction j; simp +decide [ singularChainComplexFunctor ] ;
  ext; simp +decide [ SSet.singularChainComplexFunctor ] ;

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
        convert hxy using 1;
        · convert congr_arg ( fun f => f c ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( aug_comp_boundary_eq_zero Y ) ) using 1;
          · simp +decide [ HomologicalComplex.p_descOpcycles ];
          · rw [ ← hc ];
            convert congr_arg ( fun f => f c ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( by simp +decide [ aug_comp_boundary_eq_zero ] ) ) using 1;
        · rw [ ← hd ];
          convert congr_arg ( fun f => f d ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( by simp +decide [ aug_comp_boundary_eq_zero ] ) ) using 1;
          · grind +suggestions;
          · convert congr_arg ( fun f => f d ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( by simp +decide [ aug_comp_boundary_eq_zero ] ) ) using 1
      have h_diff : c - d ∈ LinearMap.range (singularBoundary R Y 0).hom := by
        have := sub_aug_smul_basept_mem_range ( R := R ) ( Classical.arbitrary Y ) ( c - d ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_zero : (singularChainComplex R Y |>.pOpcycles 0) c = (singularChainComplex R Y |>.pOpcycles 0) d := by
        obtain ⟨ e, he ⟩ := h_diff; simp_all +decide [ sub_eq_iff_eq_add ] ;
        have h_zero : (singularChainComplex R Y |>.pOpcycles 0) (c - d) = 0 := by
          convert congr_arg ( fun x => ( singularChainComplex R Y |>.pOpcycles 0 ) x ) he.symm using 1 ; simp +decide [ ← CategoryTheory.comp_apply, singularBoundary ] ;
        simp_all +decide [ sub_eq_iff_eq_add ]
      simp_all +decide [ Function.Injective ];
    · intro r
      use (singularChainComplex R Y).pOpcycles 0 (r • chainGenerator R Y 0 (pointSimplex Y (Classical.arbitrary Y)));
      convert congr_arg ( fun f => f ( r • chainGenerator R Y 0 ( pointSimplex Y ( Classical.arbitrary Y ) ) ) ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex R Y ) ( aug R Y ) 1 prev_zero ( by simp [ aug_comp_boundary_eq_zero ] ) ) using 1 ; simp +decide [ aug_generator ];
      erw [ H0Gen.aug_generator ] ; aesop;
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
  ext n
  convert Subtype.ext ?_
  convert congr_arg (fun f => f ‹_›)
    (singularChainMap_comp R (setInclusionTopCat X S T h) (sInclusion T) n) using 1

theorem subH0aug_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0aug R X T
      = subH0aug R X S := by
  simp [subH0aug, subspaceHomologyIso];
  rw [ ← CategoryTheory.cancel_epi ( HomologicalComplex.homologyMap ( subChainCorestrict R X S ) 0 ) ];
  rw [ ← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc, ← HomologicalComplex.homologyMap_comp ];
  simp +decide [ ← CategoryTheory.Category.assoc, subChainCorestrict_inclusion_square ];
  simp +decide [ ← HomologicalComplex.homologyMap_comp, H0aug_natural ]

end H0Gen
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

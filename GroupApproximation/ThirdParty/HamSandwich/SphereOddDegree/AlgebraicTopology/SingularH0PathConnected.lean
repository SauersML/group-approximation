import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI
import Mathlib

/-!
# Zeroth homology of path-connected spaces, via the augmentation

We descend the augmentation `ε : C₀(X) → ℤ` to a natural map on degree-0 homology
`H0aug X : H₀(X; ℤ) → ℤ`, and prove it is an isomorphism for nonempty
path-connected spaces.  We also package its subspace variant `subH0aug` and the
naturality needed for the Mayer–Vietoris base-case computation `H₁(S¹) ≅ ℤ`.
-/

open CategoryTheory AlgebraicTopology Limits
open AffineBarycentricSubdivision

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {X : TopCat.{0}}

theorem prev_zero : (ComplexShape.down ℕ).prev 0 = 1 := by
  simp [ComplexShape.prev]

/-
The boundary `∂₁` composed with the augmentation is zero (as a morphism).
-/
theorem aug_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex ℤ Y).d 1 0 ≫ aug Y = 0 := by
  ext c; simp [aug_boundary];
  convert aug_boundary c using 1

/-- The augmentation descended to degree-0 homology `H₀(Y;ℤ) → ℤ`. -/
def H0aug (Y : TopCat.{0}) : (singularChainComplex ℤ Y).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (singularChainComplex ℤ Y).homologyι 0 ≫
    (singularChainComplex ℤ Y).descOpcycles (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)

/-
**Naturality of the augmentation.** For a continuous map `f : Y ⟶ Z`, the
augmentation commutes with the induced map on `H₀`.
-/
theorem H0aug_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (singularHomologyℤ 0).map f ≫ H0aug Z = H0aug Y := by
  unfold H0aug;
  have h_comm : (singularChainℤ.map f).f 0 ≫ aug Z = aug Y := by
    simp +decide [ CategoryTheory.Category.assoc, singularChainℤ, singularChainComplexFunctor, aug ];
    simp +decide [ CategoryTheory.Functor.map, SSet.singularChainComplexFunctor ];
    ext; simp +decide [ CategoryTheory.Functor.map, SSet.singularChainComplexFunctor ] ;
  simp +decide [ ← h_comm, ← CategoryTheory.Category.assoc, HomologicalComplex.homologyι, HomologicalComplex.descOpcycles ];
  simp +decide [ HomologicalComplex.sc, HomologicalComplex.homologyι ];
  erw [ CategoryTheory.ShortComplex.homologyι_naturality_assoc ];
  simp +decide [ HomologicalComplex.shortComplexFunctor, HomologicalComplex.descOpcycles ]

/-- `homologyι` at degree `0` of a chain complex is an isomorphism (no outgoing
differential at the bottom). -/
instance isIso_homologyι_zero (Y : TopCat.{0}) :
    IsIso ((singularChainComplex ℤ Y).homologyι 0) :=
  HomologicalComplex.isIso_homologyι (singularChainComplex ℤ Y) 0 ((ComplexShape.down ℕ).next 0)
    rfl ((singularChainComplex ℤ Y).shape _ _ (by simp [ComplexShape.next]))

/-
The augmentation factored through the opcycles (cokernel of `∂₁`) is an
isomorphism, for a nonempty path-connected space.
-/
theorem isIso_descOpcycles_aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso ((singularChainComplex ℤ Y).descOpcycles (aug Y) 1 prev_zero
      (aug_comp_boundary_eq_zero Y)) := by
  have h_bijective : Function.Bijective (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (by simp [aug_comp_boundary_eq_zero])).hom := by
    constructor;
    · intro x y hxy
      obtain ⟨c, hc⟩ : ∃ c : singularChainGroup ℤ Y 0, (singularChainComplex ℤ Y).pOpcycles 0 c = x := by
        exact ( ModuleCat.epi_iff_surjective _ ).mp ( by infer_instance ) x
      obtain ⟨d, hd⟩ : ∃ d : singularChainGroup ℤ Y 0, (singularChainComplex ℤ Y).pOpcycles 0 d = y := by
        have := ( ModuleCat.epi_iff_surjective ( HomologicalComplex.pOpcycles ( singularChainComplex ℤ Y ) 0 ) );
        exact this.mp ( by infer_instance ) y
      have h_eq : (aug Y).hom c = (aug Y).hom d := by
        have h_eq : (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (by simp [aug_comp_boundary_eq_zero])).hom ((singularChainComplex ℤ Y).pOpcycles 0 c) = (aug Y).hom c ∧ (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (by simp [aug_comp_boundary_eq_zero])).hom ((singularChainComplex ℤ Y).pOpcycles 0 d) = (aug Y).hom d := by
          exact ⟨ by exact congr_arg ( fun f => f c ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℤ Y ) ( aug Y ) 1 prev_zero ( by simp [ aug_comp_boundary_eq_zero ] ) ), by exact congr_arg ( fun f => f d ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℤ Y ) ( aug Y ) 1 prev_zero ( by simp [ aug_comp_boundary_eq_zero ] ) ) ⟩;
        grind +splitIndPred
      have h_diff : c - d ∈ LinearMap.range (singularBoundary ℤ Y 0).hom := by
        convert sub_aug_smul_basept_mem_range ( Classical.arbitrary Y ) ( c - d ) using 1 ; simp +decide [ h_eq ]
      have h_zero : (singularChainComplex ℤ Y).pOpcycles 0 c = (singularChainComplex ℤ Y).pOpcycles 0 d := by
        obtain ⟨ e, he ⟩ := h_diff;
        have h_zero : (singularChainComplex ℤ Y).pOpcycles 0 c - (singularChainComplex ℤ Y).pOpcycles 0 d = 0 := by
          convert congr_arg ( fun x => ( singularChainComplex ℤ Y ).pOpcycles 0 x ) he.symm using 1;
          · grind;
          · simp +decide [ ← CategoryTheory.comp_apply, singularBoundary ];
        exact eq_of_sub_eq_zero h_zero
      simp_all +decide [ Function.Injective ];
    · intro n
      obtain ⟨b⟩ : ∃ b : Y, True := by
        exact ⟨ Classical.arbitrary _, trivial ⟩
      use (singularChainComplex ℤ Y).pOpcycles 0 (n • chainGenerator ℤ Y 0 (pointSimplex Y b));
      have := HomologicalComplex.p_descOpcycles ( singularChainComplex ℤ Y ) ( aug Y ) 1 prev_zero ( by simp +decide [ aug_comp_boundary_eq_zero ] );
      convert congr_arg ( fun f => f ( n • chainGenerator ℤ Y 0 ( pointSimplex Y b ) ) ) this using 1 ; simp +decide [ aug_generator ];
      erw [ aug_generator ] ; aesop;
  convert ( ConcreteCategory.isIso_iff_bijective _ ).mpr h_bijective

/-- **The augmentation is an isomorphism on `H₀` of a nonempty path-connected
space.** -/
instance isIso_H0aug (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso (H0aug Y) := by
  have := isIso_descOpcycles_aug Y
  unfold H0aug
  infer_instance

/-
The augmentation on `H₀` is surjective for any nonempty space.
-/
theorem surjective_H0aug (Y : TopCat.{0}) [Nonempty Y] :
    Function.Surjective (H0aug Y).hom := by
  have h_surjective : Function.Surjective (⇑(ModuleCat.Hom.hom ((singularChainComplex ℤ Y).descOpcycles (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)))) := by
    intro n
    obtain ⟨b⟩ := ‹Nonempty Y›
    use (singularChainComplex ℤ Y).pOpcycles 0 (n • chainGenerator ℤ Y 0 (pointSimplex Y b));
    convert congr_arg ( fun f => f ( n • chainGenerator ℤ Y 0 ( pointSimplex Y b ) ) ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℤ Y ) ( aug Y ) 1 prev_zero ( by simp +decide [ aug_comp_boundary_eq_zero ] ) ) using 1 ; simp +decide [ aug_generator ];
    erw [ aug_generator ] ; aesop;
  convert h_surjective.comp ( show Function.Surjective ⇑ ( ModuleCat.Hom.hom ( ( singularChainComplex ℤ Y ).homologyι 0 ) ) from ?_ ) using 1;
  exact Function.Surjective.of_comp ( show Function.Surjective ⇑ ( ModuleCat.Hom.hom ( ( singularChainComplex ℤ Y ).homologyι 0 ) ) from ( show Function.Surjective ⇑ ( ModuleCat.Hom.hom ( ( singularChainComplex ℤ Y ).homologyι 0 ) ) from by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa using ( ConcreteCategory.isIso_iff_bijective _ ) |>.1 ( by exact inferInstance ) |>.2 ) ) ) ) ) ) ) ) ) ) ) ) ) )

/-! ## The subspace augmentation -/

/-- The augmentation on the degree-0 homology of the subordinate-chain complex of
a subspace `S ⊆ X`, transported via the subspace bridge. -/
def subH0aug (X : TopCat.{0}) (S : Set X) :
    (subChainComplex ℤ X S).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (subspaceHomologyIsoℤ X S 0).hom ≫ H0aug (TopCat.of S)

/-
`subH0aug` is an isomorphism for a nonempty path-connected subspace.
-/
theorem isIso_subH0aug (X : TopCat.{0}) (S : Set X) [Nonempty S] [PathConnectedSpace S] :
    IsIso (subH0aug X S) := by
  -- Apply the fact that the composition of isomorphisms is an isomorphism.
  apply CategoryTheory.IsIso.comp_isIso

/-- The inclusion `S ⊆ T` of subspaces as a morphism of topological spaces. -/
def setInclusionTopCat (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨Set.inclusion h, by fun_prop⟩

/-
**Chain-level naturality square for the corestriction bridge under inclusion.**
The corestriction chain map intertwines the subspace inclusion `S ⊆ T` (at the
space level) with the chain inclusion `subChainInclusion`.
-/
theorem subChainCorestrict_inclusion_square (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict ℤ X S ≫ subChainInclusion S T h
      = singularChainℤ.map (setInclusionTopCat X S T h) ≫ subChainCorestrict ℤ X T := by
  ext n;
  convert Subtype.ext ?_;
  convert congr_arg ( fun f => f ‹_› ) ( singularChainMap_comp ℤ ( setInclusionTopCat X S T h ) ( sInclusion T ) n ) using 1

/-
**Naturality of the subspace augmentation under inclusion `S ⊆ T`.**
-/
theorem subH0aug_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0aug X T
      = subH0aug X S := by
  convert congr_arg _ ( H0aug_natural ( setInclusionTopCat X S T h ) ) using 1;
  unfold subH0aug;
  simp +decide [ subspaceHomologyIsoℤ, singularHomologyℤ ];
  simp +decide [ subspaceHomologyIso, singularHomologyFunctor ];
  simp +decide [ ← CategoryTheory.Category.assoc, ← HomologicalComplex.homologyMap_comp, subChainCorestrict_inclusion_square ];
  rw [ show subChainInclusion S T h ≫ inv ( subChainCorestrict ℤ X T ) = inv ( subChainCorestrict ℤ X S ) ≫ ( ( singularChainComplexFunctor ( ModuleCat ℤ ) ).obj ( ModuleCat.of ℤ ℤ ) ).map ( setInclusionTopCat X S T h ) from ?_ ];
  rw [ ← CategoryTheory.cancel_epi ( subChainCorestrict ℤ X S ), ← CategoryTheory.cancel_mono ( subChainCorestrict ℤ X T ) ];
  simp +decide [ CategoryTheory.Category.assoc, subChainCorestrict_inclusion_square ]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

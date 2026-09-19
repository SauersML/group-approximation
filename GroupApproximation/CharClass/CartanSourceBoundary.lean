import GroupApproximation.CharClass.CartanTargetBoundary
import GroupApproximation.CharClass.CartanDiagonalModule

/-!
# The source's boundary, concretely

`CartanDiagonalModule.lean` builds `W ⊗ S(X)` against an abstract
`SingularBoundaryData`, so that the source complex and its `d ∘ d = 0` could be
proved before the presentation of the singular boundary was settled.  This file
supplies the instance, so `src` stops being parameterized by a hypothesis.

Two presentations of a singular simplex meet here.  `cc-steenrod`'s vocabulary,
and Mathlib's, is `singularSimplices X n`, which by the definition of
`TopCat.toSSet` — a restricted `ULift`ed Yoneda embedding — is `ULift` of the
hom-set `stdSimplexTop n ⟶ X`; the source's index `WSIndex` uses the bare
hom-set, because that is what `FreeOnModels` wants and it makes the freeness
field cost nothing.  The two differ by exactly one `Equiv.ulift`, and this file
is where it is spent: `bdHom` is `bdU` conjugated by it, and both `∂∂ = 0` and
naturality come across along the conjugation.

Nothing else in the lane carries the `ULift`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The two presentations -/

/-- A singular `n`-simplex is the `ULift` of a map out of the standard
topological `n`-simplex. -/
def simplexEquiv (X : TopCat.{0}) (n : ℕ) :
    singularSimplices X n ≃ (stdSimplexTop n ⟶ X) :=
  Equiv.ulift

/-- Under that identification the `i`-th face is precomposition with the
`i`-th coface. -/
theorem simplexEquiv_faceSimplex (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    simplexEquiv X n (faceSimplex X n i σ)
      = SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ simplexEquiv X (n + 1) σ :=
  rfl

/-- Under that identification pushing a simplex forward is postcomposition. -/
theorem simplexEquiv_pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) :
    simplexEquiv Y n (pushSimplex f n σ) = simplexEquiv X n σ ≫ f :=
  rfl

/-! ## 2. Naturality of the boundary -/

variable (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]

omit [Algebra (ZMod 2) Λ] in
theorem bdU_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : singularSimplices X (n + 1) →₀ Λ) :
    bdU Λ Y n (Finsupp.mapDomain (pushSimplex f (n + 1)) c)
      = Finsupp.mapDomain (pushSimplex f n) (bdU Λ X n c) := by
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp
  · intro a b ha hb
    rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb, Finsupp.mapDomain_add]
  · intro σ y
    have hy : Finsupp.single σ y = y • Finsupp.single σ (1 : Λ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hy, Finsupp.mapDomain_smul, map_smul, map_smul, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_single, bdU_single, bdU_single, Finsupp.mapDomain_finsetSum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Finsupp.mapDomain_single]
    exact congrArg (fun τ => Finsupp.single τ (1 : Λ))
      (restrictSimplex_naturality f (SimplexCategory.δ i) σ).symm

/-! ## 3. The boundary on the hom-set model -/

/-- The singular boundary transported to the bare hom-set model. -/
def bdHom (X : TopCat.{0}) (n : ℕ) :
    ((stdSimplexTop (n + 1) ⟶ X) →₀ Λ) →ₗ[Λ] ((stdSimplexTop n ⟶ X) →₀ Λ) :=
  (Finsupp.lmapDomain Λ Λ (simplexEquiv X n)).comp
    ((bdU Λ X n).comp (Finsupp.lmapDomain Λ Λ (simplexEquiv X (n + 1)).symm))

omit [Algebra (ZMod 2) Λ] in
theorem bdHom_apply (X : TopCat.{0}) (n : ℕ)
    (c : (stdSimplexTop (n + 1) ⟶ X) →₀ Λ) :
    bdHom Λ X n c
      = Finsupp.mapDomain (simplexEquiv X n)
          (bdU Λ X n (Finsupp.mapDomain (simplexEquiv X (n + 1)).symm c)) := rfl

theorem bdHom_bdHom (X : TopCat.{0}) (n : ℕ)
    (c : (stdSimplexTop (n + 2) ⟶ X) →₀ Λ) :
    bdHom Λ X n (bdHom Λ X (n + 1) c) = 0 := by
  have hid : ((simplexEquiv X (n + 1)).symm ∘ simplexEquiv X (n + 1))
      = id := funext fun σ => (simplexEquiv X (n + 1)).symm_apply_apply σ
  rw [bdHom_apply, bdHom_apply, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id,
    bdU_bdU, Finsupp.mapDomain_zero]

omit [Algebra (ZMod 2) Λ] in
theorem bdHom_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : (stdSimplexTop (n + 1) ⟶ X) →₀ Λ) :
    bdHom Λ Y n (Finsupp.mapDomain (· ≫ f) c)
      = Finsupp.mapDomain (· ≫ f) (bdHom Λ X n c) := by
  have h1 : ((simplexEquiv Y (n + 1)).symm ∘ fun φ : stdSimplexTop (n + 1) ⟶ X => φ ≫ f)
      = (pushSimplex f (n + 1)) ∘ (simplexEquiv X (n + 1)).symm := rfl
  have h2 : ((fun ψ : stdSimplexTop n ⟶ X => ψ ≫ f) ∘ simplexEquiv X n)
      = (simplexEquiv Y n) ∘ (pushSimplex f n) := rfl
  rw [bdHom_apply, bdHom_apply, ← Finsupp.mapDomain_comp, h1, Finsupp.mapDomain_comp,
    bdU_natural, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, h2]

/-! ## 4. The instance -/

/-- **The singular boundary as `SingularBoundaryData`.**  With this the source
functor `src` is a concrete functor, not one parameterized by a hypothesis. -/
def singularBoundary : SingularBoundaryData where
  bd X n := bdHom GroupRingZ2 X n
  bd_natural f n c := bdHom_natural GroupRingZ2 f n c
  bd_bd X n c := bdHom_bdHom GroupRingZ2 X n c

end

end GroupApproximation.CharClass

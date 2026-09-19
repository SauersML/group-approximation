import GroupApproximation.GGT.DGOProposition414GapTargetSeparation
import GroupApproximation.GGT.DGOProposition414Uniform
import GroupApproximation.GGT.DGOProposition414UniformBridge

/-!
# DGO Proposition 4.14 for additive quasi-geodesic constants

The balanced split now supplies its component families and all target
separation assertions without residual certificate hypotheses. The existing
subdivision argument therefore gives a linear isolated-component sum bound,
uniform in the number of sides, for `(1,b)` quasi-geodesic polygons.

The multiplicative parameter greater than one still needs a geometric
argument. The impossible arithmetic comparison in `UniformGeneral` is not
used here.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A uniform linear bound for isolated components in `(1,b)` polygons of
arbitrary side count, with every balanced-split certificate proved. -/
theorem linearSumBound
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ) (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply uniformSumBound_of_componentFamilies D hsymm b hδ
  intro n k R P B
  obtain ⟨hfirst, hsecond⟩ := B.exists_gapComponentFamilies
  exact ⟨hfirst, hsecond, B.firstGapTargetSeparation, B.secondGapTargetSeparation⟩

/-- A positive uniform DGO radius constant at multiplicative constant one. -/
theorem exists_uniformSumBound_one
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ) (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 (b : ℝ) C :=
  exists_dgoUniformSumBound_of_linearSumBound D b (linearSumBound D hsymm b hδ)

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.linearSumBound
#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniformSumBound_one

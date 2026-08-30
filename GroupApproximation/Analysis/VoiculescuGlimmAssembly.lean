import GroupApproximation.Analysis.VoiculescuGlimmEssentialValue
import GroupApproximation.Analysis.VoiculescuGlimmSelfAdjoint
import GroupApproximation.Analysis.LanceHermitianFunctional

/-!
# (V2) Glimm's lemma, assembled

`VoiculescuGlimmEssentialValue` proves the self-adjoint finite-family form: the
real parts of a state annihilating the compacts are approximated by one vector
state outside a prescribed finite-dimensional subspace.  This module closes the
two remaining seams.

First, a self-adjoint quadratic form and a positive functional evaluated on a
self-adjoint operator are both real, so the real estimate is exactly the complex
norm estimate the printed statement asks for.  Second, every element of the
requested finite set splits into its two self-adjoint Cartesian parts, and the
family of all parts is fed to the range theorem at once, so a single vector
serves every element of the set.

The resulting `glimmLemma` inhabits `GlimmLemmaStatement`.  Thus (V2) is no
longer a named premise for the block-recursion and absorption modules.

## The index type is a sum, not a `Fin`

`exists_unit_vector_of_state` is stated over `Fin n`, because the separation it
rests on is.  Enumerating the parts as a function on `Fin (2 * F.card)` — or on
`Fin (card (F × Fin 2))` — forces every use of an entry to reduce a `Fin.cases`
at a NUMERAL, and the reduction lemmas for `Fin.cases` are stated at `Fin.succ`,
not at `1`.  Indexing by `↥F ⊕ ↥F` instead makes every entry reduce by `Sum.elim`
on a constructor, which is definitional.  The one transport through
`Fintype.equivFin` is isolated in `exists_unit_vector_of_state_fintype`, where the
round trip is a single `Equiv.symm_apply_apply`.

## Why the reality of `ρ` is imported rather than proved

`StateExtension.real_on_selfAdjoint_of_nonneg` already has it, through Mathlib's
`IsSelfAdjoint.le_algebraMap_norm_self`, and it needs no unitality — it gets
`Φ 1` from `hpos 1`.  It applies at `A := H →L[ℂ] H` because all three instances
it wants are registered there with exactly these binders: `CStarAlgebra`
(`Analysis/CStarAlgebra/ContinuousLinearMap.lean`), the Loewner
`PartialOrder` (`InnerProductSpace/Positive.lean`), and `StarOrderedRing`
(`InnerProductSpace/StarOrder.lean`).  The Loewner order is the only
`PartialOrder` registered on `E →L[𝕜] E`, so it is the same order the positivity
hypothesis speaks about; there is no diamond to avoid.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a self-adjoint operator, the real estimate the essential numerical range
delivers is exactly the complex norm estimate Glimm's lemma asks for.  Both sides
of the difference are real: the quadratic form because `T` is self-adjoint, and
`ρ T` because `ρ` is positive. -/
theorem norm_inner_sub_apply_eq_abs_re_of_selfAdjoint
    (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    ‖⟪x, T x⟫_ℂ - ρ T‖ = |(⟪T x, x⟫_ℂ).re - (ρ T).re| := by
  have hsymm : ⟪T x, x⟫_ℂ = ⟪x, T x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
  have hconj : (starRingEnd ℂ) ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
    rw [inner_conj_symm]
    exact hsymm.symm
  have him : (⟪T x, x⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hinner : ⟪x, T x⟫_ℂ = (((⟪T x, x⟫_ℂ).re : ℝ) : ℂ) := by
    rw [← hsymm]
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact him
  obtain ⟨r, hr⟩ := StateExtension.real_on_selfAdjoint_of_nonneg ρ hpos hT
  have hρ : ρ T = (((ρ T).re : ℝ) : ℂ) := by
    rw [hr, Complex.ofReal_re]
  have key : ⟪x, T x⟫_ℂ - ρ T
      = (((⟪T x, x⟫_ℂ).re - (ρ T).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, ← hinner, ← hρ]
  rw [key, Complex.norm_real, Real.norm_eq_abs]

/-- The essential-numerical-range estimate over an arbitrary finite index type.
The transport through `Fintype.equivFin` is confined here so that the assembly
never has to compute with `Fin` arithmetic. -/
theorem exists_unit_vector_of_state_fintype {ι : Type} [Fintype ι]
    (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1) (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    (b : ι → (H →L[ℂ] H)) (hsa : ∀ i, IsSelfAdjoint (b i))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧
      ∀ i, |(⟪b i ξ, ξ⟫_ℂ).re - (ρ (b i)).re| < ε := by
  obtain ⟨ξ, hξV, hξnorm, hξ⟩ :=
    exists_unit_vector_of_state ρ hpos hone hK
      (fun j ↦ b ((Fintype.equivFin ι).symm j)) (fun j ↦ hsa _) V hε
  refine ⟨ξ, hξV, hξnorm, fun i ↦ ?_⟩
  have hi := hξ ((Fintype.equivFin ι) i)
  rwa [Equiv.symm_apply_apply] at hi

/-- Self-adjointness passes from a `⋆`-subalgebra to the ambient algebra along
the coercion, which is a `⋆`-map. -/
theorem coe_isSelfAdjoint_of_isSelfAdjoint {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {y : ↥A} (hy : IsSelfAdjoint y) : IsSelfAdjoint ((y : H →L[ℂ] H)) := by
  show star ((y : H →L[ℂ] H)) = (y : H →L[ℂ] H)
  rw [← StarMemClass.coe_star, hy.star_eq]

/-- **Glimm's lemma.**  The complete (V2) statement, assembled from the essential
numerical range theorem and the Cartesian self-adjoint reduction. -/
theorem glimmLemma : GlimmLemmaStatement := by
  classical
  intro H _ _ _ A hA hAK φ hone F ε hε V hV
  letI : FiniteDimensional ℂ V := hV
  obtain ⟨ρ, hρA, hρK, hρpos, hρone⟩ :=
    exists_state_of_positiveLinearMap hA hAK φ hone
  choose p q hp hq hdec using fun a : ↥A ↦ exists_selfAdjoint_decomposition a
  obtain ⟨ξ, hξV, hξnorm, hξ⟩ :=
    exists_unit_vector_of_state_fintype ρ hρpos hρone hρK
      (Sum.elim (fun y : {z : ↥A // z ∈ F} ↦ ((p y.1 : ↥A) : H →L[ℂ] H))
        (fun y : {z : ↥A // z ∈ F} ↦ ((q y.1 : ↥A) : H →L[ℂ] H)))
      (by
        rintro (y | y)
        · exact coe_isSelfAdjoint_of_isSelfAdjoint (hp y.1)
        · exact coe_isSelfAdjoint_of_isSelfAdjoint (hq y.1))
      V (half_pos hε)
  refine ⟨ξ, hξnorm, hξV, ?_⟩
  intro x hx
  have hpNorm :
      ‖⟪ξ, ((p x : ↥A) : H →L[ℂ] H) ξ⟫_ℂ - φ (p x)‖ < ε / 2 := by
    rw [← hρA (p x), norm_inner_sub_apply_eq_abs_re_of_selfAdjoint ρ hρpos _
      (coe_isSelfAdjoint_of_isSelfAdjoint (hp x))]
    exact hξ (Sum.inl ⟨x, hx⟩)
  have hqNorm :
      ‖⟪ξ, ((q x : ↥A) : H →L[ℂ] H) ξ⟫_ℂ - φ (q x)‖ < ε / 2 := by
    rw [← hρA (q x), norm_inner_sub_apply_eq_abs_re_of_selfAdjoint ρ hρpos _
      (coe_isSelfAdjoint_of_isSelfAdjoint (hq x))]
    exact hξ (Sum.inr ⟨x, hx⟩)
  exact norm_sub_lt_of_selfAdjoint_parts φ ξ (hdec x) hpNorm hqNorm

end

end ShulmanFill
end GroupApproximation

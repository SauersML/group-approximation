import GroupApproximation.Analysis.VoiculescuSqrtModulus
import GroupApproximation.Analysis.CalkinCStarAlgebra
import GroupApproximation.Analysis.CStarIdealApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Square roots stay compact, and so does `1 - √(1-e)`

Two facts owed by the partition-of-unity route, both about the compacts being a
closed two-sided `⋆`-ideal.

**`dⱼ` is compact.**  `isCompactOperator_sqrt` is `cfcₙ_mem` at the compact
ideal: the non-unital continuous calculus of an element of a closed non-unital
`⋆`-subalgebra stays inside it, and `CStarTensor.idealStarSub` puts the compacts
in that shape.  `CFC.sqrt_eq_real_sqrt` is what makes the lemma applicable —
`CFC.sqrt` is `cfcₙ NNReal.sqrt`, and `cfcₙ_mem` wants `RCLike` scalars, which
`ℝ≥0` is not.

**`1 - √(1-e)` is compact**, which is what makes `[√(1-e), S]` compact and is the
real point.  This one needs no functional calculus at all.  Writing
`g = √(1-e)`, the identity `(1 - g)(1 + g) = 1 - g² = e` holds by construction,
and `1 + g` is invertible because `g` is positive.  So `1 - g = e (1+g)⁻¹` is a
compact operator times a bounded one, and the ideal does the rest.  The
functional-calculus route would have to identify `1 - √(1-e)` with `cfcₙ` of a
function of `e`; the factorisation avoids that entirely.

## Why the second fact is the load-bearing one

The recursion that builds the monotone quasicentral unit sets
`e_{j+1} = e_j + g (u - g² + ...)`, and by
`VoiculescuMonotoneStep.one_sub_improveUnit`, `1 - e_{j+1} = g (1 - u) g` exactly,
so `[e_{j+1}, S] = -[g (1-u) g, S]`, which expands as

    `g (1-u) [g, S] + g [u, S] g + [g, S] (1-u) g` .

The middle term is small because `u` is quasicentral.  The outer two are small
because `[g, S]` is **compact** and `u` absorbs compacts — not because `[g, S]`
is itself small.  That distinction is what decouples the stages: without it the
tolerance at stage `j+1` would be constrained by the tolerance already spent at
stage `j`, and the schedule would have to be solved backwards.  With it, each
stage may aim at any tolerance it likes.
-/

namespace GroupApproximation
namespace ShulmanFill

open CalkinAlgebra CStarTensor

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The square root of a positive compact operator is compact.**  The
non-unital continuous calculus does not leave the closed ideal it starts in. -/
theorem isCompactOperator_sqrt {e : H →L[ℂ] H} (h0 : 0 ≤ e)
    (hK : IsCompactOperator e) : IsCompactOperator ((CFC.sqrt e : H →L[ℂ] H)) := by
  haveI : IsClosed ((compactIdeal H : Set (H →L[ℂ] H))) := isClosed_compactIdeal H
  have hmem : e ∈ idealStarSub (compactIdeal H) := hK
  have h : CFC.sqrt e ∈ idealStarSub (compactIdeal H) := by
    rw [CFC.sqrt_eq_real_sqrt e h0]
    exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt hmem
  exact h

/-- **`1 - √(1-e)` is compact.**  Not by functional calculus: `(1-g)(1+g) = e`
and `1 + g` is invertible, so `1 - g` is `e` times a bounded operator. -/
theorem mem_compactIdeal_one_sub_sqrt_one_sub {e : H →L[ℂ] H}
    (h1 : e ≤ 1) (hK : IsCompactOperator e) :
    (1 : H →L[ℂ] H) - CFC.sqrt (1 - e) ∈ compactIdeal H := by
  have hge : (0 : H →L[ℂ] H) ≤ CFC.sqrt (1 - e) := CFC.sqrt_nonneg _
  have hsq : CFC.sqrt (1 - e) * CFC.sqrt (1 - e) = 1 - e :=
    CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr h1)
  obtain ⟨v, hv⟩ : IsUnit ((1 : H →L[ℂ] H) + CFC.sqrt (1 - e)) :=
    (isStrictlyPositive_one.add_nonneg hge).isUnit
  have hfac : ((1 : H →L[ℂ] H) - CFC.sqrt (1 - e)) * (1 + CFC.sqrt (1 - e)) = e := by
    rw [mul_add, sub_mul, sub_mul, one_mul, mul_one, one_mul, hsq]
    abel
  set X : H →L[ℂ] H := (1 : H →L[ℂ] H) - CFC.sqrt (1 - e) with hX
  have h2 : X * ((v : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = e := by
    rw [hv]; exact hfac
  have heq : X = e * ((v⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := by
    rw [← h2, mul_assoc, Units.mul_inv, mul_one]
  rw [heq]
  exact Ideal.mul_mem_right _ _ hK

/-- The same fact in operator form. -/
theorem isCompactOperator_one_sub_sqrt_one_sub {e : H →L[ℂ] H}
    (h1 : e ≤ 1) (hK : IsCompactOperator e) :
    IsCompactOperator (((1 : H →L[ℂ] H) - CFC.sqrt (1 - e) : H →L[ℂ] H)) :=
  mem_compactIdeal_one_sub_sqrt_one_sub h1 hK

/-- **The commutator of `√(1-e)` with any bounded operator is compact.**  This
is the form the stage estimate consumes. -/
theorem isCompactOperator_commutator_sqrt_one_sub {e : H →L[ℂ] H}
    (h1 : e ≤ 1) (hK : IsCompactOperator e) (S : H →L[ℂ] H) :
    IsCompactOperator
      ((CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e) : H →L[ℂ] H)) := by
  have hk : (1 : H →L[ℂ] H) - CFC.sqrt (1 - e) ∈ compactIdeal H :=
    mem_compactIdeal_one_sub_sqrt_one_sub h1 hK
  have hcomm : CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e)
      = S * ((1 : H →L[ℂ] H) - CFC.sqrt (1 - e))
        - ((1 : H →L[ℂ] H) - CFC.sqrt (1 - e)) * S := by
    rw [mul_sub, sub_mul, one_mul, mul_one]
    abel
  have hmem : CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e) ∈ compactIdeal H := by
    rw [hcomm]
    exact Submodule.sub_mem _ (Ideal.mul_mem_left _ S hk) (Ideal.mul_mem_right S _ hk)
  exact hmem

end

end ShulmanFill
end GroupApproximation

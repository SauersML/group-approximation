import GroupApproximation.Analysis.VoiculescuGlimmStatement
import GroupApproximation.Analysis.CStarExactnessSliceReduction
import GroupApproximation.Analysis.CalkinCStarAlgebra

/-!
# (V2) Positivity reflects through the essential map

The assembly Glimm's lemma runs on — a state of `A` becoming a state of `B(H)`
that annihilates `K(H)` — passes through the Calkin algebra, and the step that
needs an argument is positivity: the transported functional must be positive
against `Q(H)`'s positives, which asks that a positive element of the image come
from a positive element of `A`.

`Analysis/VoiculescuGlimmStatement.nonneg_of_negPart_isCompactOperator` does
that in the form that mentions no order on the quotient: a self-adjoint element
of `A` whose negative part is compact is positive.  What is added here is the
bridge from the quotient to that hypothesis, namely that the negative part
commutes with the quotient map.

## Why the naturality is stated, not inlined

`NonUnitalStarAlgHomClass.map_cfcₙ` is the general fact, and it carries five
autoparameters — the continuity of the function on the quasispectrum, its
vanishing at zero, the continuity of the homomorphism, and the calculus
predicate at both ends.  Of those, the homomorphism's continuity cannot be
discharged by `fun_prop`, so a caller must supply the whole prefix by hand.
Doing that once, behind a statement a reader can check at a glance —
`π (a⁻) = (π a)⁻` — is worth a name; doing it inline, in the middle of a
positivity argument, would bury the content under its own bookkeeping.

The naturality is stated for the Calkin quotient specifically rather than for a
general `⋆`-homomorphism: the general form is `map_cfcₙ`'s job, and a second
general wrapper would be a near-duplicate under a different vocabulary.

Both the quotient map as a `⋆`-homomorphism and its continuity were already in
the tree, in `Analysis/CStarQuotientHom` and
`Analysis/CStarExactnessSliceReduction`, written for the tensor lane;
`CalkinCStarAlgebra.essential` is only a `RingHom`, which does not carry the
involution the calculus needs.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact IsStarNormal.instContinuousFunctionalCalculus (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact ContinuousFunctionalCalculus.toNonUnital (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℝ (CalkinAlgebra.CalkinQuotient H)
      IsSelfAdjoint := by
  exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := CalkinAlgebra.CalkinQuotient H)

/-- **The negative part commutes with the essential map.**  One application of
`map_cfcₙ`, with its argument prefix discharged here so that no consumer has to
carry it. -/
theorem essential_negPart (a : H →L[ℂ] H) (hsa : IsSelfAdjoint a) :
    CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) (a⁻)
      = (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) a)⁻ := by
  have hsa' : IsSelfAdjoint
      (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) a) := by
    show star (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) a)
      = CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) a
    rw [← map_star, hsa.star_eq]
  rw [CFC.negPart_def, CFC.negPart_def]
  exact NonUnitalStarAlgHomClass.map_cfcₙ
    (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)) (·⁻ : ℝ → ℝ) a
    continuous_negPart.continuousOn (by simp)
    (CStarTensor.continuous_quotientStarMk _) hsa hsa'

/-- **Positivity reflects.**  A self-adjoint element of `A` whose image in the
Calkin algebra has vanishing negative part is positive.

The hypothesis is stated through the negative part rather than as `0 ≤ π a`
because `Q(H)` is a general C\*-algebra and carries no registered order: at the
point where the assembly has the spectral order in scope,
`CFC.negPart_eq_zero_iff` converts the one into the other, and everything
before that point stays order-free. -/
theorem nonneg_of_essential_negPart_eq_zero
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0)
    {a : H →L[ℂ] H} (haA : a ∈ A) (hsa : IsSelfAdjoint a)
    (hzero : (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) a)⁻ = 0) :
    0 ≤ a := by
  refine nonneg_of_negPart_isCompactOperator hA hAK haA hsa ?_
  have h : CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) (a⁻) = 0 := by
    rw [essential_negPart a hsa, hzero]
  rw [CStarTensor.quotientStarMk_apply] at h
  exact (CalkinAlgebra.mem_compactIdeal H).mp (Ideal.Quotient.eq_zero_iff_mem.mp h)

end

end ShulmanFill
end GroupApproximation

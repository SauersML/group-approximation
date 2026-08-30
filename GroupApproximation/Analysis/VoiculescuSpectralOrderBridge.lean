import GroupApproximation.Analysis.VoiculescuMonotoneStep

/-!
# The spectral order is the registered order

`CStarAlgebra.spectralOrder` is deliberately not an instance — Mathlib's own
comment says "one may already have a partial order with better definitional
properties", and `B(H)` is exactly such an algebra, carrying the Loewner order.
That is a genuine obstacle to reusing any lemma stated over the spectral order at
an algebra with its own: the two `le` fields are

    spectral :  `IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) …`
    Loewner  :  `(y - x).IsPositive`

which are propositionally but not definitionally equal.

This module removes the obstacle once, for every algebra at once: whenever a
C⋆-algebra already carries a `PartialOrder` making it a `StarOrderedRing` with
nonnegative spectra, that order **equals** the spectral order, as instances.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **The spectral order is the registered order.**  On a C⋆-algebra whose
registered `PartialOrder` makes it a `StarOrderedRing` with nonnegative spectra,
`CStarAlgebra.spectralOrder` is that same instance. -/
theorem spectralOrder_eq (A : Type*) [CStarAlgebra A] [inst : PartialOrder A]
    [StarOrderedRing A] [NonnegSpectrumClass ℝ A] :
    CStarAlgebra.spectralOrder A = inst := by
  refine PartialOrder.ext fun x y ↦ ?_
  have hkey : ∀ a : A, (IsSelfAdjoint a ∧ 0 ≤ a) ↔ 0 ≤ a := by
    intro a
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨IsSelfAdjoint.of_nonneg h, h⟩⟩
  constructor
  · rintro ⟨hsa, hq⟩
    rw [← sub_nonneg]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa]
    have hq' : SpectrumRestricts (y - x) ContinuousMap.realToNNReal := hq
    rw [← SpectrumRestricts.nnreal_iff]
    exact hq' 
  · intro h
    rw [← sub_nonneg] at h
    have hsa : IsSelfAdjoint (y - x) := IsSelfAdjoint.of_nonneg h
    refine ⟨hsa, ?_⟩
    show SpectrumRestricts (y - x) ContinuousMap.realToNNReal
    rw [SpectrumRestricts.nnreal_iff]
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa).mp h

end

end ShulmanFill
end GroupApproximation

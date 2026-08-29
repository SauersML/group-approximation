import GroupApproximation.Analysis.ShulmanFillNormingTailShift

/-!
# Relabelling stays in `𝒟` and keeps the limit

`Analysis/ShulmanFillNormingTailShift` relabels a bounded sequence past a cut.
For that to be usable the relabelled sequence has to lie in the `𝒟` of the
relabelled data, and its `*`-strong limit has to be the one it started with;
otherwise the glued representation would represent something else.

Both are one observation: the `ι`-images of the relabelled sequence are the
`ι`-images of the original read along `m ↦ m + c`, and `tendsto_add_atTop_nat`
says that reading a convergent sequence along that map does not disturb it.
Neither clause of `IsStarStrongLimit` needs anything else, so the limit is
literally the same operator rather than merely an equal one.

This is `Analysis/ShulmanFillNormingTailCorner`'s `starStrongLimit_truncSeq` in
the relabelling vocabulary, and it is what keeps the faithfulness half of the
gluing intact: `q̂ ∘ Θᵢ` stays the constant embedding of `ρᵢ`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section ShiftLimit

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- **Relabelling keeps the `*`-strong limit.**  The relabelled `ι`-images are
the original ones read along `m ↦ m + c`, and both clauses of
`IsStarStrongLimit` survive that reading. -/
theorem shiftSeq_isStarStrongLimit (c : ℕ)
    {x : StarStrong.BoundedStarSequence A} {S : H →L[ℂ] H}
    (hx : StarStrong.IsStarStrongLimit (fun n ↦ ι n (x n)) S) :
    StarStrong.IsStarStrongLimit
      (fun m ↦ shiftIota ι c m ((shiftSeq (A := A) c x) m)) S :=
  ⟨fun v ↦ (hx.1 v).comp (tendsto_add_atTop_nat c),
    fun v ↦ (hx.2 v).comp (tendsto_add_atTop_nat c)⟩

/-- The relabelled sequence lies in the `𝒟` of the relabelled data. -/
theorem shiftSeq_mem (c : ℕ) {x : StarStrong.BoundedStarSequence A}
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    shiftSeq (A := A) c x ∈ StarStrong.starStrongSubalgebra
      (shiftIota ι c) (shiftIota_norm_le ι hnorm c) (shiftIota_hone ι hone c) :=
  ⟨StarStrong.starStrongLimit ι hnorm hone ⟨x, hx⟩,
    shiftSeq_isStarStrongLimit ι c
      (StarStrong.starStrongLimit_spec ι hnorm hone ⟨x, hx⟩)⟩

/-- **The relabelled limit is the original limit.**  Not merely equal to it:
the same operator, produced by the same convergence. -/
theorem starStrongLimit_shiftSeq (c : ℕ)
    {x : StarStrong.BoundedStarSequence A}
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    StarStrong.starStrongLimit (shiftIota ι c) (shiftIota_norm_le ι hnorm c)
        (shiftIota_hone ι hone c)
        ⟨shiftSeq (A := A) c x, shiftSeq_mem ι hnorm hone c hx⟩
      = StarStrong.starStrongLimit ι hnorm hone ⟨x, hx⟩ :=
  StarStrong.starStrongLimit_eq (shiftIota ι c) (shiftIota_norm_le ι hnorm c)
    (shiftIota_hone ι hone c) _
    (shiftSeq_isStarStrongLimit ι c
      (StarStrong.starStrongLimit_spec ι hnorm hone ⟨x, hx⟩))

end ShiftLimit

end

end ShulmanFill
end GroupApproximation

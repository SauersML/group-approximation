import GroupApproximation.Analysis.VoiculescuIntertwiningStep
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# (V4) The orthogonal-range bookkeeping

The assembly above the intertwining step builds one isometry out of countably
many.  The source space is cut into orthogonal blocks, the intertwining step is
run on each block separately, and the resulting isometries are summed.  This
module is the summing, and only the summing: it says nothing about
representations, defects or tolerances.

## What the summing needs, and what it forces

It needs the blocks to be a Hilbert sum of the source — an orthogonal family
whose closed span is everything — and the isometries out of them to have
pairwise orthogonal ranges.  Both are supplied by Mathlib's
`IsHilbertSum`/`OrthogonalFamily`, and the block isometry is the composition of
the canonical identification of the source with `lp G 2` and the isometry that
family induces.

The orthogonality of the ranges is not merely sufficient, it is *forced*:
`orthogonalFamily_of_blockIsometry` recovers it from the conclusion, since an
isometry preserves inner products and the blocks were orthogonal to begin with.
That is the model test of this module — a hypothesis that the conclusion implies
back is the right hypothesis, and a summing lemma stated with a stronger one
(mutually orthogonal *and* something else) would be visibly wrong here.

## What is deliberately not here

The tolerances, and the compactness of the defect.  The blocks carry no
finite-dimensionality hypothesis at this stage either: the summing does not use
it, and only the compactness argument above will.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {K H : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {G : ℕ → Type} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]

/-! ## The block isometry -/

/-- **The block sum of isometries with orthogonal ranges.**  If the source is the
Hilbert sum of the blocks and the isometries out of them have pairwise
orthogonal ranges, they are the restrictions of a single isometry. -/
theorem exists_linearIsometry_of_blocks (U : ∀ m, G m →ₗᵢ[ℂ] K)
    (hU : IsHilbertSum ℂ G U) (V : ∀ m, G m →ₗᵢ[ℂ] H)
    (hV : OrthogonalFamily ℂ G V) :
    ∃ W : K →ₗᵢ[ℂ] H, ∀ (m : ℕ) (x : G m), W (U m x) = V m x := by
  classical
  refine ⟨hV.linearIsometry.comp hU.linearIsometryEquiv.toLinearIsometry, ?_⟩
  intro m x
  have hsingle : hU.linearIsometryEquiv (U m x) = lp.single 2 m x := by
    have h := hU.linearIsometryEquiv_symm_apply_single (i := m) x
    rw [← h, LinearIsometryEquiv.apply_symm_apply]
  show hV.linearIsometry (hU.linearIsometryEquiv (U m x)) = V m x
  rw [hsingle, OrthogonalFamily.linearIsometry_apply_single]

/-! ## The model test -/

omit [CompleteSpace K] [CompleteSpace H] in
/-- **The orthogonality of the ranges is forced.**  Any isometry restricting to
the `V m` on the blocks makes them an orthogonal family, because an isometry
preserves inner products and the blocks are orthogonal in the source.  So the
hypothesis of `exists_linearIsometry_of_blocks` is exactly its conclusion's
content, not a convenient strengthening. -/
theorem orthogonalFamily_of_blockIsometry (U : ∀ m, G m →ₗᵢ[ℂ] K)
    (hU : OrthogonalFamily ℂ G U) (V : ∀ m, G m →ₗᵢ[ℂ] H) (W : K →ₗᵢ[ℂ] H)
    (hW : ∀ (m : ℕ) (x : G m), W (U m x) = V m x) :
    OrthogonalFamily ℂ G V := by
  intro m n hmn x y
  rw [← hW m x, ← hW n y, LinearIsometry.inner_map_map]
  exact hU hmn x y

end

end ShulmanFill
end GroupApproximation

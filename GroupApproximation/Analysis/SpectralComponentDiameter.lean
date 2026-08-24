import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Spectral components control norm motion

This file isolates the topology-and-Gelfand-transform core of spectral
compression.  The compression argument produces equality of every clopen
spectral projection.  In a compact Hausdorff space, equality of all clopen
tests puts two points in the same connected component.  Gelfand duality then
turns a uniform diameter bound on those components into an operator-norm
bound.

The statements here do not mention compression, property `(T)`, matrix
coronas, or group representations.  Those enter in the subsequent file that
proves the clopen tests agree.
-/

namespace GroupApproximation
namespace SpectralComponentDiameter

open WeakDual

universe u

/-! ## The compact-Hausdorff topology lemma -/

/-- Two points of a compact Hausdorff space which belong to exactly the same
clopen sets lie in the same connected component. -/
theorem mem_connectedComponent_of_same_clopens
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {x y : X}
    (hclopen : ∀ U : Set X, IsClopen U → (x ∈ U ↔ y ∈ U)) :
    y ∈ connectedComponent x := by
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter]
  intro U
  exact (hclopen U U.2.1).mp U.2.2

/-! ## The commutative C-star-algebra estimate -/

/-- If every character sees `a` and `b` in the same clopen pieces of the
spectrum of `a`, then a uniform bound on the diameters of the connected
components of that spectrum bounds `‖a - b‖`.

The hypothesis `spectrum ℂ b ⊆ spectrum ℂ a` is exactly what unitary
conjugacy supplies in the spectral-compression application. -/
theorem norm_sub_le_of_same_clopen_spectral_pieces
    {A : Type u} [CommCStarAlgebra A] (a b : A) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hspectrum : spectrum ℂ b ⊆ spectrum ℂ a)
    (hclopen : ∀ χ : characterSpace ℂ A,
      ∀ U : Set (spectrum ℂ a), IsClopen U →
        ((⟨χ a, (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩ :
            spectrum ℂ a) ∈ U ↔
          (⟨χ b, hspectrum
            ((CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩)⟩ :
            spectrum ℂ a) ∈ U))
    (hdiam : ∀ z : spectrum ℂ a,
      Metric.diam (connectedComponent z) ≤ δ) :
    ‖a - b‖ ≤ δ := by
  rw [← (gelfandTransform_isometry A).norm_map_of_map_zero
      (map_zero (gelfandTransform ℂ A)) (a - b)]
  apply (ContinuousMap.norm_le ((gelfandTransform ℂ A) (a - b)) hδ).2
  intro χ
  let za : spectrum ℂ a :=
    ⟨χ a, (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩
  let zb : spectrum ℂ a :=
    ⟨χ b, hspectrum
      ((CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩)⟩
  have hcomponent : zb ∈ connectedComponent za :=
    mem_connectedComponent_of_same_clopens (fun U hU ↦ hclopen χ U hU)
  have hdist : dist za zb ≤ Metric.diam (connectedComponent za) :=
    Metric.dist_le_diam_of_mem
      isClosed_connectedComponent.isCompact.isBounded
      mem_connectedComponent hcomponent
  have hpoint : dist za zb ≤ δ := hdist.trans (hdiam za)
  simpa [za, zb, Subtype.dist_eq, Complex.dist_eq, map_sub] using hpoint

/-- Zero-dimensional spectral pieces force equality.  This is the abstract
endpoint used after clopen spectral projections have collapsed. -/
theorem eq_of_same_clopen_spectral_pieces
    {A : Type u} [CommCStarAlgebra A] (a b : A)
    (hspectrum : spectrum ℂ b ⊆ spectrum ℂ a)
    (hclopen : ∀ χ : characterSpace ℂ A,
      ∀ U : Set (spectrum ℂ a), IsClopen U →
        ((⟨χ a, (CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩⟩ :
            spectrum ℂ a) ∈ U ↔
          (⟨χ b, hspectrum
            ((CharacterSpace.mem_spectrum_iff_exists).2 ⟨χ, rfl⟩)⟩ :
            spectrum ℂ a) ∈ U))
    (hzero : ∀ z : spectrum ℂ a, connectedComponent z = {z}) :
    a = b := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm
  · apply norm_sub_le_of_same_clopen_spectral_pieces a b (δ := 0)
      (le_refl 0) hspectrum hclopen
    intro z
    rw [hzero z, Metric.diam_singleton]
  · exact norm_nonneg _

end SpectralComponentDiameter
end GroupApproximation

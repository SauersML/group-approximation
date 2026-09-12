import GroupApproximation.GGT.VanKampen.CombMap

/-!
# Counting the darts of a region of a combinatorial map

The unconditional counts a region argument needs, stated at the level of
`CombMap` so that the estimating surgery and the power-disc argument can use
them as well.  A region is a chosen finite set of faces.  Its darts are the
darts based in those faces; they split into the internal ones, whose reverse is
also based in the region, and the boundary ones, whose reverse leaves it.  The
internal darts are closed under edge reversal, so they are a union of reversal
pairs, while the boundary darts meet each of their edges once.

Nothing here uses planarity, connectivity, or a boundary walk.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

namespace CombMap

universe u

variable (M : CombMap.{u})

/-! ## The darts of a region -/

/-- The darts based in a chosen set of faces. -/
noncomputable def regionDarts (faces : Finset M.Face) : Finset M.Dart := by
  classical
  exact Finset.univ.filter fun d => M.faceOf d ∈ faces

theorem mem_regionDarts_iff (faces : Finset M.Face) (d : M.Dart) :
    d ∈ M.regionDarts faces ↔ M.faceOf d ∈ faces := by
  classical
  simp only [regionDarts, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The darts of the region whose reverse also lies in the region. -/
noncomputable def internalDarts (faces : Finset M.Face) : Finset M.Dart := by
  classical
  exact (M.regionDarts faces).filter fun d => M.faceOf (M.alpha d) ∈ faces

/-- The darts of the region whose reverse leaves it. -/
noncomputable def regionBoundaryDarts (faces : Finset M.Face) :
    Finset M.Dart := by
  classical
  exact (M.regionDarts faces).filter fun d => M.faceOf (M.alpha d) ∉ faces

theorem mem_internalDarts_iff (faces : Finset M.Face) (d : M.Dart) :
    d ∈ M.internalDarts faces ↔
      M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∈ faces := by
  classical
  simp only [internalDarts, Finset.mem_filter, M.mem_regionDarts_iff]

theorem mem_regionBoundaryDarts_iff (faces : Finset M.Face) (d : M.Dart) :
    d ∈ M.regionBoundaryDarts faces ↔
      M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces := by
  classical
  simp only [regionBoundaryDarts, Finset.mem_filter, M.mem_regionDarts_iff]

/-! ## The split -/

/-- Every dart of the region is internal or boundary, never both. -/
theorem card_internalDarts_add_card_regionBoundaryDarts
    (faces : Finset M.Face) :
    (M.internalDarts faces).card + (M.regionBoundaryDarts faces).card =
      (M.regionDarts faces).card := by
  classical
  exact (M.regionDarts faces).card_filter_add_card_filter_not
    fun d => M.faceOf (M.alpha d) ∈ faces

/-! ## Internal darts pair up under edge reversal -/

/-- The internal darts of a region are closed under edge reversal. -/
theorem alpha_mem_internalDarts (faces : Finset M.Face) {d : M.Dart}
    (hd : d ∈ M.internalDarts faces) :
    M.alpha d ∈ M.internalDarts faces := by
  rw [M.mem_internalDarts_iff] at hd ⊢
  refine ⟨hd.2, ?_⟩
  rw [M.alpha_involutive]
  exact hd.1

/-- Edge reversal has no fixed point among the internal darts. -/
theorem alpha_ne_of_mem_internalDarts (faces : Finset M.Face) {d : M.Dart}
    (_hd : d ∈ M.internalDarts faces) : M.alpha d ≠ d :=
  M.alpha_fixedPointFree d

/-- A boundary dart of a region is never internal, and its reverse is never a
dart of the region at all. -/
theorem not_mem_regionDarts_alpha_of_mem_regionBoundaryDarts
    (faces : Finset M.Face) {d : M.Dart}
    (hd : d ∈ M.regionBoundaryDarts faces) :
    M.alpha d ∉ M.regionDarts faces := by
  rw [M.mem_regionBoundaryDarts_iff] at hd
  rw [M.mem_regionDarts_iff]
  exact hd.2

/-! ## Counting the region face by face -/

/-- The darts of a region, counted one face at a time. -/
theorem card_regionDarts_eq_sum (faces : Finset M.Face) :
    (M.regionDarts faces).card = ∑ f ∈ faces, (M.regionDarts {f}).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun d => M.faceOf d) (t := faces)
    (fun d hd => (M.mem_regionDarts_iff faces d).1 hd)]
  refine Finset.sum_congr rfl ?_
  intro f hf
  have hset : (M.regionDarts faces).filter (fun d => M.faceOf d = f)
      = M.regionDarts {f} := by
    ext d
    simp only [Finset.mem_filter, M.mem_regionDarts_iff, Finset.mem_singleton]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact hf
  rw [hset]

end CombMap

end VanKampen
end GGT
end GroupApproximation

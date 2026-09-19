import GroupApproximation.Analysis.STW22AntipodalTraceBoundaryTopology
import GroupApproximation.Analysis.STW22AntipodalBaseBoundaryMeasure

/-!
# Measurable components of the antipodal trace boundary

The finite part of the one-point boundary is the disjoint countable union of
its projective coordinate components.  This file records those component sets
as literal open-and-closed measurable subsets, ready for measure
decomposition.
-/

namespace GroupApproximation
namespace STW22AntipodalBoundaryComponents

open Set
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalTraceBoundaryTopology
open STW22AntipodalBaseBoundaryMeasure
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped OnePoint

/-- The image of the `n`-th projective component in the one-point boundary. -/
def boundaryCoordinateSet (n : Nat) : Set AntipodalTraceBoundary :=
  Set.range (boundaryCoordinateEmbedding n)

theorem boundaryCoordinateSet_eq_image (n : Nat) :
    boundaryCoordinateSet n =
      ((↑) : (Σ k : Nat, RP (antipodalBlockDimension k)) →
        AntipodalTraceBoundary) ''
        Set.range (@Sigma.mk Nat
          (fun k ↦ RP (antipodalBlockDimension k)) n) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨n, x⟩, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem isOpen_boundaryCoordinateSet (n : Nat) :
    IsOpen (boundaryCoordinateSet n) := by
  rw [boundaryCoordinateSet_eq_image]
  exact OnePoint.isOpen_image_coe.mpr isOpen_range_sigmaMk

theorem isCompact_boundaryCoordinateSet (n : Nat) :
    IsCompact (boundaryCoordinateSet n) := by
  exact isCompact_range (continuous_boundaryCoordinateEmbedding n)

theorem isClosed_boundaryCoordinateSet (n : Nat) :
    IsClosed (boundaryCoordinateSet n) :=
  (isCompact_boundaryCoordinateSet n).isClosed

theorem measurableSet_boundaryCoordinateSet (n : Nat) :
    MeasurableSet (boundaryCoordinateSet n) :=
  (isOpen_boundaryCoordinateSet n).measurableSet

theorem boundaryCoordinateSet_disjoint {n m : Nat} (h : n ≠ m) :
    Disjoint (boundaryCoordinateSet n) (boundaryCoordinateSet m) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have heq := hx.trans hy.symm
  have hsigma : (⟨n, x⟩ : Σ k : Nat, RP (antipodalBlockDimension k)) =
      ⟨m, y⟩ := OnePoint.coe_injective heq
  exact h (congrArg Sigma.fst hsigma)

/-- All non-infinity boundary points. -/
def finiteBoundarySet : Set AntipodalTraceBoundary :=
  Set.range ((↑) : (Σ n : Nat, RP (antipodalBlockDimension n)) →
    AntipodalTraceBoundary)

theorem isOpen_finiteBoundarySet : IsOpen finiteBoundarySet := by
  rw [finiteBoundarySet, ← Set.image_univ]
  exact OnePoint.isOpen_image_coe.mpr
    (isOpen_univ : IsOpen
      (Set.univ : Set (Σ n : Nat, RP (antipodalBlockDimension n))))

theorem measurableSet_finiteBoundarySet : MeasurableSet finiteBoundarySet :=
  isOpen_finiteBoundarySet.measurableSet

theorem finiteBoundarySet_eq_iUnion :
    finiteBoundarySet = ⋃ n : Nat, boundaryCoordinateSet n := by
  ext z
  constructor
  · rintro ⟨⟨n, x⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨x, rfl⟩⟩
  · rw [Set.mem_iUnion]
    rintro ⟨n, x, rfl⟩
    exact ⟨⟨n, x⟩, rfl⟩

theorem finiteBoundarySet_compl :
    finiteBoundarySetᶜ = {(∞ : AntipodalTraceBoundary)} := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [finiteBoundarySet]
  | coe z => simp [finiteBoundarySet]

end

end STW22AntipodalBoundaryComponents
end GroupApproximation

import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the closure of a range

`IsApprox S y` says that `y` lies in the norm closure of the range of an adjointable `S`.
This module shows the closure is closed under `+`, `-`, finite sums and norm limits.
The dense-range proofs for the Mingo--Phillips operator and its adjoint build their
targets from these operations.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v w w'

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B} (S : Adjointable E F)

theorem isApprox_apply (x : E.carrier) : IsApprox S (S.toFun x) := fun _ hε =>
  ⟨x, by rw [sub_self, F.norm_zero_vector]; exact hε.le⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_apply

theorem isApprox_zero : IsApprox S 0 := fun _ hε =>
  ⟨0, by rw [S.map_zero, sub_self, F.norm_zero_vector]; exact hε.le⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_zero

/-- The closure of the range is closed. -/
theorem IsApprox.of_approx {y : F.carrier}
    (h : ∀ ε : ℝ, 0 < ε → ∃ z : F.carrier, IsApprox S z ∧ F.norm (z - y) ≤ ε) :
    IsApprox S y := by
  intro ε hε
  obtain ⟨z, hz, hzy⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨x, hx⟩ := hz (ε / 2) (half_pos hε)
  refine ⟨x, ?_⟩
  calc F.norm (S.toFun x - y) ≤ F.norm (S.toFun x - z) + F.norm (z - y) :=
        modNorm_sub_le F _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hx hzy
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsApprox.of_approx

theorem IsApprox.add {y z : F.carrier} (hy : IsApprox S y) (hz : IsApprox S z) :
    IsApprox S (y + z) := by
  intro ε hε
  obtain ⟨x₁, h₁⟩ := hy (ε / 2) (half_pos hε)
  obtain ⟨x₂, h₂⟩ := hz (ε / 2) (half_pos hε)
  refine ⟨x₁ + x₂, ?_⟩
  have hrw : S.toFun (x₁ + x₂) - (y + z) = (S.toFun x₁ - y) + (S.toFun x₂ - z) := by
    rw [S.map_add]
    abel
  rw [hrw]
  calc F.norm ((S.toFun x₁ - y) + (S.toFun x₂ - z))
      ≤ F.norm (S.toFun x₁ - y) + F.norm (S.toFun x₂ - z) := F.norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h₁ h₂
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsApprox.add

theorem IsApprox.sub {y z : F.carrier} (hy : IsApprox S y) (hz : IsApprox S z) :
    IsApprox S (y - z) := by
  intro ε hε
  obtain ⟨x₁, h₁⟩ := hy (ε / 2) (half_pos hε)
  obtain ⟨x₂, h₂⟩ := hz (ε / 2) (half_pos hε)
  refine ⟨x₁ - x₂, ?_⟩
  have hrw : S.toFun (x₁ - x₂) - (y - z) = (S.toFun x₁ - y) + -(S.toFun x₂ - z) := by
    rw [S.map_sub]
    abel
  rw [hrw]
  calc F.norm ((S.toFun x₁ - y) + -(S.toFun x₂ - z))
      ≤ F.norm (S.toFun x₁ - y) + F.norm (-(S.toFun x₂ - z)) := F.norm_add_le _ _
    _ = F.norm (S.toFun x₁ - y) + F.norm (S.toFun x₂ - z) := by rw [F.norm_neg]
    _ ≤ ε / 2 + ε / 2 := add_le_add h₁ h₂
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsApprox.sub

theorem IsApprox.sum {ι : Type*} (s : Finset ι) (f : ι → F.carrier)
    (h : ∀ i ∈ s, IsApprox S (f i)) : IsApprox S (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsApprox S) (fun _ _ ha hb => ha.add S hb) (isApprox_zero S) h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsApprox.sum

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

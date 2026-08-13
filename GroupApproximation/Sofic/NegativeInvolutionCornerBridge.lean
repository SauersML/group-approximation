import GroupApproximation.Sofic.ApproxInvolutionCorner
import GroupApproximation.Sofic.NegativeInvolutionCornerModel

namespace GroupApproximation
namespace NegativeInvolutionCornerModel

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-! ## Bridge estimates for a rounded central involution -/

/-- Images of two commuting group elements asymptotically commute in every
operator-norm almost representation. -/
theorem map_commutator_vanishing (A : OpAlmostRepresentation G)
    {z : G} (hcentral : ∀ g : G, z * g = g * z) (g : G) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (A.map n z : Matrix (A.model n) (A.model n) ℂ) * A.map n g -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n z) := by
  have hzg := KazhdanCornerMatrices.multiplicativeDefect_vanishing A z g
  have hgz := KazhdanCornerMatrices.multiplicativeDefect_vanishing A g z
  refine (hzg.neg.add hgz).congr ?_
  intro n
  rw [hcentral g]
  noncomm_ring

/-- Centrality remains visible after replacing the approximate involution by
its exact rounded sign. -/
theorem rounded_commutator_vanishing (A : OpAlmostRepresentation G)
    {z : G} (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z)
    (g : G) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      ApproxInvolutionCorner.roundedInvolution
          (A.map n z : Matrix (A.model n) (A.model n) ℂ) * A.map n g -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          ApproxInvolutionCorner.roundedInvolution (A.map n z)) := by
  have hround := ApproxInvolutionCorner.roundedInvolution_sub_map_vanishing A hz
  have hmap := map_commutator_vanishing A hcentral g
  have hmapNorm : ∀ n,
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 := by
    intro n
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary (A.map n g).2).le
  have hright := hround.mul_right_of_norm_le_one
    (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ)) hmapNorm
  have hleft := hround.neg.mul_left_of_norm_le_one
    (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ)) hmapNorm
  refine ((hright.add hmap).add hleft).congr ?_
  intro n
  noncomm_ring


end NegativeInvolutionCornerModel
end GroupApproximation

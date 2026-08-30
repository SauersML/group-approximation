import GroupApproximation.Analysis.VoiculescuPartition
import GroupApproximation.Analysis.VoiculescuCompactSqrt
import GroupApproximation.Analysis.VoiculescuUnitStrongLimit
import GroupApproximation.Analysis.VoiculescuUnitRecursion

/-!
# The monotone unit builds the partition of unity

`QuasicentralPartition` is the datum the general absorption argument cuts the
space with; `MonotoneQuasicentralStatement` is the datum (V1c) is supposed to
supply.  This module proves that the second gives the first, so the two are
joined and nothing between them is left to hope.

Each clause lands on a lemma that was proved for it:

* positivity of `dⱼ` is `CFC.sqrt_nonneg`;
* compactness of `dⱼ` is `VoiculescuCompactSqrt.isCompactOperator_sqrt`, applied
  to the piece, which is a positive compact contraction by
  `MonotoneCompactUnit.succ_sub`;
* the squares resolving the identity is
  `MonotoneCompactUnit.sum_pieceSqrt_sq` — the partial sums of `dⱼ²` are the
  members `e_N` themselves, which is where the `zero` clause of the unit is
  spent — followed by `SequentialCompactUnit.tendsto_apply`, that `e_N → 1`
  strongly;
* summability of the commutators is the second conjunct of the statement
  verbatim, which is why that conjunct was written about the `dⱼ` and not about
  the `e_{j+1} - e_j`.

The first conjunct of `MonotoneQuasicentralStatement` — asymptotic centrality of
the unit itself — is not used here.  It is kept because the landed (V1) is
recovered from it (`quasicentralApproximateUnitSeparable_of_monotone`), so the
strengthened datum stays a strengthening.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **(V1c) supplies the partition of unity.**  Every separable Hilbert space
carrying the monotone quasicentral unit carries the partition the general
absorption argument runs on. -/
theorem exists_quasicentralPartition_of_monotoneQuasicentral
    (h : MonotoneQuasicentralStatement) (K : Type) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (S : ℕ → (K →L[ℂ] K)) :
    Nonempty (QuasicentralPartition K S) := by
  obtain ⟨u, -, hsum⟩ := h K S
  refine ⟨{ d := u.pieceSqrt
            nonneg := u.pieceSqrt_nonneg
            isCompact := fun j ↦
              isCompactOperator_sqrt (u.piece_nonneg j) (u.piece_isCompact j)
            tendsto_sum_sq := fun x ↦ ?_
            summable_comm := hsum }⟩
  refine Tendsto.congr (fun N ↦ ?_) (u.toSequentialCompactUnit.tendsto_apply x)
  rw [← u.sum_pieceSqrt_sq N]
  simp

/-- **The partition exists unconditionally.**  The recursive V1c construction
now supplies the exact strengthened unit consumed above. -/
theorem nonempty_quasicentralPartition (K : Type) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (S : ℕ → (K →L[ℂ] K)) : Nonempty (QuasicentralPartition K S) :=
  exists_quasicentralPartition_of_monotoneQuasicentral
    monotoneQuasicentralStatement K S

end

end ShulmanFill
end GroupApproximation

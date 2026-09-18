import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.StandardComplete
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: series in a Hilbert module

* `isCauchy_partialSum`: a series dominated termwise by a summable real series has Cauchy
  partial sums. In a complete module the partial sums therefore converge.
* `inner_eq_tsum_of_isLimit`: pairing with a limit of partial sums gives the series of the
  pairings.

The adjoint of the Mingo--Phillips operator is built from a series in `E`, and these two
facts are what the adjoint relation needs.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule Filter Topology

universe v w

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **A dominated series has Cauchy partial sums.** -/
theorem isCauchy_partialSum {E : CStarModule.{v, w} B} (a : ℕ → E.carrier) {r : ℕ → ℝ}
    (hr : Summable r) (ha : ∀ n, E.norm (a n) ≤ r n) :
    IsCauchy E fun N => ∑ n ∈ Finset.range N, a n := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hr.tendsto_sum_tsum_nat.cauchySeq ε hε
  have hle : ∀ m n : ℕ, N ≤ m → N ≤ n → m ≤ n →
      E.norm (∑ i ∈ Finset.range n, a i - ∑ i ∈ Finset.range m, a i) ≤ ε := by
    intro m n hm hn hmn
    have hd := hN n hn m hm
    rw [Real.dist_eq, ← Finset.sum_Ico_eq_sub r hmn] at hd
    rw [← Finset.sum_Ico_eq_sub a hmn]
    calc E.norm (∑ i ∈ Finset.Ico m n, a i) ≤ ∑ i ∈ Finset.Ico m n, E.norm (a i) :=
          E.norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Ico m n, r i := Finset.sum_le_sum fun i _ => ha i
      _ ≤ |∑ i ∈ Finset.Ico m n, r i| := le_abs_self _
      _ ≤ ε := hd.le
  intro m n hm hn
  rcases le_total m n with hmn | hnm
  · rw [modNorm_sub_comm]
    exact hle m n hm hn hmn
  · exact hle n m hn hm hnm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isCauchy_partialSum

/-- **Pairing with a limit of partial sums.** -/
theorem inner_eq_tsum_of_isLimit {E : CStarModule.{v, w} B} {a : ℕ → E.carrier}
    {L : E.carrier} (hL : IsLimit E (fun N => ∑ n ∈ Finset.range N, a n) L) (y : E.carrier)
    (hs : Summable fun n => E.inner y (a n)) :
    E.inner y L = ∑' n, E.inner y (a n) := by
  have h1 := hL.tendsto_inner_right y
  have h2 : Tendsto (fun N => E.inner y (∑ n ∈ Finset.range N, a n)) atTop
      (𝓝 (∑' n, E.inner y (a n))) :=
    hs.tendsto_sum_tsum_nat.congr fun N => (E.inner_sum_right (Finset.range N) y a).symm
  exact tendsto_nhds_unique h1 h2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.inner_eq_tsum_of_isLimit

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

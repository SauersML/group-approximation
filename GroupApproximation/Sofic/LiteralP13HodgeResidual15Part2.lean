import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 18--26 for residual block (1, 5). -/

namespace Residual15Part2

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![153320421, 130072740, 210165901, 111295816, 373411771, 175886734, 177327602, 567256816, 143605882]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 5 (finProdFinEquiv ((2 : Fin 4), u)) = expected u

/-- The identity-containing chunk is split into eight coefficient checks. -/
def chunk25Expected : Fin 8 → Nat := ![27172063, 195588232, 151687450, 19246674, 44266393, 9044252, 55973157, 64278595]

def chunk25Check (u : Fin 8) : Prop :=
  (residualNumerator 1 5
    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
      chunk25Expected u

mk_kernel_batched_theorem 8 chunk25Check

theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=
  combine_kernel_batched_theorems% chunk25Check 8

theorem chunk25 : initialChunk 1 5 25 = 567256816 := by
  unfold initialChunk
  calc
    ∑ u : Fin 8,
        (residualNumerator 1 5
          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
        ∑ u : Fin 8, chunk25Expected u := by
      apply Finset.sum_congr rfl
      intro u _
      exact chunk25All u
    _ = 567256816 := by decide +kernel

mk_kernel_batched_theorem_except 9 7 check

theorem check.case_7 : check 7 := by
  unfold check
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) =
      (25 : Fin 36) by decide +kernel]
  simpa [expected] using chunk25

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual15Part2

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_2 : initialPart 1 5 2 = 2042343683 := by
  have hpart : initialPart 1 5 2 =
      ∑ u : Fin 9, Residual15Part2.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual15Part2.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation

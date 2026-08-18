import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 18--26 for residual block (1, 0). -/

namespace Residual10Part2

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![199570698, 129633692, 340264564, 145910225, 414361029, 202245321, 237656202, 531006059, 159936432]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 0 (finProdFinEquiv ((2 : Fin 4), u)) = expected u

/-- The identity-containing chunk is split into eight coefficient checks. -/
def chunk25Expected : Fin 8 → Nat := ![93574498, 191278819, 12896236, 61277304, 35454390, 6040653, 92453524, 38030635]

def chunk25Check (u : Fin 8) : Prop :=
  (residualNumerator 1 0
    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
      chunk25Expected u

mk_kernel_batched_theorem 8 chunk25Check

theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=
  combine_kernel_batched_theorems% chunk25Check 8

theorem chunk25 : initialChunk 1 0 25 = 531006059 := by
  unfold initialChunk
  calc
    ∑ u : Fin 8,
        (residualNumerator 1 0
          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
        ∑ u : Fin 8, chunk25Expected u := by
      apply Finset.sum_congr rfl
      intro u _
      exact chunk25All u
    _ = 531006059 := by decide +kernel

mk_kernel_batched_theorem_except 9 7 check

theorem check.case_7 : check 7 := by
  unfold check
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) =
      (25 : Fin 36) by decide +kernel]
  simpa [expected] using chunk25

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual10Part2

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_2 : initialPart 1 0 2 = 2360584222 := by
  have hpart : initialPart 1 0 2 =
      ∑ u : Fin 9, Residual10Part2.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual10Part2.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation

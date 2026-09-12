import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 18--26 for residual block (2, 2). -/

namespace Residual22Part2

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![245945797, 141487774, 291856908, 176937836, 227733236, 340498991, 313623817, 11615939367470, 281455932]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 2 (finProdFinEquiv ((2 : Fin 4), u)) = expected u

/-- The identity-containing chunk is split into eight coefficient checks. -/
def chunk25Expected : Fin 8 → Nat := ![17875274, 11615615354728, 17875274, 15527962, 135436622, 15681651, 30727582, 90888377]

def chunk25Check (u : Fin 8) : Prop :=
  (residualNumerator 2 2
    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
      chunk25Expected u

mk_kernel_batched_theorem 8 chunk25Check

theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=
  combine_kernel_batched_theorems% chunk25Check 8

theorem chunk25 : initialChunk 2 2 25 = 11615939367470 := by
  unfold initialChunk
  calc
    ∑ u : Fin 8,
        (residualNumerator 2 2
          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
        ∑ u : Fin 8, chunk25Expected u := by
      apply Finset.sum_congr rfl
      intro u _
      exact chunk25All u
    _ = 11615939367470 := by decide +kernel

mk_kernel_batched_theorem_except 9 7 check

theorem check.case_7 : check 7 := by
  unfold check
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) =
      (25 : Fin 36) by decide +kernel]
  simpa [expected] using chunk25

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual22Part2

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_2 : initialPart 2 2 2 = 11617958907761 := by
  have hpart : initialPart 2 2 2 =
      ∑ u : Fin 9, Residual22Part2.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual22Part2.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation

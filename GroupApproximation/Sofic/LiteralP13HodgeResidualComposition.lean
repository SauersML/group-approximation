import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

/-!
# Symbolic composition of exact P13 residual subtotals

This lemma composes four independently checked residual subtotals without
reducing their concrete certificate proofs again in every block wrapper.
-/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

open scoped BigOperators

theorem sum_natAbs_eq_of_part_sums (i k : Fin 6) {a0 a1 a2 a3 : ℕ}
    (h0 : initialPart i k 0 = a0)
    (h1 : initialPart i k 1 = a1)
    (h2 : initialPart i k 2 = a2)
    (h3 : initialPart i k 3 + finalChunk i k = a3) :
    ∑ c : Fin 293, (residualNumerator i k c).natAbs =
      ((a0 + a1) + a2) + a3 := by
  calc
    ∑ c : Fin 293, (residualNumerator i k c).natAbs =
        (∑ p : Fin 4, initialPart i k p) + finalChunk i k :=
      sum_natAbs_eq_parts i k
    _ = (((initialPart i k 0 + initialPart i k 1) +
        initialPart i k 2) + initialPart i k 3) + finalChunk i k := by
      rw [Fin.sum_univ_four]
    _ = ((initialPart i k 0 + initialPart i k 1) +
        initialPart i k 2) + (initialPart i k 3 + finalChunk i k) :=
      Nat.add_assoc _ _ _
    _ = ((a0 + a1) + a2) + a3 :=
      congrArg₂ Nat.add
        (congrArg₂ Nat.add (congrArg₂ Nat.add h0 h1) h2) h3

end LiteralP13HodgeCertificate
end GroupApproximation

import Mathlib
import GroupApproximation.Meta.AxiomGuard

/-!
# Local non-metabelianity of `[[T]]`, part 2: the finite computation in `S_5`

Infrastructure lane `sk-flip-05` (census row `2e7c7d9ab149`, absent from the current tex).

With Mathlib's conventions `⁅g, h⁆ = g h g⁻¹ h⁻¹` and `(σ τ) x = σ (τ x)`:

* `p := ⁅(0 1), (1 2)⁆` is the 3-cycle `0 ↦ 2 ↦ 1 ↦ 0`, and `q := ⁅(2 3), (3 4)⁆` is the
  3-cycle `2 ↦ 4 ↦ 3 ↦ 2`.
* `⁅p, q⁆ 2 = p (q (p⁻¹ (q⁻¹ 2))) = p (q (p⁻¹ 3)) = p (q 3) = p 2 = 1 ≠ 2`, so
  `⁅⁅(0 1), (1 2)⁆, ⁅(2 3), (3 4)⁆⁆ ≠ 1` (`perm_fin_five_commutator_commutator_ne_one`).
* `((0 1) (1 2)) 0 = 1` and `((1 2) (0 1)) 0 = 2`, so `(0 1)` and `(1 2)` do not commute
  (`perm_fin_five_swap_mul_ne`).

Both evaluations at a point are checked by `decide` (kernel-checkable, no `native_decide`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open scoped commutatorElement

/-- A double commutator of transpositions in `S_5` is nontrivial: `S_5` is not metabelian. -/
theorem perm_fin_five_commutator_commutator_ne_one :
    ⁅⁅(Equiv.swap 0 1 : Equiv.Perm (Fin 5)), (Equiv.swap 1 2 : Equiv.Perm (Fin 5))⁆,
      ⁅(Equiv.swap 2 3 : Equiv.Perm (Fin 5)), (Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁆⁆ ≠
        (1 : Equiv.Perm (Fin 5)) := by
  intro h
  exact absurd (DFunLike.congr_fun h 2) (by decide)

/-- The transpositions `(0 1)` and `(1 2)` of `S_5` do not commute. -/
theorem perm_fin_five_swap_mul_ne :
    (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) ≠
      (Equiv.swap 1 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 5)) := by
  intro h
  exact absurd (DFunLike.congr_fun h 0) (by decide)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.perm_fin_five_commutator_commutator_ne_one
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.perm_fin_five_swap_mul_ne

import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Sum

/-!
# A fixed-point-free involution halves its type

If `σ` is a fixed-point-free involution on a finite `LinearOrder`, the sets
`{x | x < σ x}` and `{x | σ x < x}` partition the type and are in bijection
with each other via `σ` itself, so each is exactly half.

This is the general fact behind the seam-counting arguments in
`GGT/VanKampen/CombMapGluing.lean`: a `copyMate : Perm (Fin n)` (or any
fixed-point-free involution used to pair up finitely many objects) always has
an even number of objects, split evenly by any linear order. It is not
consumed anywhere yet; it is landed because it is the fact any future
general-`n` seam-counting argument in that file will need, and the five-line
proof is cheaper to have on hand than to re-derive under pressure.

`GroupApproximation/Algebra/InvolutionBlockSplit.lean` proves the analogous
fact in `Equiv.Perm` cycle-type language (`card_support_eq_two_of_mem`,
`Equiv.Perm.cycleType`); this file proves it directly from a `LinearOrder`
instead, since a `Fin n`-indexed `copyMate` always carries one for free and
the cycle-type route needs `DecidableEq` and cycle-factor bookkeeping this
argument does not.
-/

namespace GroupApproximation

/-- **A fixed-point-free involution halves a finite `LinearOrder`.**
`{x // x < σ x}` and `{x // σ x < x}` partition the type (linear order
trichotomy, with the fixed-point-freeness ruling out equality) and are in
bijection via `σ` (an involution swaps which side of the pair each element
of a `σ`-orbit is on), so the total count is twice either one. -/
theorem card_eq_two_mul_card_lt_of_fixedPointFree_involutive
    {α : Type*} [Fintype α] [LinearOrder α] {σ : Equiv.Perm α}
    (hinv : Function.Involutive σ) (hfree : ∀ x, σ x ≠ x) :
    Fintype.card α = 2 * Fintype.card {x : α // x < σ x} := by
  classical
  have hcompl : ∀ x, ¬ x < σ x ↔ σ x < x := by
    intro x
    constructor
    · intro hn
      rcases (not_lt.mp hn).lt_or_eq with h | h
      · exact h
      · exact absurd h (hfree x)
    · intro h
      exact not_lt.mpr h.le
  have hequiv : {x : α // x < σ x} ≃ {x : α // σ x < x} :=
    { toFun := fun x => ⟨σ x.1, by rw [hinv x.1]; exact x.2⟩
      invFun := fun y => ⟨σ y.1, by rw [hinv y.1]; exact y.2⟩
      left_inv := fun x => Subtype.ext (hinv x.1)
      right_inv := fun y => Subtype.ext (hinv y.1) }
  have hcard : Fintype.card α =
      Fintype.card {x : α // x < σ x} + Fintype.card {x : α // ¬ x < σ x} := by
    rw [← Fintype.card_congr (Equiv.sumCompl (fun x => x < σ x)), Fintype.card_sum]
  rw [hcard, Fintype.card_congr (Equiv.subtypeEquivRight hcompl),
    ← Fintype.card_congr hequiv]
  omega

end GroupApproximation

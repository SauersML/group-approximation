import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.Rat.Denumerable
import Mathlib.Order.PiLex
import GroupApproximation.ThompsonOre.ThompsonF

/-!
# `K[F]` has no zero divisors

`F` acts faithfully on `ℚ` by strictly increasing maps.  Reading `ev g` along an enumeration of
`ℚ` gives an injection `evSeq` into `Lex (ℕ → ℚ)`, and the pulled-back linear order on `F` is
invariant under left multiplication, since every `ev c` is strictly increasing.  A
left-invariant linear order gives `TwoUniqueProds F`, so `K[F]` has no zero divisors over any
semiring without zero divisors.
-/

namespace GroupApproximation
namespace ThompsonOre

noncomputable section

/-- The values of `ev g` along the enumeration of `ℚ`. -/
def evSeq (g : ThompsonF) : Lex (ℕ → ℚ) :=
  toLex fun i => ev g (Denumerable.ofNat ℚ i)

theorem evSeq_injective : Function.Injective evSeq := by
  intro a b h
  apply ev_injective
  ext t
  obtain ⟨n, rfl⟩ := (Denumerable.eqv ℚ).symm.surjective t
  exact congrFun (congrArg ofLex h) n

/-- Left multiplication preserves the lexicographic order of `evSeq`. -/
theorem evSeq_mul_lt (c : ThompsonF) {a b : ThompsonF} (h : evSeq a < evSeq b) :
    evSeq (c * a) < evSeq (c * b) := by
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, fun j hj => ?_, ?_⟩
  · show ev (c * a) (Denumerable.ofNat ℚ j) = ev (c * b) (Denumerable.ofNat ℚ j)
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact congrArg (ev c) (hi j hj)
  · show ev (c * a) (Denumerable.ofNat ℚ i) < ev (c * b) (Denumerable.ofNat ℚ i)
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact ev_strictMono c hlt

/-- `F` is left-orderable, so it has two unique products. -/
instance twoUniqueProds : TwoUniqueProds ThompsonF :=
  letI : LinearOrder ThompsonF := LinearOrder.lift' evSeq evSeq_injective
  haveI : MulLeftStrictMono ThompsonF := ⟨fun c _ _ h => evSeq_mul_lt c h⟩
  TwoUniqueProds.of_covariant_right

/-- **`K[F]` has no zero divisors.** -/
instance noZeroDivisors {K : Type*} [Semiring K] [NoZeroDivisors K] :
    NoZeroDivisors (MonoidAlgebra K ThompsonF) :=
  inferInstance

end

end ThompsonOre
end GroupApproximation

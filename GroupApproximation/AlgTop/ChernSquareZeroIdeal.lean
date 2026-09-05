import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# The square-zero hypothesis, supplied by a square-zero class

The square-zero Newton step
`GroupApproximation.AlgTop.natCast_mul_chern_eq_of_squareZero` takes the
hypothesis

```text
∀ i j, 0 < i → 0 < j → c i * p j = 0.
```

In Lemma 3 of the STW Problem LIX manuscript that hypothesis is supplied by a
single element: the virtual class `δ` has `ch(δ) = z · ch(β)` with
`z = t x ∈ H^6(S¹ × S⁵; ℤ)` and `z² = 0`, so every positive Chern class and every
positive power sum of `δ` is a multiple of `z`, and any two of them multiply to
zero.

This file is that one-line bridge, stated so that a consumer never has to
re-derive it.  It is deliberately separate from the Newton file: the Newton step
is about sequences, this is about where the sequences live.

## Main declarations

* `mul_eq_zero_of_mem_squareZero` — two multiples of a square-zero element
  multiply to zero.
* `squareZero_of_dvd_squareZero` — the hypothesis `hsq` in the exact shape the
  Newton step wants.
-/

namespace GroupApproximation
namespace AlgTop

variable {A : Type*} [CommRing A]

/-- Two multiples of a square-zero element multiply to zero. -/
theorem mul_eq_zero_of_mem_squareZero {z a b : A} (hz : z * z = 0) :
    z * a * (z * b) = 0 := by
  calc z * a * (z * b) = z * z * (a * b) := by ring
    _ = 0 := by rw [hz, zero_mul]

/-- The square-zero hypothesis of the Newton step, supplied by divisibility by a
single square-zero class `z`.  This is what `z² = 0` gives in the manuscript. -/
theorem squareZero_of_dvd_squareZero (c p : ℕ → A) {z : A} (hz : z * z = 0)
    (hc : ∀ i, 0 < i → z ∣ c i) (hp : ∀ j, 0 < j → z ∣ p j) :
    ∀ i j, 0 < i → 0 < j → c i * p j = 0 := by
  intro i j hi hj
  obtain ⟨a, ha⟩ := hc i hi
  obtain ⟨b, hb⟩ := hp j hj
  rw [ha, hb]
  exact mul_eq_zero_of_mem_squareZero hz

end AlgTop
end GroupApproximation

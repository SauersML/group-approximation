import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The sign of the vertex-reversal operator

Graded commutativity of the singular cup product is proved by comparing a
cochain with its pullback along the **vertex reversal** of each simplex.  The
reversal is a chain map only after each simplex is weighted by

```text
revSign n = (-1)^{n(n+1)/2},
```

and the whole sign bookkeeping of that argument comes down to two facts about
the weight:

* `revSign_succ` — `revSign (n+1) = (-1)^{n+1} · revSign n`, which is what makes
  the reversal commute with the boundary: the `i`-th face of a reversed simplex
  is the reverse of its `(n-i)`-th face, and reindexing the alternating sum
  costs exactly `(-1)^n`.
* `revSign_add` — `revSign (p+q) = (-1)^{p q} · revSign p · revSign q`.  **This
  is where the Koszul sign of graded commutativity comes from, and nowhere
  else.**

The file is pure `ℤ` algebra — no topology, no cochains, no dependence on the
singular-cohomology modules — so the arithmetic backbone of the commutativity
theorem can land green independently of the state of the vendored port.

## Main declarations

* `revSign` — the reversal weight, defined by recursion rather than as
  `(-1)^(n*(n+1)/2)`, so that no natural-number division ever appears.
* `revSign_sq` — the weight squares to one.
* `revSign_add` — the Koszul identity.
* `revSign_add_even` — the specialization the Chern-class layer uses: between
  even degrees the Koszul sign is `+1`, so the weight is simply multiplicative.
-/

namespace GroupApproximation
namespace AlgTop

/-- The weight `(-1)^{n(n+1)/2}` attached to a reversed `n`-simplex, defined by
recursion so that no natural-number division occurs. -/
def revSign : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1) ^ (n + 1) * revSign n

@[simp] theorem revSign_zero : revSign 0 = 1 := rfl

theorem revSign_succ (n : ℕ) : revSign (n + 1) = (-1) ^ (n + 1) * revSign n := rfl

@[simp] theorem revSign_one : revSign 1 = -1 := by
  rw [revSign_succ, revSign_zero, pow_one, mul_one]

/-- The reversal weight is a sign. -/
theorem revSign_sq (n : ℕ) : revSign n * revSign n = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : ((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ (n + 1)) = 1 := by
        rw [← pow_add]
        have h2 : (n + 1) + (n + 1) = 2 * (n + 1) := by ring
        rw [h2, pow_mul]
        norm_num
      rw [revSign_succ]
      calc (-1 : ℤ) ^ (n + 1) * revSign n * ((-1) ^ (n + 1) * revSign n)
          = ((-1 : ℤ) ^ (n + 1) * (-1) ^ (n + 1)) * (revSign n * revSign n) := by ring
        _ = 1 := by rw [hp, ih, mul_one]

theorem revSign_ne_zero (n : ℕ) : revSign n ≠ 0 := by
  intro h
  have hsq := revSign_sq n
  rw [h, zero_mul] at hsq
  exact absurd hsq (by norm_num)

/-- **The Koszul identity.**  `revSign (p+q) = (-1)^{pq} · revSign p · revSign q`.
This single fact is where the sign `(-1)^{pq}` of graded commutativity comes
from. -/
theorem revSign_add (p q : ℕ) :
    revSign (p + q) = (-1 : ℤ) ^ (p * q) * revSign p * revSign q := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hstep : p + (q + 1) = (p + q) + 1 := by omega
      have key : (-1 : ℤ) ^ (p + q + 1) * ((-1 : ℤ) ^ (p * q))
          = (-1 : ℤ) ^ (p * (q + 1)) * (-1 : ℤ) ^ (q + 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      rw [hstep, revSign_succ, ih, revSign_succ]
      calc (-1 : ℤ) ^ (p + q + 1) * ((-1 : ℤ) ^ (p * q) * revSign p * revSign q)
          = ((-1 : ℤ) ^ (p + q + 1) * (-1) ^ (p * q)) * (revSign p * revSign q) := by ring
        _ = ((-1 : ℤ) ^ (p * (q + 1)) * (-1) ^ (q + 1)) * (revSign p * revSign q) := by
              rw [key]
        _ = (-1 : ℤ) ^ (p * (q + 1)) * revSign p * ((-1) ^ (q + 1) * revSign q) := by ring

/-- **Between even degrees the Koszul sign is `+1`.**  This is the only case the
Chern-class layer needs, and it is why `⨁_n H^{2n}(X;ℤ)` is a *commutative* ring
rather than merely a graded one. -/
theorem revSign_add_even (p q : ℕ) :
    revSign (2 * p + 2 * q) = revSign (2 * p) * revSign (2 * q) := by
  have h : (-1 : ℤ) ^ (2 * p * (2 * q)) = 1 := by
    have he : 2 * p * (2 * q) = 2 * (2 * (p * q)) := by ring
    rw [he, pow_mul]
    norm_num
  rw [revSign_add, h, one_mul]

end AlgTop
end GroupApproximation

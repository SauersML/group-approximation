-- `Mathlib/Algebra/GroupPower/` no longer exists at pin `81a5d257`; all three
-- parity facts used here live in `Mathlib/Algebra/Ring/Parity.lean`
-- (`Even.neg_one_pow` l.47, `Even.mul_left` l.63, `Nat.Odd.sub_odd` l.301).
-- `Nat.Prime.dvd_choose_self` is `Mathlib/Data/Nat/Choose/Dvd.lean` l.35.
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic

/-!
# The one fact that makes odd `p` easier than `p = 2`

This lane's plan originally said "`p` odd enters in exactly two places".
`sp-design`'s review corrected that: it is **one** fact used three times, and it
is this file.

```text
    p odd  ⟹  (-1) ^ (a * (p - 1)) = 1   for every a
```

The three uses:

* the evaluating functional `u^{⊗p}` is invariant under the cyclic action on the
  nose, because on the diagonal bidegree the Koszul sign is `(-1)^{q²(p-1)}`;
* the alternating functional `u ⊗ v ⊗ u ⊗ v ⊗ ⋯` on `2p` slots is invariant
  under the block shift, with `a = (deg u + deg v)²` in place of `q²`;
* the cyclic shift of an `r`-tuple has order `r` on the nose rather than up to a
  sign.

At `p = 2` the same expression is `(-1)^{a}`, which is not `1`, and the mod-2
tree does not need it to be, because `-1 = 1` there.  So this is genuinely a
place where the odd-primary construction is *cleaner* than the mod-2 one rather
than harder, and it is worth having as a named lemma rather than as three
appeals to parity.
-/

namespace GroupApproximation.CharClass

/-- `p - 1` is even when `p` is odd. -/
theorem even_pred_of_odd {p : ℕ} (hp : Odd p) : Even (p - 1) :=
  Nat.Odd.sub_odd hp odd_one

/-- **The odd-primary sign lemma.**  Any multiple of `p - 1` is an even
exponent, so every Koszul sign this lane meets on a diagonal bidegree is `+1`. -/
theorem neg_one_pow_mul_pred {R : Type*} [Monoid R] [HasDistribNeg R]
    {p : ℕ} (hp : Odd p) (a : ℕ) : ((-1 : R)) ^ (a * (p - 1)) = 1 :=
  ((even_pred_of_odd hp).mul_left a).neg_one_pow

/-- The same fact with the factors in the other order, which is the shape the
tuple-model signs arrive in. -/
theorem neg_one_pow_pred_mul {R : Type*} [Monoid R] [HasDistribNeg R]
    {p : ℕ} (hp : Odd p) (a : ℕ) : ((-1 : R)) ^ ((p - 1) * a) = 1 := by
  rw [mul_comm]
  exact neg_one_pow_mul_pred hp a

/-- **The number of ordered pairs `u < v` in `[0, p)` vanishes mod `p`.**

This is the whole reason the `(odd, odd)` blocks of the resolution's coproduct
have reduced coefficient zero, which is in turn what kills the two competing
terms in the Cartan identity that bridges `c_1` to `c_2` — see §6.2 of this
lane's report.  The integral count `p(p-1)/2` is not zero; it is the reduction
mod `p` that kills it, and it does so precisely because `p` is odd, so that
`(p-1)/2` is an integer and the count is `p` times something. -/
theorem choose_two_cast_eq_zero (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    ((p.choose 2 : ℕ) : ZMod p) = 0 :=
  (CharP.cast_eq_zero_iff (ZMod p) p _).2 (hp.dvd_choose_self two_ne_zero hp2)

end GroupApproximation.CharClass

---
rg: 2
id: thompson-f-ore-radius-function-is-not-quasi-polynomial-proof
kind: route
title: Theorem A gives a (1 + ln n)-expanding set in a ball of iterated Ore radius; telescoping and Moore's tower bound make every elementary-iterable Ore radius function impossible
target: thompson-f-ore-radius-function-is-not-quasi-polynomial
requires:
  - ore-radius-function-bounds-folner-radius
  - thompson-f-folner-function-exceeds-every-tower
  - thompson-f-is-bi-orderable
artifacts:
  - experiments/ore-radius-folner-2026-09-17/check_local_bartholdi.py
---

Notation as in the claim. Write `E_i = exp_i` and `L_j = log_j`.

**Step 0 (hypotheses of Theorem A).** `K[F]` has no zero divisors for every field `K`. By
`thompson-f-is-bi-orderable`, `F` has a bi-invariant total order `<`. For nonzero `x, y ∈ K[F]` with
largest support elements `g, h`, every other product `g'h'` in `xy` satisfies `g'h' < gh`, so the
coefficient of `gh` in `xy` is the product of two nonzero scalars. `S` is symmetric and contains `1`,
and `|B(1)| = 5`, so `n = |B(k)| >= 5 >= 3` and `n <= 5^k`.

**Step 1 (an expanding set).** Assume `Ω_K` is finite, and let `p = (r-1)d` and `ρ_* = τ^(p)(k)`. By
`ore-radius-function-bounds-folner-radius` (Theorem A) there is a finite nonempty `F_0 ⊆ B(ρ_* - k)`
with `|B(k)F_0| < (1 + ln n)|F_0|`.

**Step 2 (telescoping).** Put `F_i = B(i) F_0` for `0 <= i <= k`, so that
`F_(i+1) = B(1) F_i ⊆ B(ρ_*)`. Since `1 ∈ S`, each ratio `|F_(i+1)|/|F_i|` is at least `1`, and their
product is `|F_k|/|F_0| < 1 + ln n <= 1 + k ln 5`. So some `i < k` has `|B(1) Z| < (1 + δ)|Z|` with
`Z = F_i` and `δ = (1 + k ln 5)^(1/k) - 1`.

Put `x = ln(1 + k ln 5)/k`. Then `x <= 1` for all `k >= 1`, and `e^x - 1 <= 2x` on `[0,1]`, so
`δ <= 2 ln(1 + k ln 5)/k`.

**Step 3 (a Følner set).** For `γ ∈ Γ = {x_0^±1, x_1^±1}`, `γZ ⊆ B(1)Z`, so `|γZ ∖ Z| < δ|Z|` and
`|γZ Δ Z| = 2|γZ ∖ Z| < 2δ|Z|`. Let `A = Z^-1`. Then `|Aγ Δ A| = |γ^-1 Z Δ Z|`, and `Γ` is symmetric, so

`Σ_(γ∈Γ) |Aγ Δ A| < 8δ|A| <= 16 ln(1 + k ln 5)/k · |A|`.

Moore's definition (arXiv:0905.1118v7, as recorded in `thompson-f-cardinality-certificates-need-tower-degree-proof`):
`A` is `ε`-Følner with respect to `Γ` if `Σ_(γ ∈ Γ) |(A·γ) Δ A| < ε|A|`. Moore's Theorem 1.1, verbatim
from `thompson-f-folner-function-exceeds-every-tower`:

> For every finite symmetric generating set Γ⊆F there is a constant C>1 such that if A⊆F is a
> C^−n-Følner set with respect to Γ, then A contains at least exp_n(0) elements.

If `16 C^m ln(1 + k ln 5) <= k`, then `A` is `C^-m`-Følner, so
`E_m(0) <= |A| = |Z| <= |B(ρ_*)| <= 5^(ρ_*)`. This is Theorem B.

**Step 4 (the class kill).** Fix `j, c >= 1` and suppose `Ω_K(R) <= E_j((L_j R)^c)` for all
`R >= R_0`. Then `Ω_K` is finite: it is finite for `R >= R_0`, and it is nondecreasing. Put
`f(R) = E_j((L_j R)^(2c))`. Three facts:
- *Pointwise bound.* For `y >= 1` and `i >= 1`, `E_i(y + 1) >= E_i(y)^2 >= 2E_i(y)`, by induction from
  `E_1(y+1) = 2E_1(y)`. And `y^c + 1 <= y^(2c)` for `y >= 2`. So for `R >= R_1 = max(R_0, E_j(2))`,
  `τ(R) <= 2E_j((L_j R)^c) <= E_j((L_j R)^c + 1) <= f(R)`.
- *Monotonicity.* `f` is nondecreasing, `τ(R) >= R`, and `L_j f(R) = (L_j R)^(2c)`.
- *Iteration.* For `k >= R_1`, induction gives
  `τ^(p)(k) <= f^(p)(k) = E_j((L_j k)^((2c)^p))`.

*Size of `p`.* We have `r <= (1 + ln n) n! + 1 <= n^n` and `d <= n^2 + n log_2 n + 2 <= n^3`, so
`p <= n^(n+3)`. With `n <= 5^k`, `log_2 p <= (5^k + 3) k log_2 5 <= 2^(3k)` for `k >= 6`, so
`p <= E_2(3k)`.

*Upper bound.* Since `L_j k <= k`,
`(L_j k)^((2c)^p) <= 2^(2^(p log_2(2c) + log_2 log_2 k))`. For large `k`,
`p log_2(2c) + log_2 log_2 k <= E_2(3k)^2 <= E_2(3k + 1)`. Hence
- `(L_j k)^((2c)^p) <= E_2(E_2(3k+1)) = E_4(3k+1)`;
- `ρ_* <= E_(j+4)(3k+1)`;
- `5^(ρ_*) <= 2^(3 E_(j+4)(3k+1)) <= E_(j+5)(3k+2)`.

*Lower bound.* Let `m(k)` be the largest integer with `16 C^m ln(1 + k ln 5) <= k`. Then
`m(k) >= log_C(k / (16 ln(1 + k ln 5))) - 1`, which tends to infinity. Theorem B gives
`E_(j+5)(E_(m-j-5)(0)) = E_m(0) <= E_(j+5)(3k+2)`, and `E_(j+5)` is strictly increasing, so
`E_(h)(0) <= 3k + 2` with `h = m(k) - j - 5`.

*Contradiction.* By induction, `E_h(0) >= 2^(2^(h-3))` for `h >= 3`. Here `h >= log_C k - O(1)`, so
`2^(h-3) >= k^(1/log_2 C) / O(1)`, and `E_h(0) >= 2^(Ω(k^ε))` with `ε = 1/log_2 C > 0`. This exceeds
`3k + 2` for large `k`.

So the supposition is false: for every `R_0` some `R >= R_0` violates the bound. If some `Ω_K(R)` is
infinite, monotonicity makes the bound fail for all larger `R`. ∎

**Where exponential control survives.** If `τ(R) ≈ 2^R`, then `τ^(p)(k)` is a tower of height about
`p ~ E_2(3k)`. Step 4 then only yields `E_m(0) <= E_(E_2(3k))(k)`, which is consistent with
`m ~ log_C k`. Killing that class this way needs an elimination depth below about `log_C k`.
- Bartholdi's alphabet has width `r > n = |B(k)|`, and `n` grows exponentially in `k` because `F`
  has exponential growth.
- A polynomial-size alphabet would therefore not suffice either.
- A different mechanism is needed, for example extracting expansion from a bounded number of Ore
  steps.

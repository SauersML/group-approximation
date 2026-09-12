---
rg: 2
id: torsion-free-small-spread-integer-atomic-proof
kind: route
title: Continue the integer zeta series outside the spectral interval and apply Pólya's rationality theorem
target: torsion-free-small-spread-spectra-are-integer-atomic
requires:
  - torsion-free-integral-zeta-is-an-integer-euler-product
  - polya-integer-series-rational-off-small-capacity
---

Let `mu = mu_T`, a positive measure of total mass `n` on `[a,b]`, with
`b - a < 4`, and let `m_j = Tr(T^j)`.

**Step 1: integrality.** By the Euler product theorem,
`zeta(z) = exp(sum_(j>=1) m_j z^j / j) in 1 + z Z[[z]]`. So

```text
f(w) := w^(-n) zeta(1/w) = sum_(k >= 0) c_k w^(-n-k),   c_k in Z,
```

converges for `|w| > R = max(|a|, |b|)`.

**Step 2: continuation.**

- For `|w| > R`,
  `zeta(1/w) = exp(-integral log(1 - x/w) d mu(x))`. Since
  `log(w - x) = log w + log(1 - x/w)` and `mu` has total mass `n`,
  `f(w) = exp(-integral log(w - x) d mu(x))`.
- Put `F(w) = exp(-integral log(w - x) d mu(x))` on `C` minus `[a,b]`. The
  integral is locally holomorphic in `w`. Continuing it once around `[a,b]`
  adds `2 pi i n`, and `n` is an integer, so `F` is single-valued and
  holomorphic there.
- Near infinity `F = f = w^(-n)(1 + O(1/w))`. So `f` continues holomorphically
  to the Riemann sphere minus `[a,b]`.

**Step 3: rationality.** `[a,b]` has capacity `(b-a)/4 < 1` and connected
complement. By `polya-integer-series-rational-off-small-capacity`, `F` is
rational.

**Step 4: the measure.**

- `F` is an exponential, so it has no zeros or poles off `[a,b]`. A rational
  function with `F(w) ~ w^(-n)` at infinity is therefore
  `F(w) = prod_i (w - lambda_i)^(-k_i)` with `lambda_i in [a,b]`, `k_i in Z`
  and `sum_i k_i = n`.
- Differentiating,
  `F'/F = -integral d mu(x)/(w - x) = -sum_i k_i/(w - lambda_i)`.
- The Stieltjes transform `integral d mu(x)/(w - x)` determines `mu`, so
  `mu = sum_i k_i delta_(lambda_i)`. Positivity of `mu` gives `k_i >= 0`, and
  the atoms that occur have `k_i >= 1`.

**Step 5: `n = 1`.** The masses are positive integers summing to `1`, so
`mu = delta_lambda`. Then `sigma(T) = {lambda}`, and the faithful regular
representation gives `T = lambda 1`. Also `lambda = tau(T) in Z`.

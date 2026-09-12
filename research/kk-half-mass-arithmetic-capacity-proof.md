---
rg: 2
id: kk-half-mass-arithmetic-capacity-proof
kind: route
title: Twist a Z-Laplacian by an involution and push the ghost congruences through the factor four
target: kk-half-mass-measures-pass-arithmetic-at-every-capacity
requires:
  - torsion-free-integral-zeta-is-an-integer-euler-product
---

Notation: `Y = N + u + u^(-1)` in `Z[Z]` with `N >= 3`, `g` the generator of `Z/2`, and
`T = T_N = 2Yg` in `Z[Z x Z/2]`. Let `tau` be the canonical trace.

**1. Spectrum and masses.** `C*_r(Z x Z/2) = C*_r(Z) ⊗ C*_r(Z/2)`, and
`C*_r(Z/2) ≅ C^2` through `g -> (1, -1)`. So `T` corresponds to `(2Y, -2Y)`, and
`tau = tau_Z ⊗ (1/2)(ev_1 + ev_2)`. The spectrum of `Y` in `C*_r(Z)` is the range
of `N + 2cos(theta)`, i.e. `[N-2, N+2]`. Hence

```text
sigma(T) = [2N-4, 2N+4] ∪ [-2N-4, -2N+4],       mu_T = (mu_(2Y) + mu_(-2Y))/2.
```

For `N >= 3` the pieces are disjoint (`2N-4 > 0`), and each carries mass `1/2`.

**2. Moments.** `g` is central of order two and commutes with `Y`, so
`tau(T^j) = tau((2Y)^j) tau(g^j)`, which equals `tau((2Y)^j)` for even `j` and `0`
for odd `j`. These are integers because `2Y` has integer coefficients.

**3. Zeta integrality.** Write `m_j = tau(T^j)` and `S_n = sum_(d | n) mu(n/d) m_d`.
- If every `c_n = S_n / n` is an integer, then
  `exp(sum_j m_j z^j / j) = prod_n (1 - z^n)^(-c_n)` lies in `Z[[z]]`. Indeed the
  logarithm of the product is `sum_n c_n sum_k z^(nk)/k = sum_j (z^j/j) sum_(n | j) n c_n`,
  and `sum_(n | j) n c_n = m_j` by Möbius inversion.
- So it suffices to show `n | S_n` for every `n`.

- **`n` odd.** Every divisor `d` is odd, so every `m_d = 0` and `S_n = 0`.
- **`n` even, `n = 2 n_1`.** The nonzero terms have `d = 2e` with `e | n_1`, and
  `mu(n/d) = mu(n_1/e)`. With `W = 4Y^2` in `Z[Z]`:

  ```text
  S_n = sum_(e | n_1) mu(n_1/e) tau((2Y)^(2e)) = sum_(e | n_1) mu(n_1/e) tau(W^e).
  ```

  - *Odd part.* `W` is an integral self-adjoint element over the torsion-free group `Z`.
    By `torsion-free-integral-zeta-is-an-integer-euler-product`, its zeta series is an
    integer Euler product, which is equivalent to `n_1 | S_n`. Write `n_1 = 2^b r` with
    `r` odd; then `r | S_n`.
  - *2-adic part.* A term with `mu(n_1/e) != 0` has `n_1/e` squarefree, so
    `v_2(e) >= b - 1` and `e >= 2^(max(b-1,0))`. Its value
    `tau(W^e) = 4^e tau(Y^(2e))` has `v_2 >= 2e`.
    - If `b = 0`, every term is divisible by `4`, so `2 | S_n`.
    - If `b >= 1`, every term has `v_2 >= 2^b >= b + 1`, so `2^(b+1) | S_n`.
  - In both cases `2^(b+1) r = n` divides `S_n`.

So every `c_n` is an integer, and `exp(sum_j m_j z^j/j)` lies in `Z[[z]]`.

**4. Capacity.** By the formula recorded on `integral-spectra-of-small-capacity-are-finite`,
the symmetric set `[-b, -a] ⊔ [a, b]` has capacity `sqrt(b^2 - a^2)/2`. With
`a = 2N - 4` and `b = 2N + 4`, `b^2 - a^2 = 32N`, so the capacity is `sqrt(8N)`. This is
at least `1` for `N >= 1`, and unbounded.

**5. The fence.** Items 1–4 give a gapped measure, with components of mass `1/2`, that
passes integer moments, positivity (it is a spectral measure), integrality of the zeta
Euler product with every ghost congruence, and any prescribed capacity lower bound.
So these properties of `mu_a` cannot imply integer component masses.

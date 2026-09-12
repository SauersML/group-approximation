---
rg: 2
id: integral-small-capacity-finite-spectrum-proof
kind: route
title: Apply Pólya's rationality theorem to the integer Stieltjes series of the spectral measure
target: integral-spectra-of-small-capacity-are-finite
requires:
  - polya-integer-series-rational-off-small-capacity
---

Let `mu` be the spectral measure of `T` for `Tr = sum_i tau(X_ii)`, a positive
measure of total mass `n` with `supp mu = sigma`, and let `m_k = Tr(T^k)`.

**Step 1: integer coefficients.** `T^k` has entries in `Z[i][G]`, and `tau`
reads the identity coefficient, so `m_k in Z[i]`. Since `T` is self-adjoint,
`m_k = integral x^k d mu` is real, hence `m_k in Z`.

**Step 2: continuation.** Put

```text
f(w) = sum_(k >= 0) m_k w^(-k-1) = integral d mu(x) / (w - x).
```

The series converges for `|w| > ||T||`. The integral is holomorphic and
single-valued on the Riemann sphere minus `sigma`, and vanishes at infinity.
No integrality of partial masses is needed: unlike the logarithm in
`torsion-free-small-spread-integer-atomic-proof`, the Stieltjes transform has
no monodromy around a component of `sigma`. So `w f(w)`, an integer power
series in `1/w`, continues to the sphere minus `sigma`.

**Step 3: rationality.** `sigma` is a compact subset of the real line, so its
complement in the sphere is connected, and `cap(sigma) < 1` by hypothesis. By
`polya-integer-series-rational-off-small-capacity`, `f` is rational.

**Step 4: finite spectrum.**
- A positive measure with a rational Stieltjes transform is finitely atomic.
  Stieltjes inversion gives `mu = -(1/pi) lim_(eps -> 0+) Im f(x + i eps) dx`
  weak-*, and a rational `f` with real poles contributes only point masses at
  simple poles, with the residues as masses.
- The trace is faithful on `M_n(C*_r(G))`, so `supp mu = sigma`. Hence `sigma`
  is the finite pole set.
- Fatou's lemma writes `f(1/z) z^(-1)` as `P(z)/Q(z)` with `P, Q in Z[z]` and
  `Q(0) = 1`. So the poles are algebraic integers, and the squarefree
  `m(x) = prod (x - lambda)` over the Galois closure lies in `Z[x]`.
- `m(T)` is self-adjoint with spectrum `m(sigma) = {0}`, so `m(T) = 0`.
  Lagrange interpolation writes each `chi_({lambda})(T)` as a polynomial in `T`.

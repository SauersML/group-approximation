---
rg: 2
id: determinant-moment-certificate-proof
kind: route
title: Squeeze the logarithm between a chord at zero and a polynomial upper bound, then read the bound off the moments
target: determinant-violations-have-finite-moment-certificates
requires: []
---

Let `mu` be the spectral measure of `T = A^* A` with respect to
`Tr = sum_i tau(X_ii)`. It is a positive measure of total mass `n` on
`[0, ||T||]`, contained in `[0, C_T]`, since right multiplication by `g` is a
unitary. By definition, `log det_N(G)(A) = (1/2) integral_(0, C_T] log x d mu`.
Put `L = integral_(0, C_T] log x d mu`, which may be `-infinity`. Moments are
integers because `T` has integer coefficients.

**Certificates give violations.** Given `(N, P, k)` with (i)--(iii):

```text
L <= integral_(0,C_T] P d mu <= integral_[0,C_T] P d mu = sum_j p_j m_j < 0.
```

- The first step uses (i).
- The second step uses (ii): `P(0) mu({0}) >= 0`.
- The equality holds because `mu` is supported in `[0, C_T]`.

So `det_N(G)(A) < 1`.

**Violations give certificates.** Assume `L < 0`.

- **Choosing `eta`.** Pick `eta in (0, min(1, C_T))` with
  `integral_(0,eta) |log x| d mu < |L|/4` when `L` is finite. When
  `L = -infinity`, pick `eta` with `integral_[eta, C_T] log x d mu < -1` instead.
- **A continuous upper bound.** Define `f` on `[0, C_T]` by `f(x) = log x` for
  `x >= eta`, and `f(x) = (x/eta) log eta` for `0 <= x <= eta`.
  - The function `g(x) = (x/eta) log eta - log x` satisfies `g(eta) = 0` and
    `g'(x) = (log eta)/eta - 1/x < 0` on `(0, eta)`, so `g >= 0` there.
  - Hence `f >= log x` on `(0, C_T]`, `f(0) = 0`, and `f` is continuous.
- **Its integral is negative.** Since `log eta < 0`, the part on `(0, eta)`
  contributes at most `0`, so
  `integral f d mu <= integral_[eta,C_T] log x d mu`.
  - Finite case: the right side equals
    `L + integral_(0,eta) |log x| d mu < (3/4) L < 0`.
  - `L = -infinity`: the right side is below `-1`.
  - Either way, `integral f d mu <= -c` for some `c > 0`.
- **Polynomial approximation.** By Weierstrass choose a real polynomial `P_0`
  with `|P_0 - f| < eps` on `[0, C_T]`, where `eps = c/(4n)`. Round its
  coefficients to rationals, changing it by less than `eps` on `[0, C_T]`, and
  add `2 eps`. The result `P` satisfies:
  - `P >= f + eps >= log x + eps` on `(0, C_T]`, which is (i) with `1/k <= eps`;
  - `P(0) >= f(0) = 0`, which is (ii);
  - `integral P d mu <= integral f d mu + 3 eps n < 0`. Since `mu` is supported
    in `[0, C_T]`, `integral P d mu = sum_j p_j m_j`, which is (iii).

**Deciding (i).** Let `M` bound `|P'|` on `[0, C_T]`.

- Choose rational `x_0 in (0,1)` with `-M x_0 >= log x_0 + 1/k`, possible
  because `log x_0 -> -infinity`. On `(0, x_0]`,
  `P(x) >= P(0) - M x_0 >= -M x_0 >= log x_0 + 1/k >= log x + 1/k`.
- On `[x_0, C_T]`, both `P` and `log` are Lipschitz, with constants `M` and
  `1/x_0`. Checking the strict inequality at the points of a fine rational grid
  with an explicit slack decides it: accept when every grid value clears the
  slack. A certificate built as above has margin `eps`, so it is accepted at a
  fine enough grid.

**Transfer.** For `B` over `H` with the same first `N` moments and
`||B^* B|| <= C_T`, the first half of the argument applies verbatim with
`mu_(B^* B)`.

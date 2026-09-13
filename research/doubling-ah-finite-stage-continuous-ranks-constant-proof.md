---
rg: 2
id: doubling-ah-finite-stage-continuous-ranks-constant-proof
kind: route
title: Branch traces with constant contamination turn finite-stage ranks into step functions plus a constant
target: doubling-ah-finite-stage-continuous-ranks-are-constant
requires: [all-ranks-occur-iff-continuous-ranks-are-dense]
---

Notation as in the target. `psi_i` is the dual map `T(A_(i+1)) -> T(A_i)`,
`psi_i(mu) = integral P_i(y) d mu(y)`, and `Psi_(M,K) = psi_M o ... o psi_(K-1)`.
For `a in M_k(A_M)_+` and a trace with stage-`M` measure `mu_M`,
`d_tau(a) = integral rank(a(z)) / r_M d mu_M(z)`.

**Step 1: branch traces.** Fix `M` and `y in X_M`. Put `y_M = y` and
`y_(K+1) = d_K(y_K)`. By the diagonal property,
`psi_K(delta_(y_(K+1))) = alpha_K delta_(y_K) + (1 - alpha_K) nu_K`. Induction
on `K`, using linearity and mass preservation of the `psi`, gives for `L >= M`

```text
Psi_(L,K+1)(delta_(y_(K+1)))
  = (prod_(s=L..K) alpha_s) delta_(y_L)
    + sum_(s=L..K) (prod_(t=s+1..K) alpha_t)(1 - alpha_s) Psi_(L,s)(nu_s).
```

As `K -> infinity` this converges in total variation, because the tail
`sum (1 - alpha_s)` is finite, to

```text
mu_L^y = beta_L delta_(y_L) + kappa_L,    beta_L = prod_(s >= L) alpha_s,
kappa_L = sum_(s >= L) (prod_(t > s) alpha_t)(1 - alpha_s) Psi_(L,s)(nu_s).
```

The limits are compatible under `psi`, so they define a trace `sigma_y` on `A`;
below stage `M` use `Psi_(L,M)(mu_M^y)`. **`kappa_L` does not depend on `y`.**
This is the constant-contamination version of Lemma 2 in
`research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md`.

**Step 2: continuity of `y -> sigma_y`.** For `b in A_L` with `L >= M`,
`sigma_y(b) = beta_L tr_(y_L)(b) + integral tr_z(b) d kappa_L(z)`. Here
`y_L = d_(L-1) o ... o d_M (y)` is continuous in `y` and `z -> tr_z(b)` is
continuous, so `y -> sigma_y(b)` is continuous. For `L < M`, push `b` forward
to stage `M`. The union of the `A_L` is dense and traces are contractive, so
`y -> sigma_y` is weak* continuous from `X_M` into `T(A)`.

**Step 3: the finite-stage case.** Let `a in M_k(A_N)_+` and choose `M >= N`
with `beta_M > 0`. Let `a'` be the image of `a` in `M_k(A_M)` and
`R(y) = rank a'(y)`, a lower semicontinuous integer-valued function on `X_M`.
By Step 1, for `y in X_M`

```text
d_(sigma_y)(a) = beta_M R(y) / r_M + c,     c = integral R / r_M d kappa_M,
```

and `c` does not depend on `y`. If `d(a)` is continuous on `T(A)`, Step 2 makes
`y -> d_(sigma_y)(a)` continuous. So `R` is continuous and integer-valued, hence
constant on the connected `X_M`. Then every trace `tau`, whose stage-`M` measure
is a probability measure, gives `d_tau(a) = R / r_M`. So `d(a)` is constant.

**Step 4: orthogonal sums.** Let `a` be a countable orthogonal sum of
finite-stage elements `a_j`, with `d(a)` finite and continuous. By the summand
statement proved in `all-ranks-occur-iff-continuous-ranks-are-dense-proof`,
each `d(a_j)` is continuous. By Step 3 each is a constant `c_j`, and
`d(a) = sum_j c_j` is constant. Square.

**What is not claimed.** A general positive element of `A tensor K` is the
supremum in `Cu(A)` of a Cuntz-increasing sequence of finite-stage elements. Its
increments need not be orthogonal summands, and nothing here constrains such
suprema. Along a single branch family a supremum of increasing step functions can
be continuous and non-constant.

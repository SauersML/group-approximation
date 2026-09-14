---
rg: 2
id: random-exponential-pairing-unlearnability-proof
kind: route
title: Bound the posterior by A^n over an independent partition function and split off low-density pullbacks
target: random-exponential-pairing-families-are-unlearnable
requires: []
artifacts:
  - research/artifacts/unique-games-smooth-design-learnability-2026-09-11.md
---

The likelihood ratio of `x` under `P` is
`L_P(x) = prod_({i,j} in P)(1 + rho^2 psi(x_i,x_j))`, with
`psi(s,t) = m 1(s=t) - 1`. Hence `L_P <= A^n`. The posterior mass of a length-`L`
list is at most `L A^n / Z'`, where `Z'` sums `L_(P_j)(x)` over the unplanted
indices.

Given `(i_0, P_(i_0), x)`, `Z'` is a sum of `M-1` independent copies of
`L_P(x)` with `P` uniform. Their mean is `mu(x) = m^(2n) nu(x)`, and
`E[L_P^2] <= A^n mu(x)`. By Chebyshev's inequality,
`Pr[Z' < (M-1) mu/2] <= 4 A^n / ((M-1) mu)`. Together,

```text
Pr[success | x] <= min(1, (2L+4) A^n / ((M-1) mu(x))).
```

`x` has law `nu`, and `{x : nu(x) < tau m^(-2n)}` has `nu`-mass at most `tau`.
Hence `E[success] <= tau + (2L+4) A^n / ((M-1) tau)`. Optimizing `tau` gives the
bound.

For `D o Q`, apply the same argument to the planted conjugates
`sigma_0(P_j)`. Full detail is in the artifact, Section 3. The proof is
mathematical, with no proof-assistant verification.

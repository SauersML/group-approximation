---
rg: 2
id: single-selected-atom-escape-compiler-proof
kind: route
title: Join the escaped atom to the current hull and iterate its trace growth
target: single-selected-atom-escape-compiler
requires:
  - maximal-forbidden-atom-has-a-named-positive-half
  - finite-pauli-seed-reducing-quarter-carrier
artifacts:
  - research/artifacts/finite-adaptive-hs-escape-audit-2026-08-24.md
---

The finite-seed correction proves that the Pauli carrier is genuinely
reducing before contextual soundness is applied; it does not assume that an
arbitrary almost-central seed matrix is close to the contextual commutant.
The exact Pauli trace flip then proves `(SEC3)`, with the stated fixed
perturbation loss. The projection identity in `(SEC4)`, `(SAE1)`, and
`(MFA2)` give `(SEC5)`.  For fixed marked separation `delta>0`, choose `N`
with

```text
(1+gamma)^N delta^2/8>1.
```

The finite geometric sum of the `O(sqrt(E))` losses is independent of matrix
dimension, so sufficiently small `E` is impossible.  Hyperlinearity would
give arbitrarily accurate canonical microstates keeping the nontrivial
central involution separated, yielding the contradiction.  The exact
tracial extension witnesses that `J` is nontrivial in the abstract group.

For canonical microstates one can use the sharper unhalved atom `(MFA1)` and
the marked-sector capacity directly. Writing `lambda=1+eta beta/M`, an
effective depth is

```text
N=floor(log(2)/log(lambda))+1.
```

The accumulated escape error is

```text
(C_E+eta C_B/M)(lambda^N-1)/(lambda-1) sqrt(E),
```

plus the fixed initial correction cost.


---
rg: 2
id: sl3-fold-positive-cross-gram-firewall-proof
kind: route
title: Compute the polar Gram tautology and its free-dihedral sharpness tower
target: sl3-fold-positive-cross-gram-does-not-select-endpoint
requires:
  - positive-cross-gram-state-rounds-to-common-pvm
  - sl3-projective-transfer-is-balanced-projection-endpoint-transfer
  - arithmetic-double-swap-extension-is-binary-coset-wreath
artifacts:
  - research/artifacts/sl3-fold-positive-cross-gram-firewall-2026-08-23.md
---

For `G=PQ`, projection multiplication gives `(FPG1)` directly, and
traciality gives `||G||_2^2=tr(QPQ)=tr(PQ)`.  In the balanced swap chart,
the identity `tr((I-2P)(I-2Q))=4tr(PQ)-1` converts the canonical fold trace
zero into `(FPG2)`.  The endpoint-distance identities in the required claim
then give the displayed distance.  This proves that the positive-Gram PVM
rounding hypothesis holds perfectly while endpoint transfer fails at the
level of the controlled data.

For `H=QPQ`, cyclicity and `P^2=P,Q^2=Q` give

```text
tr(H-H^2)=tr(PQ)-tr(PQPQ)=(1/2)||PQ-QP||_2^2.
```

If `R=1_[1-epsilon,1](H)`, then `R<=Q`.  On `I-R`, scalar functional
calculus gives `H<=epsilon^(-1)H(I-H)`, while `HR<=R`; hence

```text
m=tr(HR)+tr(H(I-R))<=tr(R)+d/epsilon.
```

Compressing `(P-Q)^2` by `R<=Q` gives

```text
R(P-Q)^2R=R-RPR=R(I-H)R,
```

which proves `(FPG4)`.

Finally `C_2*Z` is virtually free and residually finite.  Taking one finite
quotient separating each increasing word ball and its left regular
representation produces an exact finite-dimensional canonical local tower.
Normal form shows that `s` and `hsh^(-1)` generate `C_2*C_2`; equivalently,
their trace-half spectral projections are free.  In the `Q`-corner the
standard free-projection calculation gives the arcsine law on `[0,1]`, and
`QPQ` vanishes on `I-Q`, proving `(FPG5)`.  The arcsine first and second
moments are `1/2` and `3/8`, while its upper tail at `1-epsilon` is
`(2/pi)arcsin(sqrt(epsilon))`; multiplying by `tr(Q)=1/2` proves `(FPG6)`.
Weak convergence on the compact interval also implies uniformly that the
top mass tends to zero for every moving `epsilon_n->0`, because the limiting
measure has no atom at `1`.

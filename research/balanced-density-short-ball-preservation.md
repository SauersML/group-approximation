---
rg: 2
id: balanced-density-short-ball-preservation
kind: claim
title: Balanced positive-density relators preserve a linear free ball above the C'(1/6) cubulation threshold
distinct_from:
  cprime-one-sixth-presentations-are-hyperlinear: that is the proved dead zone below the classical cubulation threshold; this asks for a weaker macroscopic-isoperimetric preservation event at density strictly above 1/6.
  unitary-word-return-entropy-summability: that also needs all-dimensional unitary anti-concentration; this claim is only the group-theoretic preservation half.
artifacts:
  - research/artifacts/random-relator-density-repair-2026-08-18.md
---

For some fixed `k>=2` and density

```text
1/6 < d < 1/2,
```

there are `c>0` and infinitely many admissible lengths `L` such that the
following balanced density model has positive probability (ideally probability
`1-o(1)`) of preserving the free ball of radius `cL`.

Let `C_L^0` be the cyclically reduced length-`L` words in `F_k` whose
abelianization is zero, sample

```text
m_L = floor((2k-1)^(d L))
```

relators from `C_L^0`, and put `G_L=F_k/<<R_L>>`.  Then the quotient map
`F_k -> G_L` is injective on `B_(cL)`.

A stronger acceptable conclusion is a linear van Kampen isoperimetric
inequality with constant bounded away from zero as `L` grows.

## Attempts

- **Conditioned Ollivier counting.**  Rivin's abelianization asymptotics show
  that `C_L^0` has the same exponential growth rate as the full cyclic word
  sphere.  Prove the prefix/local-overlap estimates used in density-model
  diagram counting survive the zero-abelianization conditioning up to
  polynomial factors, then rerun the sharp `d<1/2` isoperimetric argument.
- **Prefix-heavy transfer.**  For a fixed prefix, balance asks the remaining
  nonbacktracking suffix to hit one prescribed lattice displacement.  A local
  limit theorem should make the conditional prefix probability differ from
  the unconditioned one only subexponentially whenever a positive fraction of
  the word remains.  This is exactly the scale at which density exponents are
  decided.
- **Do not strengthen to classical C'(1/6).**  That would make the resulting
  group hyperlinear by `cprime-one-sixth-presentations-are-hyperlinear` and
  therefore destroy the route.  The desired theorem is macroscopic
  preservation, not a virtual-specialness certificate.

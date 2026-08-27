---
rg: 2
id: unamplified-iwahori-sheets-have-two-thirds-defect
kind: claim
title: Unamplified index-three Iwahori sheets have parabolic gluing defect exactly two thirds
distinct_from:
  iwahori-question-as-square-root-of-parabolic: that gives the full amalgam presentation and identifies the half-parabolic; this computes the exact permutation defect of the most naive three-sheet random-lift block.
  parabolic-spectrum-is-doubling-invariant: that is a unitary spectral constraint in arbitrary dimension; this is the elementary support calculation in the three-point coset permutation representation.
artifacts:
  - research/artifacts/dyadic-iwahori-random-lift-audit-2026-08-21.md
---

Let `C=PSL_2(Z)=<x,y | x^2=y^3=1>`, let `B=Gamma_0(2)/{+-I}`,
and write `T=xy`.  In the natural action of `C` on the three left cosets
`C/B`, the image of `T` is a transposition.  Under the second edge embedding
in the dyadic amalgam, the same abstract element is sent to `(x'y')^2`; its
action on the three cosets of the second Iwahori subgroup is the identity.

Consequently, for every `N>=1` and every bijection between `N` disjoint
copies of the two three-sheet sets, the normalized Hamming distance between
the conjugated first parabolic and the second parabolic is exactly

```text
2/3.
```

Thus a random lift which merely matches unamplified index-three sheets can
never make even the parabolic edge relation asymptotically multiplicative.
Any successful lift must add an internal amplification on which the
parabolic cycle structure absorbs the squaring mismatch.


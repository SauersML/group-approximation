---
rg: 2
id: sl4z-is-not-matricially-stable
kind: claim
title: SL_4(Z) is not point-norm matricially stable
distinct_from:
  sl4z-matricially-stable: that asserts point-norm matricial stability of SL_4(Z); this is its negation, isolated so that the two routes through the block-swap involution centralizer can target it.
  laurent-sl4-not-matricially-stable-for-q-at-least-4: that is the same negation for SL_4(F_q[t^±1]) with q >= 4, via a diagonal torsion element with nonreal eigenvalues; for SL_4(Z) all torsion eigenvalue sectors used here are real, and the class is confined to the -1 eigenspace of the center instead.
---

**OPEN.** Some asymptotic homomorphism `φ_n : SL_4(Z) → U(k_n)` (operator norm, pointwise)
is not pointwise close to any sequence of genuine representations `π_n : SL_4(Z) → U(k_n)`.

## Routes

- `sl4z-instability-from-delocalized-dadarlat`: conditional on the general statement
  `weak-matricial-stability-kills-centralizer-even-cohomology`, using the nonzero class of
  `sl4z-involution-centralizers-have-rational-h2`.
- `sl4z-instability-from-odd-sector-bott`: conditional on the explicit realization
  `sl4z-odd-central-sector-bott-is-realizable`, using the invariant of
  `sl4z-delocalized-bott-lives-in-odd-central-sector`.

The two prerequisites can fail independently. The first is a theorem about all linear
groups. The second is a construction for one group, and part 6 of
`sl4z-delocalized-bott-lives-in-odd-central-sector` shows it holds on the normalizer of `F`.

## What a witness must look like

By `sl4z-delocalized-bott-lives-in-odd-central-sector`, any witness detected by the
block-swap torus satisfies all of the following:
- it has `φ_n(−I) ≈ −1` on a nonzero part;
- it carries opposite Bott indices on the two eigenspaces of `φ_n(g)` there;
- it is not a direct sum of genuine representations with a model induced from a normal
  finite-index subgroup avoiding `g`.

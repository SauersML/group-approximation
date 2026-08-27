---
rg: 2
id: mf-nonhyperlinear-collapse-structure
kind: claim
title: Structure forced on a counterexample to MF implies hyperlinear
distinct_from:
  mf-implies-hyperlinear: That root asks whether a counterexample exists; this claim describes what one would have to look like.
  mf-hyperlinear-radical-divergence: That established claim exhibits an MF-invisible word which is tracially visible, i.e. the inclusion in the opposite direction; this one constrains the hyperlinear residual of a group whose MF residual is trivial.
artifacts:
  - GroupApproximation/Sofic/RadicalSeparation.lean
---

For a countable group `G`, `hyperlinearResidual G` is exactly the set of
elements which are not tracially visible; consequently

```text
G is hyperlinear  <=>  hyperlinearResidual G = 1,
```

both directions, not only the direction already formalized.

If in addition `G` is MF and not hyperlinear, then `R = hyperlinearResidual G`
satisfies:

1. `R != 1` and `G/R` is hyperlinear;
2. `R` contains no nontrivial finite normal subgroup of `G`; in particular
   `R` is infinite and `G` has no nontrivial finite normal subgroup with
   hyperlinear quotient.

So the torsion-critical architecture that produces non-MF groups --- a finite
central mark killed by every model --- is provably unavailable for
nonhyperlinearity of an MF group.

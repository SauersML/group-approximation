---
rg: 2
id: binary-leavitt-row-dual-ergodic-measure-classification
kind: claim
title: Classify the invariant ergodic measures on the binary Leavitt row dual
distinct_from:
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that proves every nontrivial character point has an infinite orbit and hence classifies only the atomic ergodic measures; this asks for the diffuse invariant measures as well.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that excludes one specific invariant measure using the MF origin and all ambient Steinberg relations; this is the stronger abstract dynamical classification and is not needed by the endpoint route.
---

**OPEN.**  Let `R=L_(F_2)(1,2)`, let the first-row root module be

```text
N={x_(1 bullet)(v):v in R^(n-1)},
```

and let `H=St_(n-1)(R)` act on `M=hat N=(R^*)^(n-1)` by the dual elementary
shears.  Classify the `H`-invariant ergodic Borel probability measures on
`M`.

The expected algebraic candidates include the trivial point mass and Haar
measures, or ergodic components of Haar measures, on annihilators of
`H`-invariant submodules such as those arising from right ideals of `R`.
The statement is intentionally a classification problem rather than the
false oversimplification "only the trivial point mass and full Haar": proper
nonzero ideals already provide proper invariant closed subgroups.

The established finite-orbit argument dualizes from the last-column module
and shows only that the trivial point mass is the sole atomic ergodic
measure.  It gives no diffuse classification.  Even a full solution here
would still have to be combined with ambient-character constraints to rule
out the full Haar profile.

## Attempts

The shear-orbit argument disposes of atoms but has no control on diffuse
mass.  The ideal-annihilator ansatz produces many invariant closed subgroups
and therefore cannot prove a Dirac/full-Haar dichotomy.  The next attack must
classify ergodic components inside those systems or use additional ambient
root-position symmetry.

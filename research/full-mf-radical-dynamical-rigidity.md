---
rg: 2
id: full-mf-radical-dynamical-rigidity
kind: claim
title: Full MF radical forces projective, compact, and finite-dimensional dynamical rigidity
distinct_from:
  universal-mf-quotient: that theorem identifies the universal MF-visible group quotient; this theorem translates total invisibility into concrete representation-theoretic and ergodic consequences.
  map-matricial-stability-non-mf: that result assumes minimal almost periodicity and stability to deduce non-MF; this theorem starts from full MF radical and derives minimal almost periodicity together with stronger projective and dynamical conclusions.
artifacts:
  - research/full-mf-radical-dynamical-rigidity-proof.md
---

Let `G` be a countable group with `Rad_MF(G)=G`.  Then:

1. every finite-dimensional linear representation of `G` over `C` is
   trivial;
2. every finite-dimensional projective unitary action
   `G -> PU(n)` is trivial;
3. every homomorphism from `G` to a compact Hausdorff group is trivial, so
   the Bohr compactification of `G` is a point;
4. `G` has no proper finite-index subgroup;
5. every ergodic probability-measure-preserving action of `G` is weakly
   mixing.

If `G` also has property `(T)`, every ergodic probability-measure-preserving
action is simultaneously weakly mixing and strongly ergodic.  Equivalently,
its Koopman representation on `L^2_0` has no finite-dimensional submodule and
has a spectral gap.

For the Hilbert-hotel group

```text
H = EL_16(L_(F_2)(1,2)),
```

all conclusions hold.  Thus every ergodic pmp action of `H` lies at once on
the two rigid sides of the unitary spectrum: it has no compact component and
it has a Kazhdan gap.


---
rg: 2
id: properly-infinite-multiplier-solves-lxxiii
kind: claim
title: A properly infinite multiplier unit gives the global square-zero cover property
artifacts:
  - research/artifacts/problem-lxxiii-literature-audit-2026-08-30.md
distinct_from:
  finite-packets-fuse-after-one-stabilization: that constructs the fused nilpotent in M_2(A); this theorem returns it to A while preserving the ideal of the original cutdown by using multiplier isometries.
  chain-ideal-lattice-solves-lxxiii: that selects one member of a finite packet from comparability of ideals; this makes no ideal-lattice assumption and instead destabilizes the whole packet.
---

Let `A` be a C*-algebra with no nonzero finite-dimensional representations.
Suppose that the unit of `M(A)` is properly infinite.  Then, for every
`a in A_+` and every `epsilon>0`, there is `x in A` such that

```text
x^2=0,
(a-epsilon)_+ in Ideal_A(x).
```

The representation hypothesis is actually automatic here: a nonzero
finite-dimensional representation extends nondegenerately to `M(A)` after
cutting down to its support, but a properly infinite unit cannot map to a
nonzero finite-dimensional unit.

In particular the conclusion holds for every stable C*-algebra and for
every unital C*-algebra whose unit is properly infinite.  The point is
stronger than abstract invariance under `M_2`-stabilization: the corner
embedding can be chosen so that the original cutdown, not merely an image
of it under an uncontrolled stable isomorphism, remains in the generated
ideal.

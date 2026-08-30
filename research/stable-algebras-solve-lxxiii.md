---
rg: 2
id: stable-algebras-solve-lxxiii
kind: claim
title: Stable C*-algebras have the global square-zero cover property
artifacts:
  - research/artifacts/problem-lxxiii-literature-audit-2026-08-30.md
distinct_from:
  finite-packets-fuse-after-one-stabilization: that constructs the fused nilpotent in M_2(A); this theorem returns it to A while preserving the ideal of the original cutdown by using multiplier isometries.
  chain-ideal-lattice-solves-lxxiii: that selects one member of a finite packet from comparability of ideals; this makes no ideal-lattice assumption and instead destabilizes the whole packet.
---

Let `A` be a stable C*-algebra with no nonzero finite-dimensional
representations.  For every `a in A_+` and every `epsilon>0`, there is
`x in A` such that

```text
x^2=0,
(a-epsilon)_+ in Ideal_A(x).
```

Thus every stable algebra in the scope of Problem LXXIII satisfies its
conclusion.  In fact the representation hypothesis is automatic for stable
C*-algebras, since quotients of stable algebras are stable and no nonzero
finite-dimensional C*-algebra is stable.

The point is stronger than abstract invariance under `M_2`-stabilization:
the destabilization can be chosen so that the original cutdown, not merely
an image of it under an uncontrolled stable isomorphism, remains in the
generated ideal.

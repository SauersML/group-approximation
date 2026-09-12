---
rg: 2
id: binary-leavitt-root-doubling-k0-retains-xor-overlap
kind: claim
title: Root-reflection doubling retains an intersection term in K-zero
distinct_from:
  affine-active-doubling-is-elementary-matrix-conjugacy: that constructs the exact word carrying one active coefficient placement to two diagonal placements; this computes what that word says about spectral projections in an arbitrary unitary representation.
  odd-leavitt-reflections-retain-stationary-xor-overlap: that gives an S4 regular countermodel for a connector and canonical trace; this isolates the ordered K-zero identity and supplies a four-dimensional matrix-corona realization.
  corona-projective-hilbert-hotel-cancellation: that collapses a literal equivalence P isomorphic to P direct-sum P; this proves that root-reflection conjugacy gives only an XOR relation and not that literal equivalence.
artifacts:
  - research/binary-leavitt-root-doubling-k0-xor-proof.md
---

Let `Q` be a unital C-star algebra, let `u_0,u_1` be commuting
self-adjoint involutions, and put

```text
p_i=(1-u_i)/2,                 p_xor=(1-u_0u_1)/2.       (KXO1)
```

Then the three projections commute and

```text
p_xor=p_0(1-p_1)+(1-p_0)p_1.                             (KXO2)
```

Consequently, in ordered `K_0(Q)`,

```text
[p_xor]=[p_0]+[p_1]-2[p_0p_1].                           (KXO3)
```

If group-word conjugacies make `p_0`, `p_1`, and `p_xor` Murray--von
Neumann equivalent, with common class `b`, then the resulting equation is

```text
b=2c,                         c=[p_0p_1],                 (KXO4)
```

not `b=2b`.  Thus the active one-to-two elementary conjugacy does not by
itself produce a properly infinite marked projection.  It would do so only
after an additional, independently authenticated support statement killing
the overlap `p_0p_1` and identifying an orthogonal union on the same source
corner.

This distinction is already exact in a norm matrix corona.  Constant
commuting diagonal projections in `M_4(C)` can have

```text
rank(p_0)=rank(p_1)=rank(p_xor)=2,       rank(p_0p_1)=1. (KXO5)
```

All three projections are unitarily equivalent, every relation
`(KXO1)--(KXO4)` holds, and their common class is nonzero.  Hence neither
projection-monoid cancellation nor the large `K_0` of a matrix corona can
erase the XOR overlap which the root words forget.


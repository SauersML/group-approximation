---
rg: 2
id: sequential-marginal-holonomy-is-conditional-rank-matching
kind: claim
title: Sequentially freezing marginals is exactly conditional rank matching
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for all cross-context marginal identities in one corner; this gives the local block-unitary criterion for installing one more marginal while preserving those already fixed.
  piecewise-group-transport-gives-corner-unitaries: that constructs a corner unitary from already named source and range partitions; this characterizes when a block-diagonal choice can additionally conjugate one prescribed involution to another.
---

Let `d_1,...,d_r,y,z` be self-adjoint involutions in `M_D(C)`.  Assume the
`d_i` commute, and that both `y` and `z` commute with every `d_i`.  For
`omega in {+1,-1}^r`, put

```text
e_omega=product_i (1+omega_i d_i)/2.                    (CMH1)
```

There is a unitary `U` such that

```text
[U,d_i]=0 for every i,              U y U^*=z            (CMH2)
```

if and only if, for every `omega`,

```text
rank(e_omega(1+y)/2)=rank(e_omega(1+z)/2),
rank(e_omega(1-y)/2)=rank(e_omega(1-z)/2).               (CMH3)
```

Equivalently, after some marginals have been frozen, the next marginal can
be installed by a block unitary exactly when its two conditional ranks agree
inside every joint atom of the frozen marginals.  Equality of the
unconditional `+/-` ranks is only the `r=0` case and is not enough for a
second step.

For a diagonal context PVM indexed by allowed assignments, the nonzero
`e_omega` are the sums of assignment atoms having the same values on the
already frozen variables.  Thus `(CMH3)` is equality of the complete
conditional counting tables, not merely equality of one-variable marginals.
Once the frozen variables separate the allowed assignments, the blocks
`e_omega` are the context atoms themselves and every further unitary
commuting with them fixes the entire context diagonal algebra.

The criterion persists in any finite algebraic matrix corner
`q C[K] q isomorphic to M_D(C)`.  Properly infinite amplification can erase
finite rank mismatches in one chosen exact witness representation, but no
finite-matrix decoder may silently replace `(CMH3)` by unconditional balance.
This is the exact local obstruction to composing the independent
one-marginal signed-Hecke escape cells.

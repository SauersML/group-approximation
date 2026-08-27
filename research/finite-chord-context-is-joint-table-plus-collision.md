---
rg: 2
id: finite-chord-context-is-joint-table-plus-collision
kind: claim
title: Any finite family of escape chords on one context is exactly joint-table matching plus a residual collision
distinct_from:
  sequential-marginal-holonomy-is-conditional-rank-matching: that installs one new marginal conditional on already frozen signs; this gives the simultaneous finite-family criterion and exhibits the full correlation data missed by separate feasibility.
  feasible-chord-collision-has-free-phase-block-escape: that closes one feasible chord and escapes through one residual collision; this constructs one common conjugation and one free-phase escape for any fixed finite family of chord marginals on the same context partition.
  simultaneous-block-escaping-context-holonomy: that also requires globally compatible choices of target signs at every context; this completely classifies the local problem only after one context's target tuple has been fixed.
---

**ESTABLISHED FINITE-FAMILY CLASSIFICATION.**  Let
`d_1,...,d_r,x_1,...,x_m` be commuting selfadjoint involutions in `M_D(C)`.
The `d_i` are previously frozen context marginals and the `x_j` are the
finitely many chord marginals incident to one context.  Let `z_1,...,z_m`
be proposed target signs commuting with every `d_i`.

There is one unitary `U` satisfying

```text
[U,d_i]=0,                 U x_j U*=z_j  for every j       (FCC1)
```

if and only if the `z_j` commute pairwise and, for every frozen sign pattern
`omega` and every `epsilon in {+1,-1}^m`,

```text
rank(e_omega product_j p_(epsilon_j)(x_j))
 =rank(e_omega product_j p_(epsilon_j)(z_j)),              (FCC2)
```

where

```text
e_omega=product_i (1+omega_i d_i)/2,
p_epsilon(t)=(1+epsilon t)/2.
```

Thus separate feasibility of all chords is not enough: it remembers only
one-sign marginals of `(FCC2)` and can miss their joint correlations.  For
example, in `M_2(C)`, the source pair `(Z,Z)` and target pair `(Z,-Z)` have
the same positive and negative ranks coordinatewise but disjoint joint
support tables, so no common conjugation exists.

Let `(P_a)_(a in R)` be the context assignment partition and assume `(FCC2)`.
After regauging it by `U`, if two distinct supported assignments have nonzero
coordinate lines with the same joint character under

```text
d_1,...,d_r,z_1,...,z_m,                                  (FCC3)
```

then one Hadamard rotation in that common fiber followed by independent free
phases gives a finite-support corner unitary `V` commuting with every sign in
`(FCC3)`.  The single final context unitary `VU` installs all `m` chord
marginals, preserves every prior overlap, and moves both collided assignment
projections outside the finite root block.

Conversely, if `(FCC3)` separates all supported assignments, every common
endpoint conjugation preserving all chords and old overlaps fixes the entire
context partition.  Hence, **for a fixed proposed target tuple**, full joint
rank matching and a residual joint-character collision exactly characterize
this common-conjugation/free-phase escape.

This does not choose the target tuples simultaneously around a global cycle.
The surviving signed-Hecke problem is therefore the global constraint problem
of selecting target tuples whose full conditional tables agree at every
context, or escaping a collision-free context by a non-conjugation additive
operation—not a new local compatibility obstruction at higher finite valence.


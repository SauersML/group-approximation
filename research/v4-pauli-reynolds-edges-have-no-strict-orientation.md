---
rg: 2
id: v4-pauli-reynolds-edges-have-no-strict-orientation
kind: claim
title: Pauli half and joint-atom Reynolds edges inside one V4 have no strict HNN orientation
distinct_from:
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: that gives the general one-sided subgroup-Reynolds estimate and leaves open payload-coupled surrogate subgroups; this exhausts the native line and whole-group subgroups of the relative Pauli V4.
  v4-five-fourths-surplus-is-the-nonlinear-quarter: that shows the scalar five-fourths excess is carried by one joint atom; this shows that treating that atom and the Pauli halves as subgroup Reynolds projections cannot orient the excess.
  paired-frame-forbidden-scalar-overlap-gap: that detects the forbidden atom locally and leaves a reverse reservoir; this proves that a native V4 HNN edge cannot eliminate that reservoir.
---

Let `V=<r,s> congruent C_2^2`.  Its named Pauli half projections and joint
atoms are exactly

```text
e_<r>=(1+r)/2,       e_<s>=(1+s)/2,
e_V=(1+r)(1+s)/4,                                    (VRE1)
```

up to replacing a line by the third line or changing signs by a character.
Consider a subgroup-Hecke HNN actuator made only from subgroups `K,H<=V` and
an injection `phi:K->H`, with source `p=e_H` and target `q=e_K` as in
`(SHA2)--(SHA5)`.  The same conclusion holds for charged Reynolds idempotents,
provided the source character restricts along `phi` to the target character,
as covariance requires.  Then it has no strict native Pauli orientation:

1. if `|H|>|K|`, necessarily `( |H|,|K| )` is `(4,2)`, `(4,1)`, or
   `(2,1)`.  In the only joint-atom case the `H`-character eigenspace is
   contained in its restriction's `K`-character eigenspace, so the useful
   comparison is pointwise `e_(H,chi)<=e_(K,chi|K)`; the edge sees the harmless
   direction;
2. if `|H|=|K|=2`, both Reynolds projections are Pauli halves.  Conjugacy
   equates their total finite-dimensional ranks.  On the four `V` characters,
   the positive difference on one joint atom is paired with an equal negative
   difference on the opposite atom.  This is exactly the `101 <-> 011`
   reverse-reservoir exchange;
3. the remaining equal-order cases give identical whole or trivial Reynolds
   projections.

Therefore adjoining the established `S_3` affine automorphisms merely permutes
the three lines and the four atoms.  It does not create a one-sided source and
target pair: a strict quarter requires either a subgroup outside this native
`V_4` with payload-coupled fixed-space behavior, or a genuinely
finite-dimensional global capacity theorem preventing the reverse atom from
returning.  Literal relative-Pauli support reflections cannot supply the
missing actuator.

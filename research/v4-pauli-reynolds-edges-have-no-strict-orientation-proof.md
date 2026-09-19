---
rg: 2
id: v4-pauli-reynolds-edges-have-no-strict-orientation-proof
kind: route
title: Enumerate the subgroup lattice and character ranks of V4
target: v4-pauli-reynolds-edges-have-no-strict-orientation
requires:
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
  - v4-five-fourths-surplus-is-the-nonlinear-quarter
---

The subgroup lattice of `V=C_2^2` consists of the trivial subgroup, three
lines, and `V`.  Averaging a line gives its positive Pauli half, while
averaging `V` gives the joint positive atom `(VRE1)`.

For an injective HNN edge `K->H`, subgroup order cannot decrease.  The only
strict step involving the joint atom is a line (or the trivial subgroup) into
`V`; an `H`-character eigenspace is contained in the corresponding restricted
`K`-character eigenspace, so `tau(e_(H,chi))-tau(e_(K,chi|K))<=0` in every
representation.  A line-to-line edge has equal
orders.  Evaluating its two half projections on the four characters gives
values in `{0,1}` with two `+1` and two `-1` differences; hence every positive
atom has an opposite negative companion and total rank is conserved.  All
other cases are trivial.  Automorphisms from the affine `S_3` normalizer only
permute this enumeration.

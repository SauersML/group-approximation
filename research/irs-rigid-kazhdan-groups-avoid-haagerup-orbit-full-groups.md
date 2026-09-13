---
rg: 2
id: irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups
kind: claim
title: An IRS-rigid infinite Kazhdan group has no nontrivial realization by bounded piecewise translations of a free action of a Haagerup group
distinct_from:
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that treats amenable acting groups and every Kazhdan group, through hyperfiniteness; this treats every Haagerup acting group, free groups included, and needs rigidity of invariant random subgroups instead.
  irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups: that uses IRS rigidity and non-amenability with an amenable acting group; this uses IRS rigidity and property (T) with a Haagerup acting group.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that concerns finite almost actions; this concerns genuine measure-preserving realizations inside orbit full groups.
---

**ESTABLISHED.**

**Setting.** `H` is a countable group with the Haagerup property, acting essentially freely
by measure-preserving Borel automorphisms on a standard probability space `(X, mu)`.
`W(H ~ X)` is the group of Borel bijections `g` of `X` with `g(x) = c_g(x) x` for a Borel
map `c_g : X -> H` of finite range.

**Theorem.** Let `S` be an infinite group with property (T) such that every invariant random
subgroup of `S` is a convex combination of `delta_e` and `delta_S`. Then every homomorphism
`rho : S -> W(H ~ X)` acts trivially almost everywhere.

**What it removes.** The amenable orbit certificate `amenable-orbit-full-group-subgroups-are-sofic`
has an obvious non-amenable extension. If `H` lies in Paunescu's class `𝒮` (free groups,
for instance: `paunescu-sofic-action-class-permanence`), a realization that is free off its
fixed points generates a subrelation of the sofic relation of `H ~ X`. Paunescu's
Proposition 1.15 then makes `S` sofic. The theorem says this extension still cannot reach
- the `(2,4,6)` Kac--Moody lattices `Lambda_q/Z`, `q >= 4`
  (`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`);
- any other compact-hyperbolic Caprace--Thom lattice;
- the binary Leavitt unit group, whose IRS rigidity is recorded in
  `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md`.

The acting groups covered include free groups, surface groups, lattices in `PSL_2(C)` and
every a-T-menable group.

**Necessity of the hypotheses.**
- *Property (T).* `H` realizes itself in `W(H ~ X)` with constant cocycles, and its orbits
  are infinite.
- *IRS rigidity.* The proof only shows that a nontrivial realization of a Kazhdan group has
  infinite stabilizers on a set of positive measure. `SL_3(Z)` acting through a finite
  quotient by piecewise translations has finite orbits; the theorem makes no claim there.

**Credit.** No novelty is claimed for the mechanism. Bounding a cocycle from a Kazhdan
group into a group with a proper affine isometric action, through the induced affine action
and Delorme--Guichardet, is standard. Bekka--Cherix--Valette (1993) give the equivalence
of the Haagerup property with a proper affine isometric action; theorem numbers were not
re-read. The combination with IRS rigidity for this certificate is new as far as this graph
records.

Proof: `irs-rigid-kazhdan-haagerup-orbit-full-groups-proof`.

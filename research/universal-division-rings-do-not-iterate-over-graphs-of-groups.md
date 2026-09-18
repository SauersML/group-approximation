---
rg: 2
id: universal-division-rings-do-not-iterate-over-graphs-of-groups
kind: claim
title: Universal division rings do not iterate over graphs of groups, already for the Promislow group as an amalgam of two Klein-bottle groups over Z^2, and the Linnell iteration over locally indicable amalgams is exactly the open Hughes-freeness question of FSP
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports the embedding of graphs of locally indicable groups with Hughes-free vertex rings; this shows that the stronger invariant (universal) is lost at the first amalgam, and that the Linnell invariant iterates exactly when FSP's open question q:HF has a positive answer.
  nonamenable-edges-break-division-ring-compatibility: that shows arbitrary vertex rings do not iterate over non-amenable edges; this shows universal vertex rings do not iterate even over abelian edges, so the only candidate invariant left is Hughes-free/Linnell.
  amenable-edge-graphs-of-groups-preserve-division-ring-embeddings: that embeds the Promislow group ring among many; this uses the same group to show the construction's output is Linnell but cannot be universal.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is an obstruction and exact reduction for iterating the graph-of-rings construction.
---

**ESTABLISHED** (obstruction and equivalence) by [[universal-rings-iteration-obstruction-proof]]. Not yet independently re-derived.

The step proposed was: vertex groups with Linnell (universal, unique) division rings and locally indicable edge
groups give a Linnell (universal, unique) division ring for the fundamental group. Here is how it splits.

**1. Universality is false at the first step.**
- The Promislow (Hantzsche--Wendt) group `P = <x, y | x^-1 y^2 x = y^-2, y^-1 x^2 y = x^-2>` is the amalgam
  `K1 *_(Z^2) K2`.
  - `K1 = <x, y^2>` and `K2 = <y, x^2>` are Klein-bottle groups.
  - The edge group is `<x^2, y^2> = Z^2`.
- The vertex groups are amenable and locally indicable, so they are Lewin (Jaikin-Zapirain, Selecta 2021, Thm 1.1).
  Their Ore fields are Hughes-free, Linnell and universal. The edge group is locally indicable.
- But `P` is not locally indicable, so `Q[P]` has no universal division ring of fractions (Jaikin-Zapirain,
  Prop. 4.1).
- The graph-of-rings output `U(D_K1 *_(D_Z^2) D_K2)` is universal as a division ring of the coproduct ring. It is the
  Ore field of `Q[P]`, which is Linnell and unique. It is not universal for `Q[P]`.
- So universality is not inherited from the ring coproduct by the group ring.

**2. The Linnell part, for locally indicable fundamental groups.** Let `G` be a graph of locally indicable groups
whose vertex rings `D_(kG_v)` are Hughes-free, over any field `k`, and suppose `G` is locally indicable. The following
are equivalent:
- (a) `k[G]` has a Linnell embedding;
- (b) the Hughes-free division ring `D_(kG)` exists;
- (c) FSP's question q:HF (arXiv:2303.08165) has a positive answer for this graph, that is, the graph-of-rings
  embedding is Hughes-free.

In characteristic 0 all three hold, by Jaikin-Zapirain--Lopez-Alvarez. In characteristic `p`, the step in this
generality is the open question q:HF, equivalently Jaikin-Zapirain's existence problem for Hughes-free division
rings restricted to graphs of groups.

**3. Non-locally-indicable fundamental groups.** Here only the Linnell clause can survive. Uniqueness of Linnell rings for
non-locally-indicable groups is itself open (FSP; arXiv:2603.26580). Over subfields of `C`, the strong Atiyah
conjecture for `G` implies (a), but not conversely. FSP (Remark after Thm 3mfld) cannot prove (a) even for virtually
locally indicable 3-manifold groups.

**Consequence.**
- Together with `nonamenable-edges-break-division-ring-compatibility`, the only invariant that can iterate the
  graph-of-rings construction over non-amenable edges is Hughes-free/Linnell. Arbitrary vertex rings fail, and so do
  universal ones.
- For locally indicable fundamental groups, the iteration is exactly q:HF.

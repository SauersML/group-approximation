---
rg: 2
id: overgroup-room-does-not-supply-a-root
kind: claim
title: Amplification and existential closure restate the conjecture instead of proving it
invalidates: [kl-via-infinite-dimensional-amplification, kl-via-existentially-closed-overgroup]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Two enlargements that look like reductions are equivalences.

**(a) Unitary amplification.**  For a group `G` and `w in G * <t>`, the
following are the same datum: a faithful `rho : G -> U(H)` together with
`T in U(H)` satisfying `w(rho, T) = I`; and a representation of `G_w` on `H`
whose restriction to `G` is faithful.  In particular `G -> G_w` is injective
if and only if such a pair exists — the left regular representation of `G_w`
supplies one.  Choosing `H` enormous, or replacing `rho` by infinitely many
copies of itself, changes nothing: room is not a root.

**(b) Existential closure.**  An existentially closed overgroup of `G` solves
exactly those finite systems over `G` that are consistent with the diagram of
`G`.  Consistency of `w(t) = 1` with all the inequations `g != 1` is
`kervaire-laudenbach-nonsingular-conjecture` for `(G, w)`.  So passing to an
e.c. overgroup transports the problem without touching it.

## Why this is worth recording rather than obvious

Both moves *are* the standard way to get room in this repository's other
programs, and both are correct there, where the missing ingredient is space
rather than an equation.  Here the missing ingredient is the equation, and
each move quietly assumes it.  The tell in a proposed argument is that the
faithfulness of the enlarged representation, or the consistency of the
enlarged system, is asserted rather than constructed.

Recorded dead: `kl-via-infinite-dimensional-amplification` and
`kl-via-existentially-closed-overgroup`.

## What is not killed

Enlargement *combined with* an independent root theorem — which is exactly
what the hyperlinear proof is: finite-dimensional unitary groups supply a
genuine root by a degree argument, and the ultraproduct supplies the room.
The live lane in that direction is
`window-controlled-finite-dimensional-root-theorem`; nothing here weakens it.

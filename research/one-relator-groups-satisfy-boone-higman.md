---
rg: 2
id: one-relator-groups-satisfy-boone-higman
kind: claim
root: true
title: Every one-relator group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over one-relator groups, which have solvable word problem by Magnus, so it is a strictly weaker open problem that the conjecture implies.
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs, among them every one-relator group with torsion and every one-relator group with negative immersions; this asks for all one-relator groups, including non-hyperbolic torsion-free ones such as BS(1,2) and the Baumslag--Gersten group.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers groups acting on locally finite trees, including the one-relator groups BS(m,n) and the finitely generated free-by-cyclic one-relator groups; this asks for every one-relator group, most of whose Magnus--Moldavanskii splittings have associated subgroups of infinite index.
  fp-residually-finite-boone-higman: that is item (12) of the same survey list, about finitely presented residually finite inputs; this is item (9), about one-relator inputs, which need not be residually finite.
  one-relator-groups-are-coherent: that is a subgroup finiteness theorem for one-relator groups; this is an embedding problem for them, and coherence does not imply it.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**OPEN.** Every one-relator group `G = <A | r>` embeds in a finitely presented
simple group.

## Where it is asked

- **Belk--Bleak--Matucci--Zaremsky,** *Progress around the Boone--Higman
  conjecture*, arXiv:2306.16356v3, Problem 5.3: "Prove the Boone–Higman
  conjecture for: ... (9) One-relator groups (without torsion)." The survey's
  Remark 5.4 reports no progress on item (9).
- **Linton--Nyberg-Brodda,** arXiv:2501.18306, Problem 1.8.6: "Can every
  one-relator group be embedded into a finitely presented simple group?"

Only the torsion-free case is open. One-relator groups with torsion are
hyperbolic (B. B. Newman), so they are covered by
`hyperbolic-groups-satisfy-boone-higman`. Survey Theorem 5.1(9) lists them, and
Linton--Nyberg-Brodda remark that "every one-relator group with torsion embeds
into a finitely presented simple group".

It is a special case of `boone-higman-conjecture` by
`one-relator-bh-from-boone-higman`. It is a root because it is a named open
problem in its own right, and because it has a route that does not exist for
general inputs: `one-relator-bh-via-magnus-moldavanskii-hierarchy`.

## What known theorems already cover

- **Torsion:** hyperbolic, as above.
- **Negative immersions,** equivalently every two-generator subgroup is free:
  hyperbolic by Linton, *One-relator hierarchies*, Theorem 7.2, so covered by the
  same theorem.
- **Finitely generated free-by-cyclic one-relator groups** (Moldavanskii's
  criterion, often called Brown's criterion): Bux--Llosa Isenrich--Wu,
  `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`.
- **BS(m,n):** the same source.
- **Virtually finitely generated free-by-cyclic one-relator groups,** including
  the torsion-free two-generator virtually RFRS ones:
  `virtually-free-by-cyclic-groups-satisfy-boone-higman`.

What remains is torsion-free one-relator groups with a non-free two-generator
subgroup that are neither virtually finitely generated free-by-cyclic nor
Baumslag--Solitar. The Baumslag--Gersten group
`<a,t | (t a t^-1) a (t a^-1 t^-1) = a^2>` is one: it is not residually finite,
and by `baumslag-gersten-base-is-elliptic-in-every-tree-action` it lies in no
Bux--Llosa Isenrich--Wu host over free, abelian or nilpotent vertex groups. No
theorem cited here covers it.

## Attempts

1. **Magnus--Moldavanskii induction.** `magnus-hnn-permanence-forces-one-relator-boone-higman`
   shows that the whole problem follows from the permanence premise
   `bh-embeddability-survives-magnus-subgroup-hnn`, where the base group may
   already be assumed to embed. That premise follows from
   `bh-embeddability-survives-decidable-edge-hnn` by
   `magnus-hnn-permanence-from-decidable-edge-permanence`. Both are open.
   *Deferred* to those claims.
2. **Locally finite trees (Bux--Llosa Isenrich--Wu Theorem 10.5).** This needs
   edge groups of finite index in the vertex groups. A Magnus HNN step with base
   `H` has free associated subgroups of equal rank. If both have finite index,
   then `H` is virtually free and torsion-free, hence free (Stallings--Swan).
   So the theorem reaches only steps over free bases, among them the doubly
   ascending steps (finitely generated free-by-cyclic groups) and `BS(1,n)`.
   *Dies* for steps whose base is not free, for example the Baumslag--Gersten
   step over `BS(1,2)` with cyclic edges of infinite index.
3. **Hyperbolic combination.** Linton, Theorem 7.1: a one-relator hierarchy is
   quasi-convex with hyperbolic top group exactly when it is Z-stable and the
   group contains no Baumslag--Solitar subgroup. So hyperbolicity reaches no
   group with a Baumslag--Solitar subgroup. *Dies* there.

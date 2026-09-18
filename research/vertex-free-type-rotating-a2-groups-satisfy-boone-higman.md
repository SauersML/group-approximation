---
rg: 2
id: vertex-free-type-rotating-a2-groups-satisfy-boone-higman
kind: claim
title: Type rotating groups acting freely on the vertices of an Ã₂ building with finitely many orbits embed in finitely presented simple groups
distinct_from:
  exotic-a2-lattices-satisfy-boone-higman: that concerns every discrete cocompact group on an exotic Ã₂ building, torsion and non type rotating actions included; this concerns groups acting freely on vertices by type rotating automorphisms on any Ã₂ building, including the CMSZ groups on exotic buildings.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for all CAT(0) groups; this is one subclass of Kazhdan CAT(0) lattices.
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**OPEN.** Let `B` be a locally finite thick Ã₂ building and `Γ` a group of type rotating
automorphisms of `B` acting freely on the vertices with finitely many orbits. Then `Γ`
embeds in a finitely presented simple group.

**Reduction** (route `a2-boone-higman-via-rs-two-graph-full-groups`). This follows from
three nodes:
- `a2-group-embeds-in-full-group-of-its-rs-two-graph`, OPEN because of missing pins;
- `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic`, OPEN, and the real gap
  for exotic buildings;
- `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`, whose proof is complete
  modulo the standard k-graph facts.

**Scope.** The simply transitive CMSZ groups on exotic Ã₂ buildings belong to this class.
By Bader–Caprace–Lécureux (pinned in `exotic-a2-lattices-satisfy-boone-higman`) they have
only finite linear images, so no linear Boone–Higman route on main reaches them. Lattices
with torsion, or not type rotating, are not covered.

## Status update (2026-09-18, bh-groupoid)

- **Premise refuted as stated.** The primitivity premise
  `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` is false for type-preserving
  `Γ`, where the period is 3 (`rs-strip-tail-transitivity-forces-primitive-transition-matrices`).
- **Corrected premise proved.** For every `Γ`, the transition matrices are irreducible, and
  they are primitive iff the type-rotation character `θ` is nonzero
  (`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`).
- **Other premises.** Aperiodicity always holds
  (`rs-two-graph-aperiodicity-from-h3-and-irreducibility`). The embedding premise is
  ESTABLISHED (`a2-group-embeds-in-rs-two-graph-geometric-proof`). These are lane proofs.
- **Type-transitive case.** For `θ ≠ 0` the claim is therefore reduced to the unpinned
  `finite-k-graph-boundary-groupoid-standard-facts`: see
  `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups` and route
  `type-transitive-a2-bh-via-rs-two-graph-full-groups`. Subgroups of such groups follow too.
- **Type-preserving case.** `θ = 0` without a type-transitive overgroup is still open. A
  sketch of a variant route through the index-3 degree lattice is in
  `research/artifacts/gq-bh-bh-groupoid-frontier.md` §6.

**Update (2026-09-18, later).** The standard facts are proved
(`finite-k-graph-standard-facts-proof`). So the type-transitive part
(`type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups`) is ESTABLISHED, as lane
proofs. This node remains OPEN only for type-preserving groups with no type-transitive
overgroup; see frontier §6 for a sketched route.

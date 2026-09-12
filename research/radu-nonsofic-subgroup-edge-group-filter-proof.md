---
rg: 2
id: radu-nonsofic-subgroup-edge-group-filter-proof
kind: route
title: Sofic combination over amenable edge groups on both Bass–Serre trees of Radu's lattice gives the edge-group filter
target: nonsofic-subgroups-of-radu-lattice-have-nonamenable-edge-groups
requires:
  - radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups
  - sofic-kernel-amenable-quotient-permanence
artifacts:
  - research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md
---

## Why sufficient

Artifact Section 2, Theorem B. Take `S` acting on the subdivided vertical tree. There are three cases.
* **Every element elliptic.** Then `S` fixes a vertex (Serre), so it lies in a virtually free vertex group.
* **A hyperbolic element and a fixed end.** The Busemann kernel is locally virtually free, and the
  quotient is contained in `Z`. So `S` is sofic by `sofic-kernel-amenable-quotient-permanence`.
* **Otherwise.** `S` is the fundamental group of the finite graph of groups on its minimal subtree. The
  vertex groups are virtually free, and the edge groups lie in conjugates of `A` or `A_ev`. If every edge
  group were amenable, `S` would be sofic.

The same argument runs on the horizontal tree, with `V`, `E_a` and `V_a`.

**Literature input, not a Cairn node:** graphs of groups with sofic vertex groups and amenable edge groups
are sofic. For amalgams this is Elek–Szabó, and for HNN extensions and graphs of groups Ciobanu–Holt–Rees,
both as cited by `amenable-envelope-magnus-piece-sofic-proof`. This lane did not re-read those sources.

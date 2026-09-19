---
rg: 2
id: convex-cores-inherit-greedy-coding-na
kind: claim
title: If a hyperbolic group G acts on a CAT(0) cube complex X with (NA), every quasiconvex subgroup Q with a Q-cocompact convex subcomplex Y ⊆ X satisfies (NA) on Y; so Q is a contracting RSG as soon as the greedy coding of Y satisfies (IRR), and in particular for quasiconvex subgroups of hyperbolic RACGs only (IRR) remains
distinct_from:
  greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs: that is the conditional theorem for one cubulation; this shows its hypothesis (NA) passes from an ambient cubulation to the convex core of any quasiconvex subgroup.
  contracting-rsgs-pass-to-finite-index-subgroups-via-loops: that handles finite-index subgroups by coset refinement; this handles quasiconvex subgroups of infinite index, where only (NA) passes and (IRR) is left.
  hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs: that proves (NA) for hyperbolic RACGs; with this, (NA) holds for every quasiconvex subgroup of a hyperbolic RACG acting on its convex core.
---

**ESTABLISHED** by `convex-cores-inherit-greedy-coding-na-proof` (lane `bh-partials`, 2026-09-19; elementary lane
proof, not reviewed; no priority claimed).

## Statement

Let `G` be hyperbolic, acting on a locally finite CAT(0) cube complex `X` cocompactly and freely on vertices, with (NA)
(`greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`). Let `Q ≤ G` be a non-elementary subgroup with trivial
finite radical, acting cocompactly on a convex subcomplex `Y ⊆ X`. Such a `Y` exists for every quasiconvex `Q`
(Sageev–Wise / Haglund; recalled).

1. The hyperplanes of `Y` are the `H ∩ Y` for the hyperplanes `H` of `X` that meet `Y`, and `H ↦ H ∩ Y` is injective.
2. `H ∩ Y` and `K ∩ Y` cross in `Y` iff `H` and `K` cross in `X`.
3. `(Q, Y)` satisfies (NA).

Hence, by `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`, the greedy coding of `∂Y` makes `Q` a faithful
RSG, and a contracting one exactly when it satisfies (IRR).

## Where this leaves Question 1.1 for cubulated groups

- **Hyperbolic ambient.** Quasiconvex subgroups of hyperbolic RACGs, and of any other (NA) cubulation, need only (IRR)
  on their convex cores. That is a finite check once a core is given.
- **Non-hyperbolic ambient.** Virtual specialness (Haglund–Wise, Agol) embeds cubulated hyperbolic groups quasiconvexly
  in right-angled Artin groups. Their Salvetti complexes are not hyperbolic, and (NA) fails there: parallel hyperplanes
  share infinite stabilizers.
- **What is open.** For a general closed hyperbolic 3-manifold group, both (NA) for its own cubulation and (IRR) are
  open. Whether every such group is quasiconvex in some hyperbolic RACG is not settled here.

## Lesson for general BH

- **The geometric half transfers through Helly.** (NA) and the finite nucleus pass to convex cores, because convex
  subcomplexes have Helly number 2. Crossing is therefore detected inside the core, and the core's hyperplane stabilizers
  sit inside the ambient ones.
- **The combinatorial half does not.** Irreducibility belongs to the new coding.
- **So in both directions** (finite-index subgroups, quasiconvex subgroups) the obstruction to Question 1.1 is the same
  single object: the recurrent structure of one finite state graph.

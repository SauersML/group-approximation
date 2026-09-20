---
rg: 2
id: decidable-edge-tower-premise-bh-equivalence-proof
kind: route
title: Push the decidable FA envelope into a base piece of the tower
target: decidable-edge-tower-premise-is-equivalent-to-boone-higman
requires: [decidable-groups-have-decidable-fa-envelopes, fa-subgroups-of-graph-towers-lie-in-base-pieces]
artifacts: [research/artifacts/decidable-edge-tower-premise-bh-equivalence-proof-2026-09-17.md]
---

This restores the route that was demoted to the artifact
`research/artifacts/decidable-edge-tower-premise-bh-equivalence-proof-2026-09-17.md`
pending a third referee vote. The proof is the artifact's text, re-checked line by
line here (swarm-0917 w23, 2026-09-20). It also follows at once from the later,
stronger `mixed-permanence-closures-collapse-boone-higman-to-base`, whose closure
`All(C)` contains every graph tower over `C`. So two independent established
arguments give the same statement.

**(a) Collapse.** Let `G` be finitely generated with solvable word problem. By
`decidable-groups-have-decidable-fa-envelopes`, `G <= W` with `W` finitely
generated, decidable and FA. Tree-universality of `C` puts `W` in a graph tower
`K` over bases in `C`. `W` is an FA subgroup of `K`, so by
`fa-subgroups-of-graph-towers-lie-in-base-pieces` a conjugate of `W` lies in some
base `B_i`. Then `G` embeds in `B_i`, a member of `C`.

*Check of the two imports.* The first gives `W = S wr C_2 = (S x S) ⋊ C_2` for
an infinite finitely generated decidable simple FA group `S ⊇ G x Z`. Its FA
proof (commuting fixed subtrees) was re-checked, and an independent argument
that needs only perfectness of `S`, not FA, was re-derived: if the
first factor `S_1` had a hyperbolic element `g`, then `S_2` would commute with
`g`, preserve its axis and act on it through the solvable group `D_∞`; being
perfect it would fix the axis pointwise, but `S_2` contains the hyperbolic
element `c g c^-1`. So each factor fixes a point, the fixed tree of `S_1` is
`S_2`-invariant and contains an `S_2`-fixed point (nearest-point projection),
and the finite group `C_2` then fixes a point of the nonempty fixed tree of
`S_1 x S_2`. The second import is Serre's fixed-vertex argument applied down
the tower; HNN and amalgam steps act on their Bass--Serre trees without
inversions.

**(b) Equivalence.** (`=>`) With `C` the class of finitely generated groups
that embed in a finitely presented simple group, the premise
`decidable-groups-embed-in-decidable-edge-towers` makes `C` tree-universal (the
decidability of the edges is never used). By (a) every decidable `G` embeds in
a member of `C`, which is `boone-higman-conjecture`. (`<=`) Given the
conjecture, take `B = G` and `n = 0`.

**(c) Class kill.** A reduction "base class `C` with finitely presented simple
envelopes + permanence along graph towers" certifies the conjecture exactly
when `C` is tree-universal. By (a) some member of `C` then contains a copy of
each decidable `G` (in particular of each `S wr C_2`), so no permanence step is
used. This is the wording repair both returned referee votes asked for:
*some member* of `C`, not `C` itself, contains each `S wr C_2`. `∎`

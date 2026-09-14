---
rg: 2
id: fournier-facio-outside-surjunctivity-permanence
kind: claim
title: The Fournier-Facio torsion-free group is an open Gottschalk host that no permanence theorem here reaches
distinct_from:
  fournier-facio-group-is-nonsofic: that is the nonsoficity of the group; this records that its surjunctivity is open and outside every surjunctivity permanence theorem in this graph.
  leavitt-unit-group-nonsurjunctive: that seeks a counterexample on the binary Leavitt unit group; this is a different, unrelated nonsofic host, with no known embedding either way.
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces the universal conjecture to one fixed finitely presented host; this records that the Fournier-Facio group is a distinct nonsofic host whose own surjunctivity is unsettled by the permanence theorems.
  thompson-v-not-sofic: that is the open nonsoficity of Thompson V; this concerns surjunctivity of a torsion-free property-(T) group and its position relative to the permanence classes.
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

**OPEN.** Let `G = <Gamma, t_1, t_2>` be the Fournier-Facio finitely presented
torsion-free property-(T) group of `fournier-facio-torsion-free-skeleton`, with
`Gamma` an infinite property-(T) subgroup, `t_1 Gamma t_1^{-1} <= Gamma` a proper
compressing self-embedding, and a simple group in its compression defect. `G` is
not sofic (`fournier-facio-group-is-nonsofic`). Whether `G` is surjunctive is
open, and none of the surjunctivity permanence theorems in this graph decides it.

This is the one nonsofic host recorded here that is neither reached by a
permanence theorem nor part of the Leavitt tower `V <= R^x <= A^x`
(`leavitt-surjunctivity-tower`): as far as is known, `L_{F_2}(1,2)^x` does not
embed in `G` and `G` does not embed in it, so a Gottschalk counterexample on `G`
would be a mechanism distinct from the Leavitt one. A non-surjunctive `G` would
be nonsofic, which is already known, so surjunctivity carries no free corollary
here.

## Attempts

- **`finitary-split-extension-surjunctivity-permanence`.** It needs `W = N ⋊ Q`
  with a residually finite finitary kernel over a surjunctive base `Q`. `G`'s
  nonsoficity is intrinsic to the compression of the Kazhdan `Gamma`; there is no
  presentation of `G` as a split extension of a surjunctive base by a residually
  finite kernel with detection, finite support and stabilizer invariance. The
  compressed Kazhdan `Gamma` is exactly not such a base. Blocked.
- **`graph-folds-over-surjunctive-groups-are-surjunctive`.** It makes an HNN
  extension of `A <= G'` surjunctive when the associated-subgroup isomorphism is
  conjugation by an element of a surjunctive host `G'`. `G` is an
  ascending-HNN-flavored `<Gamma, t_i>`, but the required host would have to be
  surjunctive and already contain the proper compression of the Kazhdan `Gamma`,
  which is essentially `G` itself. Not known to apply.
- **`lef-lamp-graph-wreaths-are-surjunctive`.** It needs a graph-product lamp
  kernel with a permutation actor; `G` has no such description. Blocked.
- **Subgroup route.** `G` contains a simple wreath shift and other subgroups
  (`fournier-facio-group-contains-simple-wreath-shift`), but by
  `surjunctivity-passes-to-subgroups` a surjunctive subgroup gives no information
  about the whole group; subgroup structure constrains counterexamples (the
  overgroup form), not surjunctivity proofs. No non-surjunctive subgroup of `G`
  is known.
- **Fixed-tester route.** `gottschalk-surjunctivity-fixed-two-generator-tester`
  reduces the universal conjecture to one fixed host, so `G` is not needed for
  the universal question; but its own surjunctivity remains a separate open
  problem, not settled by that reduction.

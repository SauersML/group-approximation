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
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
---

**OPEN.** Let `G = <Gamma, t_1, t_2>` be the Fournier-Facio finitely presented
torsion-free property-(T) group of `fournier-facio-torsion-free-skeleton`, with
`Gamma` an infinite property-(T) subgroup, `t_1 Gamma t_1^{-1} <= Gamma` a proper
compressing self-embedding, and a simple group in its compression defect. `G` is
not sofic (`fournier-facio-group-is-nonsofic`). Whether `G` is surjunctive is
open, and none of the surjunctivity permanence theorems in this graph decides it.

This is the one nonsofic host recorded here that is neither reached by a
permanence theorem nor part of the Leavitt tower `V <= R^x <= A^x`
(`leavitt-surjunctivity-tower`). No member of that tower embeds in `G`, because
each has elements of order two and `G` is torsion-free
(`leavitt-tower-does-not-embed-in-torsion-free-hosts`). Whether `G` embeds in
`L_{F_2}(1,2)^x` is not known. So a Gottschalk counterexample on `G` would be a
mechanism distinct from the Leavitt one. A non-surjunctive `G` would
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
- **Torsion-free design constraints (gk-n-ff, 2026-09-12).**
  - `invariant-output-injective-ca-need-torsion`: no injective automaton on `G`
    has output invariant under a nontrivial subgroup. That kills the
    invariant-output architecture and every finite-subgroup corner design, swap
    and Klein included.
  - `torsion-free-scalar-df-failure-gives-exotic-idempotents`: a scalar linear
    counterexample on `G` would first refute Kaplansky's idempotent and
    zero-divisor conjectures for `G`.
  - What survives: matrix-size linear designs, and nonlinear designs without
    output symmetry whose forward table forces a nonsofic core read off the
    compression of `Gamma`. No candidate is known.
- **Certification surface.**
  - The word problem of `G` is not established, since the construction is
    existential.
  - A counterexample certificate on `G` needs explicit derivations for forward
    coincidences and inequalities certified inside `G`.
  - (W8) of `fournier-facio-nontrivial-quotients-contain-simple-wreath` certifies
    inequalities inside the embedded `S wr Z`, which has solvable word problem when
    `S` does. It certifies nothing that involves `Gamma` or `t_2`.
- **Positive side.**
  - The structured subgroups `S wr Z`, `Gamma x (+)_(k<=0) J_k` and the tree lamp
    group are covered by no permanence theorem: `S` is simple and not residually
    finite, and closure under finite direct products is open.
  - `wreath-surjunctivity-reduces-to-stabilizer-products`: the embedded `S wr Z` is
    surjunctive iff every finite power `S^n` is. So on this subgroup the question is
    exactly surjunctivity of the powers of the simple factor, and whether surjunctivity
    is closed under finite direct products is the missing input.
  - `sofic-permanence-closure-omits-simple-fa-nonsofic-groups` bears on `G` only
    through a finitely presented simple nonsofic FA subgroup, and none is recorded.
  - Details: `research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md`.

---
rg: 2
id: leavitt-surjunctivity-tower
kind: claim
title: Thompson V, the binary Leavitt unit group and the d-ary Leavitt unit groups form a surjunctivity tower
distinct_from:
  leavitt-unit-group-nonsurjunctive: that seeks one injective non-surjective automaton on the binary Leavitt unit group; this decides no group's surjunctivity and only orders the three groups by inclusion so their surjunctivity statements are comparable.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is a nonsoficity statement about the d-ary unit, GL and EL groups; this is a surjunctivity ordering that uses the group embeddings underneath that result, and asserts nothing about soficity.
  surjunctive-guard-subgroups-force-surjectivity: that concerns an automaton preserving cosets of one surjunctive guard inside a fixed group; this concerns inclusions between three different nonsofic groups and the monotonicity of surjunctivity along them.
  thompson-v-not-sofic: that is the open nonsoficity of Thompson V; this records the group inclusion V into the binary Leavitt unit group and its surjunctivity consequences, not any approximation property.
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

ESTABLISHED. Write `R = L_{F_2}(1,2)`, `R^x = L_{F_2}(1,2)^x` the binary Leavitt
unit group (the group of the open root `leavitt-unit-group-nonsurjunctive`), and
`A^x = L_{F_2}(1,d)^x` for `d >= 2`. Then there are group embeddings

    V <= R^x <= A^x,

where `V` is Thompson's group. Consequently, by `surjunctivity-passes-to-subgroups`:

- surjunctivity descends: `A^x` surjunctive implies `R^x` surjunctive implies
  `V` surjunctive;
- non-surjunctivity ascends: `V` not surjunctive implies `R^x` not surjunctive
  implies `A^x` not surjunctive.

This decides none of the three groups. It orders the two searches. For a
counterexample, `V` is the strongest target (a non-surjunctive automaton there
refutes Gottschalk and ascends to `R^x` and `A^x`) and the d-ary `A^x` is the
easiest (largest group, most room, still a refutation, but it does not by itself
settle `R^x`). For a positive proof, `A^x` is hardest and implies the others.

The lower embedding is `leavitt-cylinder-swaps-generate-thompson-in-el`
(`V <= EL_9(R)`) together with `leavitt-gl-equals-el-and-perfect-unit-group`
(`GL_n(R) = EL_n(R)` for `n >= 2`, all identified with `R^x`). The upper
embedding is the corner family of `d-ary-leavitt-groups-nonsofic-over-finite-fields`:
over `F_2` the corner of `L_{F_2}(1,d)` carries a binary Leavitt family
generating a copy of `L_{F_2}(1,2)`, and its corner-extension homomorphism is
injective. Every d-ary Leavitt unit, `GL` and `EL` group over `F_2` contains this
binary core, so all sit above `R^x` and inherit the same statements.

Two consequences recorded here: the finitely presented simple nonsofic group of
`fp-simple-nonsofic-via-leavitt-unit-group` is `R^x` itself, not a separate host;
and a non-surjunctive `V` would be nonsofic by Gromov--Weiss, which would settle
`thompson-v-not-sofic`.

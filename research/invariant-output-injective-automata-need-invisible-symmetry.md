---
rg: 2
id: invariant-output-injective-automata-need-invisible-symmetry
kind: claim
title: An injective automaton with right-coset-invariant output needs its symmetry inside the sofic radical of the memory group
distinct_from:
  order-three-axis-feedback-surjunctivity-iff-corner-finiteness: that reduces one quadratic feedback family on order-three blocks to direct finiteness of a corner ring; this is a necessary condition on every nonlinear or linear automaton whose output is constant on right cosets of a finite subgroup, phrased through permutation models.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `G` be countable, `A` finite with `|A| >= 2`, and `H` a finite subgroup.
Suppose `tau` is an injective cellular automaton with

    tau(x)(gh) = tau(x)(g)       for all x, g, and h in H.

Then:

- `h M_eff = M_eff` for the effective memory and every `h` in `H`, so `H` lies
  in `K = <M_eff>`;
- `H` lies in `Rad(K)`, the sofic radical of
  `sofic-radical-localizes-garden-of-eden-windows`;
- if `H != 1`, `tau` is not surjective. Every configuration that is not
  right-`H`-invariant is missed, so a two-cell pattern on `{1,h}` with distinct
  symbols is a Garden of Eden.

Consequently the class is empty whenever the memory generates a sofic group. A
strict automaton of this shape must be built on a symmetry that no
almost-multiplicative permutation model of its memory group can see.
Conversely, over a group where every finite subgroup is invisible,
this counting obstruction has nothing left to say (see
`leavitt-unit-group-has-only-trivial-sofic-morphisms`).

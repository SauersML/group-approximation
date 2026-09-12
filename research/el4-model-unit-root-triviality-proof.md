---
rg: 2
id: el4-model-unit-root-triviality-proof
kind: route
title: Twelve Steinberg commutators fill the normal closure of one root element
target: el4-model-trivial-on-one-unit-root-element-is-trivial
requires: []
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

This is Section 2, Lemma 3 of the artifact.

**Setup.** Let `N` be the normal closure of `x_IJ(1)` in `EL_4(R)`, and let `K`, `L` be the other two
indices. If `a` is in `N`, then so are `[a, g]` and `[g, a]` for every `g`. Use the relation
`[x_ab(r), x_bc(s)] = x_ac(rs)` for distinct `a, b, c`.

**Part 1.** In each commutator below, the argument drawn from `N` comes from an earlier step:

```text
x_IK(r) = [x_IJ(1), x_JK(r)],  x_IL(r) = [x_IJ(1), x_JL(r)],
x_KJ(r) = [x_KI(r), x_IJ(1)],  x_LJ(r) = [x_LI(r), x_IJ(1)],  x_IJ(r) = [x_IK(r), x_KJ(1)],
x_KL(r) = [x_KJ(r), x_JL(1)],  x_LK(r) = [x_LJ(r), x_JK(1)],
x_KI(r) = [x_KL(r), x_LI(1)],  x_LI(r) = [x_LK(r), x_KI(1)],  x_JI(r) = [x_JK(1), x_KI(r)],
x_JK(r) = [x_JI(r), x_IK(1)],  x_JL(r) = [x_JI(r), x_IL(1)].
```

So `N` contains every root subgroup, and `N = EL_4(R)`.

**Part 2.** From `x_IJ(r)` in `N`, both `x_IK(rb) = [x_IJ(r), x_JK(b)]` and
`x_LK(arb) = [x_LI(a), x_IK(rb)]` are in `N`. Simplicity gives `sum_m a_m r b_m = 1`, so
`x_LK(1) = prod_m x_LK(a_m r b_m)` is in `N`, and Part 1 applies.

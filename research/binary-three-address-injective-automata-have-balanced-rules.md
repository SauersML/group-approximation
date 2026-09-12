---
rg: 2
id: binary-three-address-injective-automata-have-balanced-rules
kind: claim
title: Over every group, an injective two-symbol automaton with at most three memory elements has a balanced rule
distinct_from:
  binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective: that excludes placements whose quotients m^-1 m' are distinct, for every memory size; this settles every placement of three elements, the relation cases included, by constant tests, prescribed flips and a double flip along an involution.
  unbalanced-forward-tables-identify-memory-letters: that is the open goal-equivalent claim that unbalanced designs collide memory letters in every minimal table group; this proves its two-symbol, three-address case.
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `binary-three-address-balance-census-proof`.

**Theorem.** Let `G` be any group, `M` a subset of `G` with `|M| <= 3`, and
`mu : {0,1}^M -> {0,1}`. If `tau(x)(g) = mu((x(g m))_(m in M))` is injective, then `mu` is
balanced. With `|M| <= 2` the same holds for every alphabet.

This is the smallest nontrivial case of `every-injective-ca-has-uniform-single-site-output-law`,
which is equivalent to Gottschalk's conjecture. The memory here can generate any 2-generated
group, nonsofic ones included, and the proof uses no finite models of it.

**How the proof goes.**
- **Constant tests.** Constant configurations, and one flip of a constant, leave four rule classes
  up to symmetry: `T = {000, 110}`, `{000, 100, 110}`, `{000, 110, 001}` and `{000, 110, 101}`.
- **Prescribed flips.** For each class, a flip with prescribed surroundings is invisible. The only
  exception is a short relation among `a, b` that makes `<M>` cyclic or dihedral.
- **Double flip.** For `{000, 110, 101}` with an involution among the memory quotients, a double
  flip along that involution does the same job, again unless `<M>` is cyclic, dihedral or abelian.
- **Amenable cases.** In all of those, injectivity forces surjectivity.

**Design form.** Take a binary three-address design with an unbalanced rule. Every
forward-sufficient table group collides two of its memory letters.

Artifact, Section 4.

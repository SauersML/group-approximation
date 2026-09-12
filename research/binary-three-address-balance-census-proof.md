---
rg: 2
id: binary-three-address-balance-census-proof
kind: route
title: Constant tests leave four rule classes, and prescribed flips exclude each of them outside cyclic, dihedral and abelian memory groups
target: three-address-binary-injective-rules-are-balanced
requires:
  - sofic-groups-are-surjunctive
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

This is a second, independent proof of w3-bal-design's claim, which uses the rectangle relation and
an involution-glued double flip. This route runs a different case analysis (artifact, Section 6).

Section 4 of the artifact, with the reductions of Section 1.
- **Two addresses.** `M = {1, a}` generates a cyclic group. Cyclic groups are sofic, so an
  injective automaton there is bijective and has a balanced rule.
- **Constant tests.** Constant configurations, and one flip of the constant `1`, reduce three
  addresses to the four classes `{000, 110}`, `{000, 100, 110}`, `{000, 110, 001}` and
  `{000, 110, 101}`. This uses output negation, global input negation and permutation of
  addresses.
- **Prescribed flips.** For each class the artifact lists values on the six sites
  `h {a, b, a^-1, a^-1 b, b^-1, b^-1 a}` that make a flip at `h` invisible. A choice fails only
  when a 0-site equals a 1-site, and every such relation makes `<a, b>` cyclic or dihedral.
- **Double flip.** For `{000, 110, 101}` with `a^2 = 1` (or `b^2 = 1`), the double flip of `h` and
  `ha` is invisible with the listed surroundings, unless `<a, b>` is cyclic, dihedral or abelian.
- **Amenable cases.** There, `sofic-groups-are-surjunctive` makes the automaton bijective, and
  `bijective-ca-preserve-uniform-bernoulli-measure` balances its rule.

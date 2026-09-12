---
rg: 2
id: dihedral-marker-formalization-induces-to-thompson-v
kind: route
title: Embed the infinite dihedral group in V and reuse the same polynomials
target: thompson-v-marker-involution-is-formalizable
requires:
  - dihedral-marker-involution-is-formalizable
  - formal-pairs-push-along-quotients-of-the-encoder-memory-group
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

1. **The dihedral subgroup.** In `V`, `g(0w) = 0 a(w)`, `g(1w) = 1 a^(-1)(w)` and the first-letter swap
   `s` satisfy `s^2 = 1` and `sgs = g^(-1)`. Also `s` is not in `<g>`. So `<g, s>` is infinite dihedral
   (artifact Section 5).
2. **The same rule.** The `V`-marker along `g` is the automaton induced from the `D`-marker: same local
   rule, same memory.
3. **Formal pairs pass up.** A formal pair over `D` is a formal pair over `V` with the same polynomials,
   because the composite at cell `1` involves only cells in `D`. This is the "passes up" consequence of
   the second prerequisite.

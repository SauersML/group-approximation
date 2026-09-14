---
rg: 2
id: thompson-v-marker-stable-formalizability-from-dihedral
kind: route
title: Induce the dihedral stable formalization up to V with the same polynomials
target: thompson-v-marker-involution-is-stably-formalizable
requires:
  - dihedral-marker-involution-is-stably-formalizable
  - formal-pairs-push-along-quotients-of-the-encoder-memory-group
artifacts:
  - research/artifacts/dihedral-marker-composition-reduction-2026-09-12.md
---

1. **Dihedral subgroup.** `g(0w) = 0 a(w)`, `g(1w) = 1 a^(-1)(w)` and the first-letter swap `s`
   generate an infinite dihedral `<g, s> <= V` (artifact of
   `thompson-v-marker-involution-is-formalizable`, Section 5).
2. **Same rule.** `tau_g` is induced from the `D`-marker: same local rule, same memory, and the
   ancilla tracks are added over all of `V`.
3. **Pass up.** A `D`-equivariant formal pair is a `V`-equivariant formal pair with the same
   polynomials, since the formal identity at cell `1` involves only cells of `<g, s>` (the "passes up"
   direction of `formal-pairs-push-along-quotients-of-the-encoder-memory-group`). The ancilla tracks,
   carried along, keep the identity on their own cells. So a stable formalization over `D` gives one
   over `V`.

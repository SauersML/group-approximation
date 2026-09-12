---
rg: 2
id: level-unit-hnn-extensions-have-anti-central-rank-models
kind: claim
title: The twisted regular tower of the ternary level unit group extends to every multiple HNN extension along partial conjugations by elements of the Leavitt unit group
distinct_from:
  char-three-level-factoring-models-of-leavitt-units-are-trivial: that excludes models of G_3 factoring through level groups with positive displacement; this builds models of HNN extensions of the level unit group whose letters are deliberately not level-factoring.
  ternary-leavitt-units-have-a-nontrivial-char-three-rank-model: that is the open gate for G_3 itself; this realizes only the relations of the level unit group and single-letter partial conjugations, which G_3 satisfies together with further multi-letter relations.
artifacts:
  - research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md
---

**ESTABLISHED** (proof: Section 2 of the linked artifact, route
`level-unit-hnn-extension-rank-models-proof`).

**Setting.** `G = L_(F_3)(1,2)^x`, `z = −1`. The level unit group `L = ∪_j GL_(2^j)(F_3)` embeds through
depth-`j` matrix units. For `g ∈ G`, put `B_g = {a ∈ L : g a g^(−1) ∈ L}` and `φ_g(a) = g a g^(−1)`.

**Theorem.**
1. **The tower.** Left multiplication on `F_3[GL_(2^j)(F_3)] ε₋`, with `ε₋ = (1 − [z])/2`, defines an
   injective anti-central rank model `σ_reg` of `L`. It is free on every finite subgroup containing `z`,
   so it carries the Haar law on the signed diagonal.
2. **One letter.** For every `g ∈ G` there is `X_g ∈ M^x` with `X_g σ_reg(a) X_g^(−1) = σ_reg(φ_g(a))`
   for all `a ∈ B_g`.
3. **HNN extensions.** For every countable `I ⊆ G`, `σ_reg` extends to the multiple HNN extension
   `<L, t_g (g ∈ I) | t_g a t_g^(−1) = φ_g(a), a ∈ B_g>`, which maps onto `G` for `I = G`.
4. **Torsion letters.** A torsion letter whose domain is exhausted by invariant finite subgroups keeps
   its order. An example is the Thompson three-cycle of cylinders `[0], [10], [11]`.

**Consequence for the "no" direction.** A proof that all characteristic-three rank models of `G` are
trivial cannot rest on the relations of `L` and single-letter partial conjugations. It must use a
relation among two or more letters outside `L`, for instance:
- `V`'s multiplication table on depth-changing elements;
- commutation of disjointly supported depth-changing elements;
- Steinberg commutators of two non-level root elements, as in family R4's rank-four assembly.

No priority is claimed. This is a linear analogue of soficity of HNN extensions over amenable subgroups,
recorded to calibrate the gate.

## Attempts

Established; see `level-unit-hnn-extension-rank-models-proof`.

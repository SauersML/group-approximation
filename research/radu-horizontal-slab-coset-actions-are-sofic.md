---
rg: 2
id: radu-horizontal-slab-coset-actions-are-sofic
kind: claim
title: The arithmetic quotient of Radu's lattice acts soficly on the cosets of its horizontal free product and of the index-two kernel of the c-sign
distinct_from:
  function-field-building-vertex-action-is-sofic: that is the Kazhdan building action of SL_3(F_2[t,1/t]), where exact models are excluded and perturbations are fenced; this is a tree action with virtually free stabilizers and the Haagerup property
  radu-bmw-lattice-sofic: that is soficity of Radu's lattice; this is a set action of its residually finite arithmetic quotient, which implies it
---

**OPEN.** Let `Q = Γ_R/Λ_v` be the cocompact arithmetic lattice in `PGL_2(Q_2) × PGL_2(Q_2)` of
`radu-horizontal-quotient-is-arithmetic-lattice`. Let `A = <a,b,c> ≅ C_2 * C_2 * C_2`, the image of the
horizontal letters, and `A_c = ker(χ_c : A → {±1}, c ↦ −1)`. The claim is that both coset actions

```text
Q ↷ Q/A        and        Q ↷ Q/A_c
```

are sofic in the sense of GKP Definition 2.1(5).

**Why it matters.** `Q/A_c ⊔ Q/A` is the `Q`-set of oriented edges of `Y = Λ_v\T_v`, so this claim
makes `Γ_R` sofic (`radu-bmw-lattice-sofic-via-slab-coset-actions`). Γ_R/[Λ_v,Λ_v], which is `G_2` of
`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`, is then sofic too.

**Geometry.**
* `A` fixes the vertex `p` of the second tree `T'` and has index 6 in `Stab_Q(p)`
  (`radu-xz-slab-is-second-tree-edge-stabilizer`). So `Q/A → V(T')` is 6-to-1.
* The stabilizers are commensurated, cocompact, virtually free lattices on the first tree. Their
  Schlichting completion is the closure of `Q` in the second factor `PGL_2(Q_2)`.
* This is the tree, Haagerup analogue of the Hecke-pair coset actions.

## Attempts

* **Exact finite actions.** Dead at the congruence level. At the degree-one primes
  `13, 19, 43, 47, 53, 59`, the image of `A` in `PGL_2(F_p)` has index at most 2, and the images of
  `H_Q ⊃ A` and `Q` coincide (`research/artifacts/radu-slab-character-screen-output-2026-09-13.txt`).
  * *Why this kills them.* Strong approximation suggests `A` is dense in every congruence quotient up
    to bounded index. In any `Q/L` with `A ⊆ L`, the point stabilizer then contains the whole
    congruence closure of `A`. That closure holds short elements outside every conjugate of `A`, so
    `Q/L` cannot model `Q/A` locally.
  * *Status.* This is argued for congruence quotients only, not for all finite quotients.
* **GKP Theorem 2.14.** It covers only locally finite stabilizers. `A` is virtually free. Dies.
* **Kazhdan codensity fence.** It does not apply. `A` and `Q` have the Haagerup property, so
  perturbed models are not excluded (contrast `codense-kazhdan-coset-action-forces-permutation-outliers`).
  No nonsoficity mechanism is known either.
* **Geometric models.** Take finite square complexes locally modelled on `T_h × T'` with `Q`'s labels,
  complete links and exact squares. Each is `L\(T_h × T')` for a finite-index `L ≤ Q`, so it has at
  most `[Q : L·Stab_Q(p)]` horizontal slices. A model of `Q/A` needs many slices, each looking like
  `A\T_h`. So a model must break squares on a sparse set while keeping arithmetic labels coherent.
* **Parity constraint.** On `Q/A_c` the sign `χ_c` is built into the stabilizer. The screens also show
  `χ_c` does not descend to congruence images of `A`. So the two sheets of `Q/A_c → Q/A` must be
  separated by the model, not by a congruence character.

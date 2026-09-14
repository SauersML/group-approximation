---
rg: 2
id: polynomially-small-units-have-order-dividing-420
kind: claim
title: "In any unital F_2-algebra, a unit σ with 1 in span(σ^{±1}, σ^{±2}) has order dividing 420"
artifacts:
  - research/artifacts/sk-cstar-genericity-2026-09-14-part1.md
distinct_from:
  idempotent-displacement-fails-for-polynomially-small-units: that shows these units admit no idempotent displacement configuration; this bounds their order, so every group inside B_4 ∪ {1} has exponent dividing 420
---

**ESTABLISHED (unreviewed).** Let `M` be a unital `F_2`-algebra and `σ ∈ M^×` with `1 = c_1σ + c_{-1}σ^{-1} + c_2σ^2 + c_{-2}σ^{-2}` for some `c_k ∈ F_2`. Then `σ^{420} = 1`.

**Consequence.** Every subgroup of `M^×` contained in `B_4 ∪ {1}`, where `B_4 = {σ : 1 ∈ span_{F_2}(σ^{±1},σ^{±2})}`, has exponent dividing 420. With `confined-subgroup-pigeonhole-commutator-lemma` (R″), (L3) reduces to commutators whose 420th power is nontrivial.

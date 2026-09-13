---
rg: 2
id: dead-vertex-raag-kernels-retract-onto-subgraph-kernels-proof
kind: route
title: The standard retraction of a RAAG onto a subgraph RAAG restricts to the kernels
target: dead-vertex-raag-kernels-retract-onto-subgraph-kernels
requires: []
---

Let `r : A_Γ → A_Λ` be the standard retraction, sending `v ↦ v` for `v ∈ Λ`
and `v ↦ 1` for `v ∉ Λ`. It is well defined because every commutation
relation maps to a relation of `A_Λ` or to a trivial one, and `r` restricts to
the identity on `A_Λ ≤ A_Γ`.

On generators, `χ_Λ ∘ r = χ`: for `v ∈ Λ` both sides give `χ(v)`, and for
`v ∉ Λ` both give `0`. So `r(ker χ) ⊆ ker χ_Λ`. Also
`ker χ_Λ = ker χ ∩ A_Λ ⊆ ker χ`, and `r` is the identity there. So
`r|_{ker χ}` is a retraction of `ker χ` onto `ker χ_Λ`.

A retract of a finitely presented group is finitely presented, and its Dehn
function is `≼` that of the group. Choose a finite presentation of the
subgroup and extend it to one of the group. A word null in the retract is
filled in the group, and the retraction sends each relator of the group to a
null word of bounded length in the retract, which has bounded area there.

---
rg: 2
id: kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich
kind: route
title: A hyperlinear floor below the normal closure is compressor-stable with polynomial content, so the sandwich collapses it to Gamma
target: hyperlinear-wreath-model
requires:
  - kt-pair-hyperlinear-floor-below-normal-closure
  - kt-compressor-stable-polynomial-content-overgroups-are-gamma
  - kt-compressor-stable-overgroups-have-polynomial-content
  - theorem-c-separation-iff-infranormal-coset-wreath
---

Assume `kt-pair-hyperlinear-floor-below-normal-closure`. The Theorem E group `G` is
residually finite and therefore hyperlinear. By
`theorem-c-separation-iff-infranormal-coset-wreath` (2)(b)⇒(c) and Part 1,
`Δ_hl = Δ_hl(Γ,G)` contains `Γ`, `W_(Δ_hl)` is hyperlinear, `⟨⟨Γ⟩⟩ ⊄ Δ_hl`, and
`pΔ_hl p^(-1) ≤ Δ_hl` for every `p ∈ P_Γ ⊇ Mon`.

By `kt-compressor-stable-overgroups-have-polynomial-content`,
`e_12(f) ∈ Δ_hl ⇒ f ∈ A`. The sandwich claim
`kt-compressor-stable-polynomial-content-overgroups-are-gamma` then gives `Δ_hl = Γ`. So
`W_Γ` is hyperlinear, which is `hyperlinear-wreath-model` for the Theorem E pair.

The converse, `hyperlinear-wreath-model` ⇒ the node, is immediate with `Δ = Γ`. Under the
sandwich claim the node is therefore **equivalent** to `hyperlinear-wreath-model`, and the
Theorem-C route to a hyperlinear nonsofic action gives no discount at this pair.

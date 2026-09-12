---
rg: 2
id: finite-subgroup-idempotent-ideal-shift-proof
kind: route
title: Transfer the one-coset equation to the HNN extension, use direct finiteness there, and push the equality back
target: finite-subgroup-idempotent-ideals-admit-no-proper-group-shift
requires: []
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

Artifact Sections 1–2.
- **One double coset.** `x ⊗ y |-> x[g]y` is injective from `k[K] ⊗_(k[D]) k[K]`, in any group where
  `K ∩ gKg^(-1) = D` and the twist is the same. By Britton's lemma, the stable letter of the HNN extension qualifies.
  So `(I - e)[g]e = 0` in `G` gives `(I - e)[t]e = 0` in `H`.
- **Left inverse in `H`.** `yx = I + e[t^(-1)](I - e)` is a unit, with `x = [t]e + (I - e)` and
  `y = e[t^(-1)] + (I - e)`.
- **Direct finiteness.** `x` is invertible, so `B = [t]eB (+) (I - e)B = eB (+) (I - e)B` with `[t]eB ⊆ eB`. The
  modular law gives equality.
- **Finite `K`.** `H -> Sym(K)` is injective on `K`, and its kernel acts freely on the Bass–Serre tree, so it is free.
  `M_n(k[H])` then embeds in matrices over a Malcev–Neumann division ring.
- **Push forward** along `H -> G`.

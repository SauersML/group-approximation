---
rg: 2
id: bs-1-m-in-3v-via-odd-smart-renormalization
kind: route
title: A height-m renormalization of SMART_m induced on level-zero moves gives BS(1,m) in 3V for every odd m
target: bs-1-m-embeds-in-brin-thompson-3v-for-odd-m
requires:
  - odd-smart-induced-map-has-height-m-renormalization
  - renormalizable-thompson-elements-give-baumslag-solitar
---

Fix odd `m >= 3`. `odd-smart-induced-map-has-height-m-renormalization` gives `U' ∈ 2V` (the moving-tape map
of `SMART_m`, induced on the starts of genuine level-0 moves and conjugated brick-locally into `2V`) with a
height-`m` renormalization `(A, φ)`: `A` is clopen with `C^2 = A ⊔ U'A ⊔ … ⊔ U'^{m-1}A` and `U'^m A = A`, and
`φ : A → C^2` is a brick-local homeomorphism with `φ ∘ U'^m|_A = U' ∘ φ`.

`renormalizable-thompson-elements-give-baumslag-solitar`, with `k = 2`, then gives `s = U' × id ∈ 3V` and
`u ∈ 3V` with `u s u^-1 = s^m`. `U'` has infinite order by items 1–2 of that criterion, so
`⟨s, u⟩ ≅ BS(1,m)` by the faithfulness argument there. This is the route
`bs13-in-3v-via-smart-renormalization` with `3` replaced by `m`.

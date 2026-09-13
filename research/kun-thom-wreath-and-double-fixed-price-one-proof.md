---
rg: 2
id: kun-thom-wreath-and-double-fixed-price-one-proof
kind: route
title: Start from the lamp group, or from one copy of G, and add elements that commensurate an infinite piece
target: kun-thom-wreath-and-double-have-fixed-price-one
requires: [gaboriau-commensurated-chain-fixed-price-criterion, fpbs-elementary-matrix-semidirect-fixed-price-one]
---

**Wreath.**
- Start with `Γ_1 = ⊕_(G/Γ) Z/2`. It is abelian and normal in `W`, and infinite because
  `[G:Γ]` is infinite (`kun-thom-wreath-l2-acyclic-proof`).
- Add generators of `G` one at a time. Each normalizes `Γ_1`, so its conjugate meets the current
  stage in at least `Γ_1`. Criterion VI.24(3) applies.

**Double.** Write `G, G'` for the two copies, with `G ∩ G' = Γ` in `D`.
- **Stage one.** The chain of `fpbs-elementary-matrix-semidirect-fixed-price-one-proof` builds `G`
  from one root subgroup, and its steps satisfy the criterion's condition. The condition
  concerns subgroups of `G`, so it holds verbatim inside `D`.
- **Stage two.** Add the root elements `x'_ij(a)` of `G'`, `a in F_q[x^±]`. Each commutes with
  `x'_ij(F_q[x_1..x_d]) = x_ij(F_q[x_1..x_d]) ⊆ Γ`, which is infinite and already present.
- **Stage three.** Add the generators of `SL_d(Z)'`. After stage two the current group contains
  `EL_r(F_q[x^±])'`, which every such generator normalizes.
- The union is `D`, since `G` and `G'` generate it, and criterion VI.24(3) applies.

---
rg: 2
id: cograph-raags-are-rips-type-r-proof
kind: route
title: Cograph RAAGs are of Rips type R because their Salvetti covers have the Jensen–Helly property
target: cograph-raags-are-rips-type-r
requires:
  - jensen-helly-graphs-have-contractible-rips-complexes
  - cograph-salvetti-covers-have-the-jensen-helly-property
---

The Cayley graph of `(A_Γ, V(Γ))` is the 1-skeleton of `X_Γ`. It has degree
`2|V(Γ)|`, and its path metric on vertices is the standard word metric. By
`cograph-salvetti-covers-have-the-jensen-helly-property`, `X_Γ` has the
Jensen–Helly property of dimension `k`. By
`jensen-helly-graphs-have-contractible-rips-complexes`, `R_t(A_Γ, V(Γ))` is
contractible for every integer `t ≥ k(k+1) − 1`.

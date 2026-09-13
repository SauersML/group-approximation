---
rg: 2
id: every-raag-is-rips-type-r-via-jensen-helly
kind: route
title: All RAAGs are of Rips type R if their Salvetti covers have the Jensen–Helly property
target: every-raag-is-rips-type-r
requires:
  - jensen-helly-graphs-have-contractible-rips-complexes
  - raag-salvetti-covers-have-the-jensen-helly-property
---

The Cayley graph of `(A_Γ, V(Γ))` has degree `2|V(Γ)|`, so it has bounded
degree, and its path metric on vertices is the standard word metric. If it has
the Jensen–Helly property of dimension `k` (the clique number of `Γ`), then
`jensen-helly-graphs-have-contractible-rips-complexes` makes `R_t(A_Γ, V(Γ))`
contractible for all `t ≥ k(k+1) − 1`, for every finite `Γ`. That is
`every-raag-is-rips-type-r`.

This is a genuine reduction and not a restatement. The prerequisite is a
metric-geometric statement about barycentres and Helly numbers in one
realization, and it can fail independently of type R: type R does not imply
Jensen barycentres.

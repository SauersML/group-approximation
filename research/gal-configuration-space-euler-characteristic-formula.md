---
rg: 2
id: gal-configuration-space-euler-characteristic-formula
kind: claim
title: "Gal's product formula for the Euler characteristics of unordered configuration spaces of a graph"
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part3.md
---

For a finite graph `Γ`:
`Σ_{n≥0} χ(UConf_nΓ) t^n = Π_{v∈V(Γ)} (1 + (1 − deg v)t) · (1 − t)^{−|E(Γ)|}`.
This is the graph case of Gal's formula for complexes. A vertex gives the
factor `1 + (1 − deg v)t`, an edge (empty normal link) gives `(1 − t)^{−1}`,
and `χ(UConf_n) = χ(C_n)/n!` because the symmetric group acts freely.

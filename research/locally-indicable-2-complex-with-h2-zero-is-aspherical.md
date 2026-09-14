---
rg: 2
id: locally-indicable-2-complex-with-h2-zero-is-aspherical
kind: claim
title: A connected 2-complex with locally indicable fundamental group and vanishing second homology is aspherical (Howie, as quoted by Barreto--Minian)
distinct_from:
  lot-complexes-with-vanishing-first-l2-betti-are-aspherical: that derives asphericity of LOT complexes from an L²-Betti hypothesis; this derives asphericity of any connected 2-complex from local indicability and H_2 = 0.
  ascending-hnn-one-cell-complements-have-vanishing-l2-b1: that proves asphericity for one-cell complements whose group is an ascending HNN extension; this uses local indicability instead.
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

Imported through `locally-indicable-2-complex-aspherical-citation`.

**Claim.** Let `X` be a connected 2-complex such that `π_1(X)` is locally indicable and
`H_2(X) = 0`. Then `X` is aspherical.

**Use here.** A LOT complex `K(Γ)` has one 0-cell, `n` 1-cells and `n - 1` 2-cells, so
`χ = 0`, and `H_1 = Z`. Its cellular `H_2` is free abelian of rank
`χ - b_0 + b_1 = 0 - 1 + 1 = 0`, so `H_2(K(Γ)) = 0`. Hence local indicability of `G(Γ)`
makes `K(Γ)` aspherical.

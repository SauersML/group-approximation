---
rg: 2
id: burau-faithful-iff-faithful-on-noncentral-normal-subgroup
kind: claim
title: "For n >= 4, the Burau representation of B_n is faithful iff it is faithful on some normal subgroup not contained in the center"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Let `n ≥ 4`, let `ρ_n` be the reduced Burau representation of the braid group `B_n`, and let
`N ⊴ B_n` be a normal subgroup not contained in `Z(B_n) = ⟨Δ²⟩`. Then `ρ_n` is faithful on `B_n`
if and only if its restriction to `N` is faithful.

This is Long's theorem. It is quoted in arXiv:2607.05283v1 (Bharathram–Birman–Brendle,
reference [18]: D. D. Long, *A note on the normal subgroups of mapping class groups*, Math. Proc.
Cambridge Philos. Soc. 99 (1986)) as: the Burau representation is faithful on `B_n` if it is
faithful on any nontrivial noncentral normal subgroup. The statement was not read from Long's paper
here. The route `burau-faithful-iff-faithful-on-noncentral-normal-subgroup-proof` gives an
independent proof for `n ≥ 4`.

The same proof works for any representation of `B_n` that is injective on the center.

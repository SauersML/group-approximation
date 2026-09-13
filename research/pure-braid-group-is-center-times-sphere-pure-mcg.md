---
rg: 2
id: pure-braid-group-is-center-times-sphere-pure-mcg
kind: claim
title: For n >= 3 the pure braid group P_n is Z times the pure mapping class group of the (n+1)-punctured sphere
artifacts:
  - research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md
---

For every `n ≥ 3` there is an isomorphism `P_n ≅ Z × PMod(S_{0,n+1})`, in which the `Z` factor is the center
`⟨Δ²⟩` of `P_n` and a complement is the kernel of the homomorphism `P_n → P_2 ≅ Z` that deletes strands
`3, …, n`.

Standard. The derivation is Proposition A of
`research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md` (§3): the strand-deleting map sends the
full twist to a generator of `P_2`, so the center is a direct factor, and `P_n/Z(P_n) ≅ PMod(S_{0,n+1})` by
capping the boundary of the `n`-marked disk.

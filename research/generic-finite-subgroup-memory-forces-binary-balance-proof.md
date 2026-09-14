---
rg: 2
id: generic-finite-subgroup-memory-forces-binary-balance-proof
kind: route
title: Hide a perturbation on the subgroup from outside blocks; injectivity makes the inside block map a bijection
target: generic-finite-subgroup-memory-forces-binary-balance
requires: []
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

The proof is Proposition 9 of the artifact, Section 3. Suppose `mu` is unbalanced.

- **Every address has an insensitive context.** If every context at an address were sensitive, `mu`
  would have weight `2^(|M|-1)`.
- **Blocks in `K` have distinct context sites.** If `hm = h'm'` with `h, h'` in `K` and `m, m'` in
  `M \ K`, then `m' ∈ Km`. Condition (G1) gives `m = m'` and `h = h'`.
- **Outside blocks read `K` once.** If `h` is not in `K` and `hm, hm'` are both in `K`, then `m^-1 m'`
  is in `K`, so `m' ∈ mK` and (G1) gives `m = m'`.
- **The perturbation.** Change the configuration on `K`, and give each outside block an insensitive
  context at its private sites (G2). Then the only outputs that can change are those of the blocks in
  `K`. Injectivity makes the resulting map of `{0,1}^K` injective, hence a bijection for every choice
  of contexts.
- **Balance.** Its coordinate at `h = 1` balances `mu(., r)` for every context `r`, so `mu` is
  balanced.

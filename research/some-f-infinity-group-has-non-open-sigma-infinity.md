---
rg: 2
id: some-f-infinity-group-has-non-open-sigma-infinity
kind: claim
title: "Some group G of type F_infinity has Sigma^infinity(G) not open in the character sphere"
---

There is a group `G` of type `F_∞` such that
`Σ^∞(G) = ∩_{n ≥ 1} Σ^n(G)` is not an open subset of the character sphere
`S(G)`. Here `Σ^n(G)` is the homotopical Bieri–Neumann–Strebel–Renz invariant.

This is the negative answer to Zaremsky Problem 1.13
(`zaremsky-1-13-sigma-infinity-is-open`).

## Attempts

- Necessary shape (2026-09-13, established): a witness needs a character
  `χ ∈ Σ^∞(G)` approached by characters `ψ_k ∉ Σ^∞(G)` whose depths
  `min{n : ψ_k ∉ Σ^n(G)}` are finite and tend to infinity
  (`non-open-sigma-infinity-needs-unbounded-sigma-depth`), and `G` must have
  infinite cohomological dimension
  (`bnsr-invariants-stabilize-at-cohomological-dimension`).
- Products of known groups: dead, since depth is additive under direct
  products (artifact §3, M1).
- Two-ended Thompson-like groups (`F`, `F_{n,∞}`, `F_τ`): dead, their invariants
  stabilize at `m = 2` (artifact §2 and §3, M2).
- Open leads (artifact §3): arithmetic depth along rational directions of a
  rank-2 slope group (M3), tropical jump loci whose slopes accumulate (M4), pure
  braided Thompson groups containing every pure braid group (M5).

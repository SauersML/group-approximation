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

- Necessary shape (2026-09-13, established in
  `non-open-sigma-infinity-needs-unbounded-sigma-depth`): a witness needs a
  character `χ ∈ Σ^∞(G)` approached by characters `ψ_k ∉ Σ^∞(G)` whose depths
  `min{n : ψ_k ∉ Σ^n(G)}` are finite and tend to infinity. So the invariants
  `Σ^n(G)` must take infinitely many distinct values, and `G` must be
  infinite-dimensional in the sense of the stabilization results for groups with
  finite classifying spaces. No such group is known to this lane yet.

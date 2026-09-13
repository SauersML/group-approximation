---
rg: 2
id: f-infinity-group-with-properly-nested-bnsr-invariants
kind: claim
title: "Some group G of type F_infinity has Sigma^m(G) properly containing Sigma^{m+1}(G) for every m >= 1"
distinct_from:
  zaremsky-1-18-properly-nested-bnsr-invariants: that claim is Problem 1.18 as a question, established by either answer; this is the affirmative answer, an existence statement about one group
artifacts:
  - research/artifacts/zp-properly-nested-bnsr-2026-09-13-part1.md
---

There is a group `G` of type `F_∞` whose homotopical BNSR invariants satisfy
`Σ^1(G) ⊋ Σ^2(G) ⊋ Σ^3(G) ⊋ ⋯`, every inclusion proper.

## Attempts

- **Necessary conditions so far.**
  - `G` is not of type F (`type-f-bnsr-invariants-stabilize-at-dimension`,
    established).
  - `G` fails the Bieri Σ-property (`bieri-sigma-property-forces-bnsr-constant-from-rank`,
    established).
  - `G` should have infinite cohomological dimension: Proposition 1 of the
    artifact, via the Novikov criterion and the Bieri–Renz comparison, both
    still to verify from sources.
- **A sufficient condition through coabelian subgroups (verified import).**
  Zaremsky, arXiv:1502.02620, Citation 1.2 (from Bieri–Geoghegan–Kochloukova):
  for `G` of type `F_m` and `N ◁ G` containing `[G,G]`, `N` is of type `F_m`
  iff `[χ] ∈ Σ^m(G)` for every `χ` vanishing on `N`. So it suffices that, for
  each `k`, some `N_k ⊇ [G,G]` is of type `F_k` but not `F_{k+1}`.
- **Computed infinite-dimensional examples stop at level 2 (verified from the
  sources).**
  - Thompson's `F`: `Σ^2(F) = Σ^∞(F)` (arXiv:1501.06682, Theorem A).
  - `F_{n,∞}`: `Σ^m(F_{n,∞}) = Σ^2(F_{n,∞})` for `n, m ≥ 2` (arXiv:1502.02620,
    Theorem A).
  - The Stein group `F_{2,3}`: `Σ^m = Σ^2` for `m ≥ 2` (arXiv:2012.05000,
    Theorem 3.9). Spahn–Zaremsky conjecture the same three-level shape for all
    Stein groups `F_S^r` (§4.1) and remark "it is notable how often Σ²=Σ^∞
    holds for globally defined Thompson-like groups".
  - The Lodha–Moore groups: all higher invariants equal `Σ^2`
    (arXiv:2007.12518, abstract).
  - Finite-dimensional examples realize long finite chains: Houghton groups `H_n`
    give levels `1, …, n−1` (arXiv:1808.00634, Theorems 2.2 and 2.3), and the
    pure symmetric automorphism groups `PΣAut_n` have characters in
    `Σ^{n−2} \ Σ^{n−1}` (arXiv:1607.03043).
- **Why product and germ mechanisms stall (artifact §5).**
  - Joins and convex hulls: conic Carathéodory bounds the number of levels.
  - Germ characters of Thompson-like groups: self-embeddings act on germ
    characters with finite orbits.
  - Permutational wreath products `A ≀_X F` of type `F_∞`: heuristically, few
    lamps control the level.
- **Calibration (artifact §4).** Chain length is not bounded by the rank of
  `G^{ab}`. Products of cyclically permuted powers of `F_2` give proper chains
  of length `2^k − 1` at rank `3k`, using the Meier–Meinert–VanWyk criterion
  (statement to verify). They violate the Bieri Σ-property through weighted
  levels and killer elements, and are finite dimensional.
- **Architecture that would answer yes (artifact §6).** Infinitely many
  blocks sharing a fixed finite-rank character space, block `n` activating at
  level `n` and killed exactly off a line `ker c_n`, with pairwise
  non-proportional killer directions. The complements `S \ Σ^m` would be
  growing finite sets. Their accumulation would also make `Σ^∞` non-open
  (Problem 1.13). Missing: a finitely generated `F_∞` host, cocompact by
  self-similarity or an oligomorphic action, and an exact local-to-global
  computation of `Σ^m` in both directions.

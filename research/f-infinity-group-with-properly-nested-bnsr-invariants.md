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

- **Necessary condition, infinite cohomological dimension (argument written,
  imports not yet verified from sources).** Let `G` be of type `F_∞` with
  `cd G = d < ∞`, so `G` is of type FP. Import (a), the Novikov-homology
  criterion (Sikorav for `m = 1`, Bieri for general `m`; exact reference to
  verify): for `G` of type `FP_m`, `[χ] ∈ Σ^m(G;Z)` iff
  `Tor_i^{ZG}(\widehat{ZG}_{−χ}, Z) = 0` for `0 ≤ i ≤ m`. Because
  `pd_{ZG} Z = d`, every such Tor vanishes for `i > d`. So
  `Σ^m(G;Z) = Σ^d(G;Z)` for all `m ≥ d`. Import (b) (Bieri–Renz; reference to
  verify): `Σ^m(G) = Σ^2(G) ∩ Σ^m(G;Z)` for `m ≥ 2`. Hence
  `Σ^m(G) = Σ^{max(2,d)}(G)` for every `m ≥ max(2,d)`, and the chain is
  constant from there on. A group answering Problem 1.18 therefore has
  infinite cohomological dimension, like Thompson's group `F`.
- **A sufficient condition through coabelian subgroups.** Import (c) (Renz;
  Bieri–Renz; reference to verify): if `N ◁ G`, `G/N` is abelian and `G` is of
  type `F_m`, then `N` is of type `F_m` iff `S(G,N) ⊆ Σ^m(G)`, where `S(G,N)`
  is the subsphere of characters vanishing on `N`. So it suffices to find `G`
  of type `F_∞` such that, for each `k ≥ 1`, some `N_k ◁ G` with abelian
  quotient is of type `F_k` but not `F_{k+1}`. Then `S(G,N_k) ⊆ Σ^k(G)` and
  `S(G,N_k) ⊄ Σ^{k+1}(G)`, so `Σ^k(G) ≠ Σ^{k+1}(G)`. Since `G^{ab}` has
  finite rank, this asks for coabelian subgroups of every finiteness level
  inside one lattice of sublattices of `Z^r`.
- **Known infinite-dimensional computations stop early (to verify against the
  sources).** Bieri–Geoghegan–Kochloukova computed `Σ^m(F)` and found
  `Σ^2(F) = Σ^∞(F)`. Zaremsky (arXiv:1502.02620) computed `Σ^m(F_{n,∞})` for
  all `m, n` by Morse theory on Stein–Farley cube complexes. Still to check:
  Spahn–Zaremsky on the Stein groups, Lodha–Moore groups, pure braided
  Thompson groups.
- **Why product and germ mechanisms stall.** In products the complements
  `S \ Σ^m` grow by spherical joins (the product formula; Bieri–Geoghegan over
  fields). In Thompson-like groups characters are logarithms of germs at global
  fixed points, and self-embeddings act on germ characters by projections or
  permutations, which have finite orbits. Both give finitely many levels in a
  fixed group. A positive answer needs a mechanism where a fixed finite-rank
  character space sees supports of unbounded size.
- **Calibration: proper-chain length is not bounded by `rank G^{ab}`.** For
  `B_n = F_2^n ⋊ Z` with `Z` permuting the factors cyclically,
  `Hom(B_n,R) = R^3` (diagonal characters plus the `Z` coordinate). By the
  finite-index transfer to the right-angled Artin group `F_2^n × Z` and the
  Meier–Meinert–VanWyk criterion, a diagonal character with zero `Z`
  coordinate lies in `Σ^{n−1} \ Σ^n`, and a character with nonzero `Z`
  coordinate lies in `Σ^∞`. Products `B_1 × B_2 × B_4 × ⋯ × B_{2^{k−1}}` then
  realize every level `1, …, 2^k − 1` (subset sums) at rank `3k`. The finite
  cohomological dimension bounds all such examples.

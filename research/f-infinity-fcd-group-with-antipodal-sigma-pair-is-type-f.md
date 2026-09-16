---
rg: 2
id: f-infinity-fcd-group-with-antipodal-sigma-pair-is-type-f
kind: claim
title: "An F_infinity group of finite cd d with an antipodal pair in Sigma^d(G;Z) is of type F with zero K_0 Euler class"
distinct_from:
  nonzero-euler-characteristic-blocks-symmetric-sigma: that assumes type F and uses only the integer e(G) to forbid antipodal pairs; this assumes only F_infinity with finite cd and concludes type F and vanishing of the whole class chi_G in K_0(ZG), so it restricts counterexamples to Problem 1.21
  graph-braid-nonzero-euler-characteristic-sigma-asymmetric: that is the graph braid group application of the e(G) obstruction; this is a general finiteness theorem for F_infinity groups of finite cd
  f-infinity-groups-of-finite-cd-are-of-type-f: that is the open hole for every F_infinity group of finite cd; this proves it under the extra hypothesis of an antipodal pair of BNSR classes
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Let `G` be of type `F_∞` with `cd G = d`, `1 ≤ d < ∞`. Suppose some character
class `[χ]` has both `[χ]` and `[−χ]` in the homological BNSR invariant
`Σ^d(G;Z)`. It suffices that they lie in `Σ^d(G)`, or in `Σ^m(G)` for some
`m ≥ d`, or in `Σ^∞(G)`. Then:

- `G` is of type F;
- `χ_G = 0` in `K_0(ZG)`, so `σ(G) = 0` and `e(G) = 0`;
- some epimorphism `G → Z` has a kernel of type FP.

Consequences for a counterexample `G` to Problem 1.21
(`f-infinity-groups-of-finite-cd-are-of-type-f`), with `d = cd G`:

- `Σ^d(G;Z) ∩ −Σ^d(G;Z) = ∅`, so `Σ^∞(G)` contains no antipodal pair;
- if some automorphism of `G` acts as `−1` on `Hom(G,R)`, then
  `Σ^d(G;Z) = ∅`.

Model tests:

- `G = Z^n`: `Σ^∞ = S^{n−1}` is symmetric, and `G` is of type F.
- `G = B × Z` with `B` finitely presented of type FP: the projection
  character has `±χ ∈ Σ^∞`, and `G` is of type F, consistent with
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`.
- `F_2`: `Σ^1 = ∅`, and indeed no antipodal pair, since `e = −1 ≠ 0`
  (`nonzero-euler-characteristic-blocks-symmetric-sigma`).

Proof: `antipodal-sigma-pair-type-f-proof`.

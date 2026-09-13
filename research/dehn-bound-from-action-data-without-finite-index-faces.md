---
rg: 2
id: dehn-bound-from-action-data-without-finite-index-faces
kind: claim
title: "The Llosa Isenrich–Weis Dehn function bound holds for cocompact actions on simply connected complexes with no finite-index hypothesis on face stabilizers"
distinct_from:
  llosa-isenrich-weis-dehn-bound-for-cocompact-actions: that proves the bound for trees and for complexes whose 2-cell stabilizers have finite index in their edge stabilizers; this asserts it with no hypothesis on 2-cell stabilizers, measuring distortion over all cells of dimension at most 2.
---

**Statement (open).** Let `G` act cellularly, cocompactly and without
inversions on a simply connected simplicial complex `X` with `δ_X(n) < ∞` for
all `n`, finitely presented vertex stabilizers and finitely generated edge
stabilizers. Let `dist_X(n) = max { dist^G_{G_σ}(n) : dim σ ≤ 2 }`. Then

```text
δ_G(n) ≼ δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) ).
```

This is the upper-bound reading of Zaremsky Problem 1.17
(`zaremsky-1-17-dehn-function-from-cocompact-action-data`, route
`zaremsky-1-17-by-yes`).

## Attempts

- Lifting a van Kampen diagram over `X` to `G` gives, on each interior edge
  `e`, a discrepancy element of `G_e`. When `[G_e : G_σ] < ∞`, each face lift
  can be chosen so that the discrepancies are coset representatives of bounded
  length; this is where the finite-index hypothesis should enter Llosa
  Isenrich–Weis §3 (still to check against their proof). Without it, a
  discrepancy `h ∈ G_e \ G_σ` has to be carried through the vertex groups at
  the corners of `σ`, and its length is controlled only by distortion of
  intersections of stabilizers. Whether distortion over cells of dimension
  ≤ 2 is enough is the open point.
- 2026-09-13, after reading pp. 10–14 of arXiv:2608.07191
  (`research/artifacts/zp-dehn-cocompact-face-collapse-2026-09-13.md`): the
  hypothesis enters only through Lemma 3.4, the face collapse, whose cost
  without it is `min_{s ∈ G_σ} d_{G_e}(p, ψ_{e,σ}(s))`, the distance from the
  loop to the disks over `σ`. Loop length does not bound that distance. A proof
  has to choose `G`-close fillings; the candidate controlling datum is the
  corner coarse-intersection function `κ_X` of pairs of edge stabilizers
  inside vertex stabilizers. It is bounded under finite index and linear for
  products of trees.
- 2026-09-13 (`research/artifacts/zp-dehn-cocompact-face-collapse-2026-09-13-part2.md`):
  Lemma 3.4 holds with the detour `d_{EG_e}(γ(0), ψ_{e,σ}(G_σ))`, so `X̂` is
  simply connected and `δ_G ≃ δ_{X̂}` in general. By the accounting corollary,
  this claim holds once some filling of area `≼ δ_X(n)` has detours bounded by
  the stated data. With trivial face stabilizers the detours are twists
  forming relations among edge-stabilizer elements in `G_w` around interior
  vertices. A bounded-twist filling lemma is the missing step.

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

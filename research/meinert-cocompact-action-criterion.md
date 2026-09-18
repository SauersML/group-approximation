---
rg: 2
id: meinert-cocompact-action-criterion
kind: claim
title: Meinert's cocompact-action criterion for Sigma^m, with finite-index and conjugation invariance of the invariants
distinct_from:
  germ-complex-and-bux-gonzalez-morse-inputs: that imports the Bux–Gonzalez criterion, which needs every cell stabilizer in ker(chi); this imports the criterion for the opposite case, where chi is nonzero on every cell stabilizer.
  characters-living-on-m-plus-one-factors-lie-in-sigma-m: that imports Meinert's product inequality; this imports Meinert's cocompact-action criterion.
---

**ESTABLISHED by citation (route `meinert-cocompact-action-criterion-citation`; unreviewed).**

**(MMV)** Let `G` act cocompactly on an `(m−1)`-connected complex `X`, and let `χ in Hom(G,R)`. Suppose that:

- `χ|_{Stab_G(σ)} != 0` for every cell `σ` with `dim σ <= m`;
- for every cell `σ` with `dim σ < m`, `Stab_G(σ)` has type `F_{m−dim σ}` and
  `[χ|_{Stab_G(σ)}] in Σ^{m−dim σ}(Stab_G(σ))`.

Then `[χ] in Σ^m(G)`.

**(Mon)** `Σ^1(G) ⊇ Σ^2(G) ⊇ ...`.

**(FI)** Let `H` have type `F_m`, let `H' <= H` have finite index and let `χ in Hom(H,R)` be nonzero. Then
`[χ] in Σ^m(H)` iff `[χ|_{H'}] in Σ^m(H')`.

**(Conj)** For `χ in Hom(G,R)`, `H <= G` and `g in G`: `[χ|_H] in Σ^m(H)` iff `[χ|_{gHg^{-1}}] in Σ^m(gHg^{-1})`.

(FI) and (Conj) are derived in the route from the definition of `Σ^m`.

## Attempts

- Imported for `germ-extension-base-nontrivial-characters-via-point-fixers`.

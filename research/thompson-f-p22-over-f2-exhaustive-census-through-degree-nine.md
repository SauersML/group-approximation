---
rg: 2
id: thompson-f-p22-over-f2-exhaustive-census-through-degree-nine
kind: claim
title: Over F_2, exactly 76830 of the 130305 pairs in Guba's Problem P_(2,2) for Thompson's F have no nonzero common right multiple of degree at most nine
distinct_from:
  thompson-f-p22-over-f2-exhaustive-degree-seven-census: that stops at degree seven; this reproduces that census exactly with an independent implementation and extends the exact count to degrees eight and nine.
  thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9: that bounds one explicit integer pair in characteristic 0 and over F_(2^61-1); this is an exhaustive count over F_2 for every pair, in both directions, up to degree nine.
  thompson-f-ore-window-kernel-profiles-monotone-binomial-floor: that describes how kernel dimensions grow once a pair is settled and why profiles cannot certify a non-Ore pair; this counts how many pairs settle in each degree.
artifacts:
  - research/artifacts/hl-f-kernel-profiles-2026-09-14.md
  - research/artifacts/hl-f-kernel-profiles-2026-09-14-data/census_compare.json
  - research/artifacts/hl-f-kernel-profiles-2026-09-14-data/s35_unsolved_after_k9.json.gz
---

**ESTABLISHED** through `thompson-f-p22-over-f2-census-through-degree-nine-proof` (exhaustive exact
computation; not independently reviewed; no priority claimed).

Notation as in `thompson-f-p22-over-f2-exhaustive-degree-seven-census`:
- `S_(3,5)` is the set of nine monomials of Guba's Problem `P_(2,2)`;
- the pairs are the 130305 unordered pairs of distinct nonzero `a, b ∈ F_2[S_(3,5)]`;
- `δ(a, b)` is the least degree of nonzero homogeneous `u, v ∈ F_2[M]` with `a u = b v`, or `∞`.

1. **Degrees eight and nine.** Exactly 8880 pairs have `δ = 8`, and exactly 8619 have `δ = 9`.
2. **Survivors.** The remaining 76830 pairs have `δ > 9`, i.e. no nonzero common right multiple of degree
   `<= 9`. Their list is `s35_unsolved_after_k9.json.gz`, in the bitmask convention of the degree-seven census.
3. **Planes.** `δ(a, b)` depends only on the plane `{0, a, b, a + b}`, so every count is three times a count
   of planes. Of the 43435 two-dimensional subspaces of `F_2[S_(3,5)]`, 2960 settle at degree 8, 2873 at
   degree 9, and 25610 have `δ > 9`.
4. **Reproduction.** Through degree seven, both the per-degree counts and the survivor list agree exactly with
   the landed census.

**Growth.** The fraction of surviving pairs that settle in the next degree does not decay:
- 7.85% at degree 7, of 102366 survivors;
- 9.41% at degree 8, of 94329;
- 10.09% at degree 9, of 85449.

This is evidence about how survivors settle. It says nothing about whether some pair never settles.

**Relation to the root.** A finite computation only settles pairs positively, so this proves nothing about
`thompson-f-is-amenable` or `thompson-f-is-not-amenable`. The 76830 pairs are the remaining `F_2` candidates
for a non-Ore pair of `P_(2,2)`, by Guba's alternative as recorded in the degree-seven census.

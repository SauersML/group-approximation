---
rg: 2
id: fpbs-generating-sets-connected-by-product-moves-proof
kind: route
title: Grow along geodesic prefixes, then remove in decreasing word length
target: fpbs-generating-sets-connected-by-product-moves
requires: []
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

Write `|x|_S` for the word length over `S`. Since `S` is symmetric,
`|x^{-1}|_S = |x|_S`.

**Phase 1: add `S'`.**
- For `s' in S' \ S`, take an `S`-geodesic word `a_1 ... a_l`. Its length is
  `l >= 2`, since `l = 1` would put `s'` in `S` and `l = 0` would mean `s' = e`.
- Add the prefixes `P_j = P_{j-1} a_j` for `j = 2, ..., l`, skipping any already
  present.
- Each Add move is legal: both factors are present, and `P_j != e` because
  `|P_j|_S = j`.

**Phase 2: remove the auxiliary prefixes.** These are the added elements not in
`S ∪ S'`. Remove them in decreasing `|.|_S`. When removing `P_j`:
- `P_{j-1}` is still present, because it is strictly shorter;
- `a_j in S` is present;
- `a_j != P_j^{±1}`, since otherwise `P_j` would lie in `S`;
- `P_{j-1} != P_j^{±1}`, since their word lengths differ.

Removal needs only strictly shorter elements, so removing `P_j^{-1}` together
with `P_j` does not block later steps.

**Phase 3: remove `S \ S'`.**
- For each `s in S \ S'`, add the prefixes of an `S'`-geodesic word for `s`, as
  in Phase 1.
- Then remove every element of `S \ S'`, and every auxiliary that is not in
  `S'`, in decreasing `|.|_{S'}`. Each has length at least 2, since length 1
  would put it in `S'`.
- Each such element is `Q_{j-1} b_j`, with `b_j in S'` and `Q_{j-1}` strictly
  shorter, so both factors are still present.
- Neither factor is the removed element or its inverse, by the same length
  argument as in Phase 2.

What remains is exactly `S'`. Every intermediate set is admissible: Add keeps
generation trivially, and Remove keeps it because the removed element is a
product of remaining ones.

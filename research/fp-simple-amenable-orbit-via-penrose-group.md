---
rg: 2
id: fp-simple-amenable-orbit-via-penrose-group
kind: route
title: A finitely presented derived Penrose tiling group is an amenable-orbit realization
target: fp-simple-group-in-amenable-orbit-full-group
requires:
  - penrose-tiling-group-is-an-amenable-orbit-full-group
  - penrose-derived-full-group-is-finitely-presented
---

Let `S = D(𝒫)`, `Lambda = P/<w_1, w_2> ≅ Z^2 ⊕ Z/5Z`, `X = C~/<w_1, w_2>` and `mu`
be as in `penrose-tiling-group-is-an-amenable-orbit-full-group`.

1. `Lambda` is countable and amenable. It acts freely on `X`, preserving `mu`
   (item 2 there).
2. `S` is finitely generated, infinite and simple (items 1 and 3 there), and
   `S ≤ [[Lambda ~ X]] ≤ W(Lambda ~ X)`.
3. A nontrivial element of `S` moves a nonempty open set, which has positive
   measure by full support. So the inclusion is nontrivial on a set of positive
   measure.
4. `S` is finitely presented by `penrose-derived-full-group-is-finitely-presented`.

So `S` witnesses `fp-simple-group-in-amenable-orbit-full-group`. This is a second
instance, independent of `fp-simple-amenable-orbit-via-labbe-shift`: the root
`hyperlinear-fp-infinite-simple-group` would follow from finite presentation of
either group.

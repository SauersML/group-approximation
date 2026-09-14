---
rg: 2
id: subshift-el3-f2-iso-soe-via-standard-isomorphisms
kind: route
title: A standard isomorphism of the binary subshift groups gives an isomorphism or anti-isomorphism of 3x3 matrix rings, which forces strong orbit equivalence
target: subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence
requires:
  - subshift-el3-isomorphisms-are-standard-over-f2
  - cantor-crossed-product-matrix-ring-iso-forces-soe
---

Let `α: G_X → G_Y` be an isomorphism.
1. By `subshift-el3-isomorphisms-are-standard-over-f2` (open), `α` comes from a ring isomorphism or anti-isomorphism
   `M_3(LC(X,F_2) ⋊ Z) → M_3(LC(Y,F_2) ⋊ Z)`.
2. By `cantor-crossed-product-matrix-ring-iso-forces-soe` (Theorem R, with `m = 3` and `k = k' = F_2`), such a ring
   isomorphism or anti-isomorphism forces `X` and `Y` to be strongly orbit equivalent. ∎

Only step 1 is open, so this route is live but incomplete.

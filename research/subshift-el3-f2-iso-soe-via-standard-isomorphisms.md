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
1. By `subshift-el3-isomorphisms-are-standard-over-f2` (established through Theorem D; sk-verify-25a and sk-verify-25b
   PASS-WITH-FIXES), `α` comes from a ring isomorphism or anti-isomorphism
   `M_3(LC(X,F_2) ⋊ Z) → M_3(LC(Y,F_2) ⋊ Z)`. By Fix W3 it is `inn(k)∘M_3(φ)`, possibly after the graph automorphism,
   for a ring isomorphism `φ: R_X → R_Y`.
2. By `cantor-crossed-product-matrix-ring-iso-forces-soe` (Theorem R, with `m = 3`, or `m = 1` after Fix W3, and
   `k = k' = F_2`), such a ring isomorphism or anti-isomorphism forces `X` and `Y` to be strongly orbit equivalent. ∎

Both steps are established, so the route is complete (sk-rigidity-merge, 2026-09-14).

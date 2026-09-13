---
rg: 2
id: zp-detection-from-strong-approximate-innerness
kind: route
title: If every outer Z/p-action on O_2 is strongly approximately inner, Izumi's theorem makes each phantom candidate approximately representable, its dual Rokhlin, and hence the candidate contractible
target: zp-restriction-and-crossed-product-detect-kk-g-contractibility
requires:
  - outer-zp-actions-on-o2-are-strongly-approximately-inner
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
  - izumi-rokhlin-approximately-representable-duality
---

**What the route does.**  It is the converse of
`outer-zp-actions-on-o2-strongly-approx-inner-via-detection`.  With both
routes, the detection claim and
`outer-zp-actions-on-o2-are-strongly-approximately-inner` are equivalent in the
graph.  Barlak--Li II, Remark 4.14(2), records the latter as unknown for
`Z_2`.

`zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner`, item 4, derives
detection from the stronger hypothesis of asymptotic innerness by
asymptotically invariant unitary paths.  This route needs only Izumi's
sequential strong approximate innerness, because it goes through the Rokhlin
property of the dual action instead of the uniqueness theorem.

**Derivation.**  Let `p` be prime, `G = Z/p`, and let `D` be a separable
nuclear `G`-algebra with `Res D ≃_KK 0` and `D ⋊ G ≃_KK 0`.
1. By item 3 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, `D` is
   KK^G-equivalent to a pointwise outer action `α : G ↷ O_2` with
   `O_2 ⋊_α G ≃_KK D ⋊ G ≃ 0`.
2. By the hypothesis, `α` is strongly approximately inner.  By item 3 of
   `izumi-rokhlin-approximately-representable-duality` (Izumi I, Theorem 4.6,
   for `q = p` a prime power), `α` is approximately representable.
3. By item 4 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, an outer
   approximately representable action on `O_2` with KK-contractible crossed
   product is KK^G-contractible.  Unwound: `α̂` is Rokhlin on
   `O_2 ⋊_α G ≅ O_2`, so it absorbs `id_(O_2)` and is contractible, and Takai
   duality carries this back to `α`.
4. So `D ≃_(KK^G) (O_2, α) ≃ 0`.

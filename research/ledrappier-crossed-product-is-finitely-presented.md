---
rg: 2
id: ledrappier-crossed-product-is-finitely-presented
kind: claim
title: Ledrappier's shift is quantum rigid, so its crossed-product algebra over a field with p-th roots of unity is finitely presented
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that is the entropy obstruction to finite presentation; this is the calibration showing that a zero-entropy SFT can have a finitely presented crossed product.
  labbe-wang-shift-crossed-product-is-finitely-presented: that is the open rigidity question for a minimal aperiodic SFT; this settles it for a permutive SFT with fixed points, whose crossed product is not simple.
---

**ESTABLISHED (unreviewed).** Let `p` be a prime and
`X_L = {x ∈ F_p^(Z^2) : x(z + e_2) = x(z) + x(z + e_1)}`. Let `k` be a field with
`p != char k` that contains a primitive `p`-th root of unity. Then `X_L` is `1`-quantum rigid, so
`LC(X_L, k) ⋊ Z^2` is finitely presented.

**Mechanism.** With `X(z) = sum_a zeta^a E_a(z)`, the local rules give
`X(z + e_2) = X(z) X(z + e_1)`. Commutation in the row above at distance `j - 1`, together with
commutation at distances `1` and `j - 1` in the row itself, gives commutation at distance `j`
(`abcd = cdab` gives `ad = da`). Rows commute at every distance. Upward determination then
extends this to all pairs.

**Consistency.** By Fourier transform, the algebra is the group algebra of
`F_p[t^(±1), (1+t)^(-1)] ⋊ Z^2`. That is a lamp quotient of Baumslag's finitely presented
metabelian group. Its finite presentation is recalled here, not re-read.

**What it teaches the ring route.** Rigidity comes from permutive propagation of commutation. This
shift has a fixed point, so its crossed product is not simple. A usable coefficient ring needs the
same propagation with no periodic point at all.

Route: `ledrappier-crossed-product-is-finitely-presented-proof`.

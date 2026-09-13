---
rg: 2
id: zero-entropy-subshift-pestov-ring-has-rank-model-by-growth
kind: claim
title: For a zero-entropy minimal subshift the Pestov coefficient ring has GK dimension bounded by growth of complexity, so it has a rank model with no towers
---

**ESTABLISHED (unreviewed).** Let `X ⊆ A^Z` be an infinite minimal subshift with word complexity `p(n)` of
subexponential growth, equivalently of zero topological entropy, and let `R = LC(X, F_q) ⋊_T Z` be the
Pestov 9.1 coefficient ring. Then `R` has subexponential growth, hence a unital rank model over `F_q`, hence
is stably finite. For a Sturmian `X` (`p(n) = n+1`, for instance the Fibonacci subshift) `R` has
Gelfand–Kirillov dimension `2`.

**Point of the claim.** The Pestov 9.1 answer obtains far more for this ring — exact matricial models from
return-word towers, hence LEF, hence sofic. The value here is that the *rank model* half needs none of that
machinery: it follows from word complexity alone, by a one-line growth estimate, and the same argument
applies to coefficient rings with no tower structure. It is therefore a growth-only calibration of rung (Σ)
of `kazhdan-elementary-approximation-type-mirrors-ring-type`.

GK dimension `2` is the least possible for an infinite dimensional affine simple algebra, since affine
algebras of GK dimension `1` are PI, hence finite dimensional when simple and affine.

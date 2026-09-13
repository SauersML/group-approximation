---
rg: 2
id: zero-entropy-subshift-pestov-ring-has-rank-model-by-growth
kind: claim
title: For a zero-entropy minimal subshift the Pestov coefficient ring has GK dimension bounded by growth of complexity, so it has a rank model with no towers
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that gives exact matricial models for every infinite minimal subshift, hence a rank model as well; this reaches only the rank model, but by a growth bound alone.
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

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §2.3): PASS.** The ball
bound `dim R_m ≤ (2m+1)·p(2m+1)` and the GK-dimension value (Bergman's gap theorem, Small–Stafford–Warfield,
Kaplansky) were checked. As a rank model it is subsumed by the exact models of `minimal-subshift-algebra-is-simple-lef-ring`;
the growth-only proof is the content.

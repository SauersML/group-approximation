---
rg: 2
id: subsurface-mapping-class-groups-are-undistorted
kind: claim
title: A cleanly embedded subsurface with no annular complementary components has an undistorted mapping class group
distinct_from:
  once-punctured-mcg-is-lipschitz-retract-of-out-free: that places a surface mapping class group undistortedly inside Out(F_2g); this places a subsurface mapping class group undistortedly inside the mapping class group of the ambient surface.
---

**ESTABLISHED (literature import).**

> **Remark 8.3 (Rafi--Schleimer, arXiv:math/0701719v2).** Suppose that a subsurface Z ⊂ S is cleanly
> embedded and S∖Z has no annuli components. Then the inclusion Z → S induces a quasi-isometric
> embedding on mapping class groups. This follows directly from the summation formula of Masur and
> Minsky (See [MM00], Theorems 7.1, 6.10, and 6.12) and was independently obtained by Hamenstädt
> [Hama, Theorem B, Corollary 4.6].

In their Section 3, a subsurface `Z` is **cleanly embedded** if every component of `∂Z` is either a
boundary component of `S` or an essential, non-peripheral curve in `S`.

**Use on main.** It is applied to the subgroup of `Mod(S)` of classes supported in `Z`, for `S` of
finite type with punctures.

**Injectivity.** When no component of `∂Z` bounds a disk or a once-punctured disk in `S`, and no two
components of `∂Z` are isotopic in `S`, the inclusion homomorphism `Mod(Z) → Mod(S)` (with `∂Z` fixed
pointwise) is injective. This is Farb--Margalit, *A primer on mapping class groups*, Theorem 3.18,
which BFFHZ cite for the same purpose (arXiv:2503.21882v2, proof of Corollary B). The primer's text
was not re-read in this lane.

Nothing is reproved here, and there is no Lean counterpart.

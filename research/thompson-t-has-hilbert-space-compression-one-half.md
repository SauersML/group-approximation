---
rg: 2
id: thompson-t-has-hilbert-space-compression-one-half
kind: claim
title: Thompson's group T has Hilbert space compression and equivariant Hilbert space compression both equal to 1/2
distinct_from:
  thompson-f-has-hilbert-space-compression-one-half: that is the imported Arzhantseva--Guba--Sapir value for the subgroup F; this is the value for the circle group T, which also gives the equivariant exponent through the standard-chart cocycle
  thompson-v-standard-cylinder-charts-are-commensurated: that is the exact caret formula for one commensurated subset of V; this is the metric consequence for T once caret count is compared with word length in T
---

Let `α(T)` be the Hilbert space compression of Thompson's group `T` (definition
as in `thompson-f-has-hilbert-space-compression-one-half`). Let `α*(T)` be the
equivariant compression: the same supremum, but taken only over orbit maps
`g ↦ g·ξ` of affine isometric actions of `T` on Hilbert spaces. Then

`α*(T) = α(T) = 1/2`.

More precisely:

- the standard-chart cocycle `b(g) = 1_{gA} - 1_A` of
  `thompson-v-standard-cylinder-charts-are-commensurated`, restricted to
  `T ⊂ V`, satisfies `‖b(g) - b(h)‖² = 2·c(h^{-1}g)`;
- word length in `T` is at most `K·(c(g) + 1)`;
- `F` is undistorted in `T`.

Here `c` is the caret count of the reduced diagram.

**Why it is recorded (fence for Zaremsky Problem 2.4(c)).** Compression is a
quasi-isometry invariant (Guentner–Kaminker). So a proof of
`thompson-f-is-not-quasi-isometric-to-thompson-t` cannot come from Hilbert space
compression, since `α(T) = α(F) = 1/2`. The same holds for the equivariant
exponent: restricting `b` to `F` gives `α*(F) = 1/2` as well.

Novelty: no source stating `α(T) = 1/2` was located on 2026-09-16 (arXiv title and
abstract searches). The ingredients are classical, so the statement is probably
folklore. It is not claimed as new.

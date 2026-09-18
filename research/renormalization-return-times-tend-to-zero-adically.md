---
rg: 2
id: renormalization-return-times-tend-to-zero-adically
kind: claim
title: A height-m renormalization makes the m-adic phase local at linearly growing depth, and forces every return time to a point to tend to 0 in Z_m
distinct_from:
  renormalization-heights-force-eigenvalue-roots: that says a height-m renormalization makes the eigenvalue group closed under m-th roots; this is the pointwise return-time test and the explicit depth bound, which give finite certificates against a given induced map.
  renormalizable-thompson-elements-are-odometer-codes: that constructs the odometer factor; this reads off its locality and its consequence for return times.
---

**ESTABLISHED (2026-09-18)** through `renormalization-return-times-tend-to-zero-adically-proof`.
Lane proof (gq-nv-obstruct). Reviewed PASS by gq-referee-b, citation and scope lens (fba51b1a0).

**Setting.** Let `T` be a homeomorphism of `X = C^k` with a height-`m` renormalization `(A, φ)` in the
sense of `renormalizable-thompson-elements-give-baumslag-solitar`:
- `X = A ⊔ TA ⊔ ⋯ ⊔ T^{m-1}A` and `T^m A = A`;
- `φ: A → X` is a brick-local homeomorphism with `φ T^m = T φ`.

Write `digit(x) = i` for `x ∈ T^i A`, and `S x = φ T^{-i} x`.

**Statement.**
1. **The factor.** `π(x) = Σ_{j>=0} digit(S^j x) m^j` is continuous, and `π ∘ T = π + 1`
   (`renormalizable-thompson-elements-are-odometer-codes`, item 2).
2. **Depth bound.** Suppose each `T^i A` is a union of bricks of depth `<= D`. Suppose also that the
   maps `φT^{-i}` (`0 <= i < m`) are canonical on bricks and lengthen the needed address by at most `P`,
   meaning the image of a depth-`d` brick inside such a piece is determined by the input's depth-`(d + P)`
   brick. Then `π mod m^j` is constant on bricks of depth `D + (j-1)P`. For a moving-tape machine coded by
   bounded prefix codes, this says `π mod m^j` is a function of the state and the cells within radius
   `a + b·j` of the head, for constants `a, b`.
3. **Return-time test.** If `T^{n_i} y → y` for some point `y` and integers `n_i`, then `n_i → 0` in `Z_m`.
   Hence, if some `y` has returns `T^{n_i} y → y` with `m^j ∤ n_i` for all `i` and a fixed `j`, then `T`
   has **no** height-`m` renormalization.

**Calibration.** For SMART induced on its genuine level-0 moves
(`smart-level-zero-return-map-factors-onto-3-adic-odometer`, `m = 3`), items 1–3 hold, since the factor
is proved.
- Its phase `mod 3^j` is read at radius `j + 2`, which is item 2 with `b = 1`.
- On MSI, the returns of its first genuine configuration (radius 6, `4·10^7` steps) have `n ≡ 0 mod 729`,
  as item 3 requires.
- For the binary-timing machine `M°`, the returns found up to radius 18 violate item 3's condition:
  `n ≡ 4 mod 8`. Item 3 applies only if these returns converge at all radii, which is OPEN. See
  `research/artifacts/gq-gq-nv-obstruct-binary-smart-search.md` §3e.

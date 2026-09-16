---
rg: 2
id: busemann-null-isometries-have-no-boundary-contraction
kind: claim
title: An isometry fixing two boundary points with zero Busemann pseudocharacter contracts no third boundary point onto either
---

**Setting.**
- Let `X` be a metric space, and write `(x|y)_w = (d(x,w) + d(y,w) − d(x,y))/2`. Let `δ ≥ 0` satisfy
  `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all `x, y, z, w ∈ X`.
- Fix `o ∈ X`. A sequence `(y_i)` in `X` converges at infinity if `liminf_{i,j→∞} (y_i|y_j)_o = ∞`.
  Two such sequences `(y_i)`, `(w_j)` are equivalent if `liminf_{i,j→∞} (y_i|w_j)_o = ∞`.
- The sequential boundary `∂X` is the set of equivalence classes. Write `y_i → u` when `(y_i)`
  represents `u`.
- For `u, v ∈ ∂X`, put `(u|v)_o := sup liminf_{i,j→∞} (y_i|w_j)_o`, over all `y_i → u` and `w_j → v`.
- Isometries of `X` act on `∂X` by bijections.

Let `ξ ∈ ∂X` and fix `z_i → ξ`. For an isometry `k` of `X` with `kξ = ξ`, put
`q(k) := limsup_{i→∞} (d(o,z_i) − d(ko,z_i))`.

**(i)** For every group `G` of isometries of `X` fixing `ξ`, the limit `p(k) := lim_{n→∞} q(k^n)/n`
exists for each `k ∈ G`, and `p: G → R` is a homogeneous quasimorphism. Moreover
`|p(k) − q(k)| ≤ 18δ` for all `k ∈ G`. This is the Busemann pseudocharacter of arXiv:2406.12982,
Definition 1.10, with `x = o` and `x_i = z_i`. The value `p(k)` only involves the powers of `k`.

**(ii)** Let `k` be an isometry with `kξ = ξ`, `ka = a` for some `a ∈ ∂X \ {ξ}`, and `p(k) = 0`. Then no
`x ∈ ∂X \ {ξ, a}` satisfies `(k^n x | a)_o → ∞` as `n → +∞`.

Proof: route `busemann-null-isometries-have-no-boundary-contraction-proof`. It is elementary and
uses only the displayed four-point inequality at the base point `o`.

Context.
- arXiv:2406.12982, Citation 1.12, attributes to Manning (Section 4.1) the stronger statement:
  `p(g) ≠ 0` iff `g` is loxodromic.
- Combined with "a parabolic element has exactly one fixed point in ∂X" (same source, before
  Citation 1.1), that statement would give (ii) through ellipticity.
- Neither source argument was read, and this claim does not use them.
- Caprace–Cornulier–Monod–Tessera, arXiv:1202.3585v2, was fetched on 2026-09-16. Its Lemma 3.8 states,
  verbatim up to extraction spacing: "Let Γ act on X by isometries and let ξ be a boundary point. Then
  the (possibly empty) set of hyperbolic isometries in Γ_ξ is {g ∈ Γ_ξ : β_ξ(g) ≠ 0}".
  - Their `β_ξ` is the Busemann quasicharacter of their Proposition 3.7, credited there to Manning
    [Man08, Sec. 4].
  - Their proof is a few lines. It uses a comparison with horokernels and the Morse-type fact that a
    quasi-geodesic orbit gives a hyperbolic isometry. That is prior art for the statement "`p(k) = 0`
    implies `k` is not loxodromic".
  - Part (ii) here is instead proved directly, from the four-point inequality.
- This claim feeds `thompson-f-no-cobounded-qi-h2-action-via-busemann`.

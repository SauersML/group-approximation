---
rg: 2
id: icc-group-out-injects-into-group-factor-out
kind: claim
title: For an ICC group G the natural map Char(G) ⋊ Out(G) → Out(L(G)) is injective
artifacts:
  - research/artifacts/sk-vn-rigidity-2026-09-14.md
---

**ESTABLISHED (import).** Let `G` be a countable ICC group, `Char(G) = Hom(G, T)`, and `Ψ(ρ, δ)` the automorphism of `L(G)` with
`u_g ↦ ρ(g) u_{δ(g)}`. The induced map `Char(G) ⋊ Out(G) → Out(L(G))` is injective.

Source: Chifan–Ioana–Osin–Sun, *Wreath-like products of groups and their von Neumann algebras II: Outer automorphisms*,
arXiv:2304.07457 (Duke Math. J. 175 (2026), no. 2), Proposition `inj` (e-print source l.2048), read at source on MSI.
Route: `icc-group-out-injects-into-group-factor-out-citation`.

For an infinite simple group `G`, the proof specializes as follows. A finite twisted conjugacy class
`{δ(g)hg^{-1}}` has a finite-index stabilizer, and an infinite simple group has no proper finite-index subgroup, so
`δ = Ad(h)`.

## Review
- **sk-verify-18 PASS at source (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part8.md`):** arXiv:2304.07457 e-print l.2048 Proposition `inj` and its proof (Fourier coefficients constant on twisted classes, a finite-index G_h, ICC forces a single support point) and the l.220 remark match verbatim.

---
rg: 2
id: spherical-artin-groups-are-linear-over-q-x-y
kind: claim
title: Every spherical-type Artin group is a finitely generated subgroup of GL_N(Q(x,y))
distinct_from:
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that reduces the permutational Boone--Higman property for spherical types to E_6, E_7, E_8, using Crisp's embedding; this is a linearity statement over one explicit field of transcendence degree 2, using the same embedding.
  algebraic-linear-groups-satisfy-boone-higman: that is the established Boone--Higman theorem over fields algebraic over Q; this places the spherical Artin groups over Q(x,y), which has transcendence degree 2 and so lies outside that theorem.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED (literature import with a one-line assembly).** Let `A(Γ)` be an
Artin group of spherical type. Then for some `N` there is an injective
homomorphism `A(Γ) -> GL_N(Q(x,y))`, where `x, y` are independent
indeterminates. So `A(Γ)` is a finitely generated linear group over a field of
characteristic zero with transcendence degree 2 over `Q`.

**Sources** (L. Paris, *Braid groups and Artin groups*, arXiv:0711.2372, text
extracted on MSI):

1. **The representation.** §6.1 builds, for Γ "of small type and without
   triangle", a `K`-vector space `V` with basis indexed by the positive roots,
   where `K = Q(x,y)`. It is finite-dimensional exactly when Γ is spherical.
2. **Faithfulness.** Corollary 6.5 (Bigelow, Krammer, Digne, Cohen--Wales):
   "Suppose that Γ is of spherical type. Let ˆΦ : GΓ → GL(V) be the homomorphism
   induced by Φ . Then ˆΦ is injective." The types A_n, D_n and E_k are trees
   with all labels 3. So they are of small type without triangle, and
   Corollary 6.5 applies to them.
3. **Reduction to those types.** §6, p. 45, citing Crisp [57]: "any spherical
   type Artin group embeds in a direct product of Artin groups of type An (n≥ 1),
   Dn (n≥ 4), and Ek (k = 6, 7, 8)".

**Assembly.** Embed `A(Γ)` in a finite product of groups of types A, D and E by
(3). Represent each factor faithfully over `Q(x,y)` by (2), and take the block
diagonal sum. That sum is faithful on the product, so it restricts to a faithful
representation of `A(Γ)`.

**Trust.** Crisp's theorem and the primary faithfulness proofs are read through
Paris's survey, not from the primary sources.
- **Primary check (2026-09-12).** Cohen--Wales, arXiv:math/0010204v2, was read
  from the PDF.
  - Theorem 1.1: "Every Artin group of finite type is linear."
  - Theorem 1.2, types A, D and E: coefficients lie in `Z[r,t,r^-1,t^-1]` and
    `V` is free on the positive roots. The representation is faithful after
    `r -> r_0` with `0 < r_0 < 1`.
  - Source (2) is therefore confirmed from a primary source, over a field of
    characteristic zero and transcendence degree 2.
- **Not reached.** Digne, J. Algebra 268 (2003), doi 10.1016/S0021-8693(03)00327-2,
  has no open-access copy and no arXiv version, so it was not read.

The derivation is `spherical-artin-linearity-over-q-x-y-proof`.

---
rg: 2
id: free-product-finite-groups-boundary-simple-kazhdan-not-mf
kind: claim
title: For finite A, B with |A| >= 2 and |B| >= 3, EL_N over LC(∂(A*B), F_q) ⋊ (A*B) mod centre is an infinite fg simple Kazhdan group with no nontrivial MF quotient
distinct_from:
  boundary-action-elementary-simple-kazhdan-not-mf: that is the free group F_d on its boundary; this is a free product of finite groups on the ends of its Bass–Serre tree, e.g. PSL_2(Z) = Z/2 * Z/3, where the acting group is virtually free with torsion.
  p-adic-projective-line-elementary-simple-kazhdan-not-mf: that is the arithmetic family on P^1(Q_p); this is the free-product family on tree ends with trivial edge stabilizers.
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; proof in `free-product-finite-groups-boundary-simple-kazhdan-not-mf-proof`).**

**Setting.**
- `A` and `B` are finite groups with `|A| >= 2` and `|B| >= 3`, and `Γ = A * B`.
- `Ω` is the space of infinite words `x_1 x_2 ...` with letters in `(A \ 1) ∪ (B \ 1)` and consecutive letters in
  different factors, with the product topology. It is the space of ends of the Bass–Serre tree.
- `Γ` acts on `Ω` by concatenation and reduction.
- `q` is a prime power, `N >= 3`, and `R = LC(Ω, F_q) ⋊ Γ`.

**Statement.** `S = EL_N(R)/Z(EL_N(R))` is an infinite, finitely generated, simple group with property (T). Every
homomorphism from `S`, or from `EL_n(R)` for `n >= 2`, to an MF group is trivial.

**Example.** `Γ = PSL_2(Z) = Z/2 * Z/3` acting on the ends of the (2,3)-biregular tree gives
`EL_3(LC(Ω, F_2) ⋊ PSL_2(Z))/Z`.

**Excluded case.** `|A| = |B| = 2` gives `D_∞`, whose boundary has two points and is not Cantor.

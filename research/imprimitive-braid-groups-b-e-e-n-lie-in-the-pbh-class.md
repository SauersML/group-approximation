---
rg: 2
id: imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class
kind: claim
title: The braid group B(e,e,n) of every imprimitive complex reflection group G(e,e,n) lies in B_A and embeds in a finitely presented simple group, including the cases e >= 3, n >= 3 where linearity is open
distinct_from:
  finitely-generated-linear-groups-satisfy-boone-higman: that covers every finitely generated linear group; B(e,e,n) for e >= 3 and n >= 3 is not known to be linear (Marin's conjecture), so this is not a special case of it.
  spherical-artin-groups-satisfy-permutational-boone-higman: that covers the real case e = 2, i.e. A(D_n), through linearity over Q(x,y); this reproves D_n without linearity and adds the non-real family.
  b-tilde-artin-groups-via-one-cone-point-fibration: that fibres over strands plus a puncture, with the cone point as fibre coordinate; this uses the same move with no puncture and a cone point of any order e.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class-proof`.
This is a lane proof, elementary, and not independently reviewed. The bundle is
probably the classical one in Nakamura's proof that these orbit spaces are K(π,1)
(Nakamura 1983, not read). No priority is claimed for it; the Boone--Higman
consequence is the content.

## Statement

For `e >= 2` and `n >= 2`, let `G(e,e,n)` be the imprimitive complex reflection group,
`M = {y ∈ C^n : y_i^e ≠ y_j^e for i ≠ j}` its reflection arrangement complement,
`P(e,e,n) = π_1(M)` its pure braid group, and `B(e,e,n) = π_1(M/G(e,e,n))` its braid
group.

1. `(c, y) ↦ (c + y_1^e, …, c + y_n^e)` is a fibre bundle `C × M -> Conf_n(C)`. Its
   fibre `Σ` is the connected `(Z/e)^n`-cover of `C` branched at `n` points, with
   `χ(Σ) = e^(n−1)(e − n(e−1))`.
2. For `(e, n) ≠ (2, 2)`, `π_1(Σ)` is free of rank `1 − χ(Σ) >= 2`, so
   `1 -> F_(1 − χ) -> P(e,e,n) -> P_n -> 1`.
3. Hence `P(e,e,n)` and `B(e,e,n)` lie in `B_A`, and `B(e,e,n)` embeds in a finitely
   presented simple group. For `(e, n) = (2, 2)`, `B(2,2,2) = Z^2`.

## Context

- `e = 2`: `B(2,2,n) = A(D_n)`, already known (BFFHZ Corollary B; the spherical nodes
  on main). This is a linearity-free proof.
- `n = 2`: `B(e,e,2) = A(I_2(e))`, already known.
- `e >= 3`, `n >= 3`: linearity of `B(e,e,n)` is open (conjectured by Marin; Neaime,
  arXiv:1812.03714, constructs Krammer-type representations and conjectures they are
  faithful). The other imprimitive braid groups `B(de,e,n)`, `d >= 2`, embed in
  `B(de,1,n) ≅ A(B_n)` and are linear. So this family is the one not covered by
  linearity.
  - A bounded search (web, 2026-09-18) found no Boone--Higman statement for complex
    braid groups.

## Why one cone point works and two do not

In the orbifold picture, `M/(Z/e)^n` is `n` strands in `C` with one cone point of
order `e` at `0`, and strands may pass through it. Fibring over the orbifold positions
of the strands, with the cone point as fibre coordinate, makes "strand at the cone
point" a simple branch point of the fibre. Two strands can never be at the cone point
together.

For D̃_n there are two cone points, and the same move leaves a two-dimensional fibre
(`d-tilde-artin-groups-satisfy-permutational-boone-higman`).

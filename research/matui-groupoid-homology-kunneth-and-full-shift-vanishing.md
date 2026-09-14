---
rg: 2
id: matui-groupoid-homology-kunneth-and-full-shift-vanishing
kind: claim
title: "Matui: groupoid homology satisfies a Künneth formula, and the groupoid of a one-sided shift of finite type has homology Coker and Ker of id - M^t"
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED (import).**

1. For étale groupoids `G` and `H` and every `n >= 0` there is a natural short exact
   sequence
   `0 -> ⊕_{i+j=n} H_i(G) ⊗ H_j(H) -> H_n(G × H) -> ⊕_{i+j=n-1} Tor(H_i(G), H_j(H)) -> 0`,
   and it splits.
2. For the étale groupoid `G` of a one-sided shift of finite type with matrix `M`:
   `H_0(G) = Coker(id - M^t)`, `H_1(G) = Ker(id - M^t)` and `H_n(G) = 0` for `n >= 2`.

**Consequence derived here.** For the one-sided full shift on two symbols, `M = (2)`. So
`Coker(1 - 2) = Z/Z = 0`, `Ker(1 - 2) = 0`, and the groupoid `G_2` has `H_*(G_2) = 0`.
By item 1, `H_*(G × G_2) = 0` for every étale groupoid `G`.

Sources:
- H. Matui, *Étale groupoids arising from products of shifts of finite type*, Adv. Math.
  303 (2016), arXiv:1512.01724, Theorem `Kunneth`.
- H. Matui, *Topological full groups of one-sided shifts of finite type*, J. reine angew.
  Math. 705 (2015), arXiv:1210.5800, TeX l.214–220, citing Matui, Proc. LMS 2012,
  Theorem 4.14.

Route: `matui-kunneth-full-shift-homology-citation`.

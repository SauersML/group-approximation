---
rg: 2
id: boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el
kind: claim
title: Every boundary simple Kazhdan group S_∂(d,k) is hyperlinear iff EL_3 over the binary Leavitt algebra L_(F_p)(1,2) is, p = char k
distinct_from:
  boundary-action-simple-kazhdan-group-is-hyperlinear: that is the open hyperlinearity question for S_∂; this proves the question is equivalent to the binary Leavitt one, and decides neither.
  binary-leavitt-unit-group-hyperlinear: that is the open question for L_(F_2)(1,2)^x or its elementary subgroups; this shows the boundary groups carry exactly the same question in each characteristic.
  leavitt-unit-groups-over-finite-fields-mutually-embed: that makes all Leavitt unit groups of one characteristic mutually embeddable; this adds the boundary simple Kazhdan groups to the same approximation problem.
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

ESTABLISHED by `boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el-proof` (unreviewed).

Let `k` be a finite field of characteristic `p`, `d >= 2`, `N >= 3`, and
`S_∂(d,k) = EL_N(LC(∂F_d, k) ⋊ F_d)/Z(EL_N)`. Put `L_p = L_(F_p)(1,2)`. Then:
- (i) the groups `EL_M(L_p)`, `M >= 2`, embed in one another;
- (ii) `S_∂(d,k)` is hyperlinear if and only if `EL_3(L_p)` is hyperlinear;
- (iii) if `L_p^x` is hyperlinear, then every `S_∂(d,k)` of characteristic `p` is hyperlinear.

**Meaning.** The boundary groups are infinite, simple and Kazhdan, and they are nonsofic. As candidates for a
hyperlinear nonsofic group they are not new: their hyperlinearity is exactly the binary Leavitt question
`binary-leavitt-unit-group-hyperlinear`, in its elementary-group form, in each characteristic. An attack on either
question transfers to the other in both directions. In particular a hyperlinear `EL_3(L_(F_2)(1,2))` would make
`S_∂` over `F_2` a hyperlinear nonsofic infinite simple Kazhdan group.

---
rg: 2
id: purely-infinite-simple-algebras-have-nonsofic-el-groups
kind: claim
title: Every countable purely infinite simple algebra over a finite field has nonsofic unit, GL and EL groups
distinct_from:
  halvable-corner-makes-elementary-groups-nonsofic: that is the corner criterion for an arbitrary algebra; this applies it to the whole purely infinite simple class through Ara--Goodearl--Pardo cancellation.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that assumes a unital Leavitt family; a purely infinite simple algebra whose unit has infinite order in K_0 contains no unital Leavitt family, and this uses a halvable corner instead.
---

**ESTABLISHED.** Let `k` be a finite field and `R` a countable purely infinite simple unital
`k`-algebra. In the sense of Ara--Goodearl--Pardo, this means `R` is simple, is not a division
ring, and every nonzero right ideal contains an infinite idempotent. Then `R^x`, every `GL_n(R)`
and every `EL_n(R)` with `n >= 2` are nonsofic.

**Scope.**
- It covers the Leavitt algebras `L_k(1,n)`, `n >= 2` (AGP Theorem 4.2, read in
  `agp-purely-infinite-simple-k1-citation`), with no use of a Leavitt family in `R` itself.
- Algebras with a unital `d`-ary Cuntz family need no simplicity at all. They are already covered
  by `d-ary-leavitt-groups-nonsofic-over-finite-fields`. Examples are Nekrashevych algebras of
  self-similar groups over `k`, which satisfy `s_x^* s_y = delta_xy` and `sum_x s_x s_x^* = 1`.
- It does not cover simple algebras with a unital rank model, which have no halvable corner
  (`halvable-corner-makes-elementary-groups-nonsofic`). The subshift crossed product
  `LC(X, F_q) ⋊ Z` is one: its `EL_3` is LEF.

**For the ring route.** The coefficient ring of a sofic finitely presented simple elementary group
cannot be purely infinite. Purely infinite simple is the class in which every finite presentation
theorem for simple rings of Leavitt, graph or Nekrashevych type lives
(`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`).

Route: `purely-infinite-simple-algebras-have-nonsofic-el-groups-proof`.

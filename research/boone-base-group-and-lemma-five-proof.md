---
rg: 2
id: boone-base-group-and-lemma-five-proof
kind: route
title: Read Lemma 5 off the sub-basis calculus in the split extension
target: boone-base-group-and-lemma-five
requires: [free-subbasis-subgroup-calculus]
artifacts:
  - GroupApproximation/Computability/BooneGroupBase.lean
---

## Why sufficient

In the split-extension model `T` is the kernel of the projection to the acting
`Z^2` (`mem_Tsub_iff`: `g in T` iff `g.right = 1`), so `T` is the free group on
`Z x Z` sitting inside as `inl`, and every subgroup of `T` occurring in the
construction is a `basisSubgroup` for an explicit index set.  The prerequisite
is then applied three times.

**Lemma 5.**  `T cap G_{ab}^{MN}` is computed by intersecting index sets.  The
image of `emb a b M N` meets `T` in the sub-basis subgroup on
`embIdx a b M N '' univ`, and `twSub_inf` (the prerequisite's intersection
fact, transported to `BaseGroup`) gives
`twSub S cap twSub T = twSub (S cap T)`.  What is left is arithmetic on
indices -- `embIdx a b M N q = (a + q.1 * M, b + q.2 * N)`, injective for
nonzero `M, N` by `scaleIdx_injective` -- and that identifies the intersection
with `T_{ab}^{MN}`.

**Injectivity of `emb`.**  `emb` is `inl` on the free factor along the index
map `embIdx`, and `inr` on the acting factor along `scaleIdx`; both index maps
are injective for nonzero `M, N`, and the prerequisite's `range_indexMap`
turns that into injectivity of the induced map on the free factor.  The
semidirect product then assembles the two components.

**`Gsub_eq_closure`.**  `Gsub = (top).map emb` by `MonoidHom.range_eq_map`, and
`top = Subgroup.closure {t, x, y}` because `sh_conj_tw` writes
`t(p) = x^{-p} t x^{p}` and `SemidirectProduct.inl_left_mul_inr_right` splits
an arbitrary element, with `FreeGroup.induction_on` covering the free factor.
`Subgroup.map_closure` and the generator images `emb_tGen`, `emb_sh` finish.
The one step worth naming is `sh h ^ n = sh (n . h)`, via `map_zpow` and
`ofAdd_zsmul`, which is the only place the `Prod` `zsmul` instance is touched.

## Not a restatement

The prerequisite is a statement about an arbitrary free group with no group
`G`, no `t(a,b)` and no `M, N` in it.  This claim is about one specific split
extension and identifies two of its subgroups; the arithmetic of `embIdx` and
the semidirect-product bookkeeping are neither stated nor implied by the
prerequisite.

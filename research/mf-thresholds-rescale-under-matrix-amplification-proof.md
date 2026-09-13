---
rg: 2
id: mf-thresholds-rescale-under-matrix-amplification-proof
kind: route
title: Proof that the MF thresholds rescale by the matrix size
target: mf-thresholds-rescale-under-matrix-amplification
requires:
  - mf-rigidity-is-monotone-in-matrix-rank
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

**Lemma: `EL_N(M_m(R)) = EL_(Nm)(R)` for `N >= 2`, `m >= 1`.**

Inclusion `<=`. For `X in M_m(R)` and `i != j` in `{1,...,N}`, the block elementary `e_ij(X)` equals the
product of the `e_((i,a),(j,b))(X_ab)` over `a, b in {1,...,m}`. The index pairs `((i,a),(j,b))` are
pairwise distinct and, since `i != j`, no one of them is the transpose of another, so the factors commute
and each is an elementary matrix over `R`.

Inclusion `>=`. Let `p != q` in `{1,...,Nm}`, lying in blocks `i` and `j`. If `i != j` then `e_pq(r)` is the
block elementary `e_ij(X)` where `X` is the matrix unit of the corresponding entry scaled by `r`. If `i = j`
use `N >= 2` to choose a block `l != i` and an index `p'` inside it; then
`e_pq(r) = [ e_(p p')(r), e_(p' q)(1) ]`, a commutator of two elementary matrices whose index pairs lie in
distinct blocks, each already in `EL_N(M_m(R))` by the previous case.

**Theorem.** Let `N >= 2`. By the Lemma, `EL_N(M_m(R))` is MF-rigid if and only if `EL_(Nm)(R)` is. By
`mf-rigidity-is-monotone-in-matrix-rank` the MF-rigid ranks of `R` are exactly the `K >= rig(R)`, so this
holds if and only if `Nm >= rig(R)`, that is `N >= ceil(rig(R)/m)`. Intersecting with `N >= 2` gives
`rig(M_m(R)) = max(2, ceil(rig(R)/m))`.

The same argument with the down-set of MF ranks gives that `EL_N(M_m(R))` is MF if and only if
`Nm <= mf(R)`, that is `N <= floor(mf(R)/m)`; so `mf(M_m(R)) = floor(mf(R)/m)` when that number is at least
`2`, and `mf(M_m(R)) = 1` otherwise.

**Corollary.** `ceil(x/m)` is finite exactly when `x` is, and `floor(x/m)` is infinite exactly when `x` is,
so finiteness of `rig` and infiniteness of `mf` are unchanged by `R |-> M_m(R)`, while the values move.

**The state-space remark.** For `R` countable simple unital, `simple-ring-stably-finite-iff-unit-not-paradoxical`
gives: `R` is stably finite if and only if `[R]` is not paradoxical in `V(R)`, if and only if `V(R)` carries
a state finite and nonzero at `[R]`. If `R` is simple, every nonzero element of `V(R)` is full: for an
idempotent `e` over `M_j(R)`, writing `1` as a finite sum `sum a_i e b_i` gives `[1] <= m[e]` for some `m`,
while `[e] <= j[1]`. So a state nonzero at any element is nonzero at `[R]`, and "V(R) carries a nonzero
state" is a property of the ordered monoid alone, hence a Morita invariant. Combined with
`stably-infinite-ring-elementary-groups-have-no-mf-quotient`, the Morita-invariant condition "`V(R)` has no
nonzero state" implies `rig(R) < infinity`. The converse is the open claim
`stably-finite-simple-rings-have-mf-elementary-groups` of lane `un-architect` and is not used here.

---
rg: 2
id: malnormal-edge-amalgam-tree-action-is-acylindrical-proof
kind: route
title: Malnormality kills stabilizers of 3-paths, and a middle 3-path of a long segment pins every coarse fixer to one of 4ε+2 translates
target: malnormal-edge-amalgam-tree-action-is-acylindrical
requires: []
---

**Standard tools.**
* **(BS)** The Bass--Serre tree of `G = A *_C B` (Serre, *Trees*, §I.4.1,
  Theorem 7).  Its vertices are the cosets `gA` and `gB`, its edges the
  cosets `gC`, and `gC` joins `gA` to `gB`.  `G` acts by left multiplication,
  without inversions.  The edges at the vertex `B` are the `βC` with
  `β in B`, and `Stab(βC) = βCβ^{-1}`.
* **(NF)** The normal form theorem for amalgams.  A product
  `g_1...g_n` (`n >= 1`) whose factors alternate between `A \ C` and `B \ C`
  is not `1`.  Also `A cap B = C` inside `G`.

## (S3) 3-paths have trivial stabilizers

Take a geodesic path `x_0,x_1,x_2,x_3`.  Types alternate, so one of `x_1`,
`x_2` is a `B`-type vertex `w`, with two distinct path edges `e ≠ e'` at `w`.
Translate by some `h in G` so that `hw = B`.  Then `he = βC` and
`he' = β'C`, with `β,β' in B` and `β^{-1}β' notin C`.  The pointwise
stabilizer of the path lies in

```text
Stab(e) cap Stab(e') = h^{-1} β ( C cap (β^{-1}β') C (β^{-1}β')^{-1} ) β^{-1} h = 1
```

by malnormality of `C` in `B`.  ∎

## (ACYL) Counting coarse fixers

Let `x,y` be vertices, with `D = d(x,y) >= 2ε+5`, and let `[x,y]` have
vertices `v_0=x,...,v_D=y`.  Let `g` satisfy `d(x,gx) <= ε` and
`d(y,gy) <= ε`.

*Every middle vertex goes back onto `[x,y]` near itself.*  Let `m = v_i` with
`ε < i < D-ε`.  In a tree, `[gx,gy]` is contained in
`[gx,x] ∪ [x,y] ∪ [y,gy]`, and `gm` lies on `[gx,gy]` with `d(gx,gm) = i`.
If `gm` were on `[gx,x]`, then `i <= d(gx,x) <= ε`, which is false.
Symmetrically, `gm` is not on `[y,gy]`, so `gm in [x,y]`.  Also
`|d(x,gm) - i| = |d(x,gm) - d(gx,gm)| <= d(x,gx) <= ε`.

*A middle 3-path.*  Put `p = floor(ε)+1` and `σ = (v_p,...,v_{p+3})`.  Since
`p+3 < D - ε`, all four vertices satisfy the condition above.  So `gσ` is a
geodesic 3-path whose vertices all lie on the geodesic `[x,y]`.  It is
therefore a subsegment `(v_q,...,v_{q+3})`, traversed forwards or backwards.
Its start is within `ε` of index `p`, so `q` takes at most `2 floor(ε)+1`
values once the orientation is fixed.  Hence the map `v_{p+j} |-> g v_{p+j}`
(`0<=j<=3`) takes at most `2(2ε+1)` values.

*Injectivity.*  If `g` and `g'` induce the same map on `σ`, then `g^{-1}g'`
fixes `σ` pointwise, so `g = g'` by (S3).

So at most `4ε+2` elements qualify: `R(ε)=2ε+5` and `N(ε)=4ε+2`.  For
arbitrary points of the geometric realization, move `x` and `y` to nearest
vertices, which costs at most `1/2` each.  Then `R(ε)=2(ε+1)+6` and
`N(ε)=4(ε+1)+2` work.  ∎

## (NE) Two independent loxodromics

Let `u = A`, `v = B` and `e = C`, so `e=[u,v]`.  Then `t` fixes `u` with
`te ≠ e` (as `t notin C`), and `b` fixes `v` with `be ≠ e`.

*`h = tb` is loxodromic of translation length 2.*  `te` joins `u` and `tv`.
`tbe` joins `tv` and `tbu = hu`.  Concatenate the translates `h^k π` of the
path `π = (u, tv, hu)` for all `k in Z`.  There is no backtracking:

* at `tv`, the two edges are `te` and `tbe`, and they differ because `be ≠ e`;
* at `hu`, the two edges are `tbe` and `h·te = tb·te`, and they differ because
  `te ≠ e`.

A locally injective bi-infinite edge path in a tree is a geodesic line.  `h`
translates it by `2`, so `h` is loxodromic with axis through `e`.  The same
argument with the roles of the factors exchanged shows that `h' = bt` is
loxodromic of translation length `2`.

*No common endpoint.*  Suppose `h` and `h'` share an endpoint `ξ`.  Replace
`h'` by `h'^{-1}` if necessary so that both translate towards `ξ`.  Their axes
share a ray towards `ξ`, and on all sufficiently deep vertices of that ray
both elements move points `2` steps towards `ξ`.  So `h^{-1}h'^{±1}` fixes a
3-path pointwise, and (S3) gives `tb = (bt)^{±1}`.

* `tb = bt` gives `b^{-1}·t·b·t^{-1} = 1`, an alternating product of four
  elements of `A \ C` and `B \ C`, contradicting (NF).
* `tb = (bt)^{-1} = t^{-1}b^{-1}` gives `t^2 = b^{-1}·b^{-1}` after
  multiplying by `t` on the left and by `b^{-1}` on the right.  So
  `t^2 in A cap B = C`, contradicting `t^2 notin C`.

So `h` and `h'` are independent.  The limit set then has at least four points,
so the action is non-elementary.  ∎

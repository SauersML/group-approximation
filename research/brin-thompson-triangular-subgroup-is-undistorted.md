---
rg: 2
id: brin-thompson-triangular-subgroup-is-undistorted
kind: claim
title: "Every infinite-order element of the triangular subgroup T_n of nV has linearly growing exponent cocycle, so it is undistorted in every finitely generated subgroup of nV"
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is the case n = 1 (T_1 = V); this extends undistortion to the triangular subgroup of every nV, which contains C(C,V) ⋊ V, V^n and the fibred subgroups, while nV itself (n >= 2) has distorted elements
  brin-thompson-mv-contains-a-distortion-element: that exhibits a distorted element of mV; this says no power of such an element is triangular, in any coordinate order and up to conjugacy
---

**ESTABLISHED** by `brin-thompson-triangular-subgroup-is-undistorted-proof`.

**Definitions.** `C = {0,1}^ω`, and `nV` acts on `C^n` by finitely many brick maps
`Π C(u_j) → Π C(v_j)`, `(u_j z_j)_j ↦ (v_j z_j)_j`. For `1 ≤ k < n` let
`pr_k : C^n → C^k` be the projection to the first `k` coordinates. The *triangular subgroup* is

```text
T_n = { g ∈ nV : for each 1 ≤ k < n there is a homeomorphism h_k of C^k with pr_k ∘ g = h_k ∘ pr_k } ,
```

and `T_1 = V`. The *exponent cocycle* is `δ_g(x) = (|v_j| − |u_j|)_j ∈ Z^n` for `x` in a table
brick of `g`. Put `D(g) = max_x ‖δ_g(x)‖_∞`.

**Statement.**

1. `T_n` is a subgroup of `nV`. Each `h_k` lies in `kV`, and `h_{n−1} ∈ T_{n−1}`.
2. For every infinite-order `g ∈ T_n` there is an integer `Q ≥ 1` with `D(g^m) ≥ ⌊m/Q⌋` for all
   `m ≥ 0`.
3. Hence every infinite-order element `g` of any conjugate `k T_n k^{-1}` (`k ∈ nV`), or of its
   image under a permutation of coordinates, is undistorted in every finitely generated subgroup
   `L ≤ nV` containing `g`: `|g^m|_L ≥ c m` for some `c > 0`.

**Examples inside `T_n`.** The product `V^n` acting coordinatewise; for `n = 2`, the group
`C(C,V) ⋊ V` of maps `(x, y) ↦ (h(x), F_x(y))` with `h ∈ V` and `F` locally constant with
values in `V`, which contains `C(C,Z) ⋊ V`; more generally `C(C, T_{n−1}) ⋊ V ≤ T_n`.
The baker's map `(i x, y) ↦ (x, i y)` of `2V` is not in `T_2`: its projection factors through
the non-injective shift.

**Use.** With `cubical-coset-proper-actions-capture-distorted-elements` (item 3) and the
distorted element of `brin-thompson-mv-contains-a-distortion-element`, this gives
`brin-thompson-nv-no-cubical-action-proper-mod-triangular`.

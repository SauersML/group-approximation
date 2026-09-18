---
rg: 2
id: brin-thompson-nv-product-subgroup-has-finite-shear-core
kind: claim
title: "For n >= 2 the coordinate-permuted triangular subgroups of nV meet in V^n, and V^n meets finitely many of its shear conjugates in a group of order at most 2^n"
distinct_from:
  brin-thompson-triangular-subgroup-is-undistorted: that proves undistortion of T_n and that its base maps lie in kV; this computes intersections of automorphic images of T_n, which is a statement about coset geometry, not about growth
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that uses the shear-like single-brick fibre elements as central elements of copies of C(C,Z) ⋊ V; this uses them as conjugators that force product elements into centralizers
---

**ESTABLISHED** by `brin-thompson-nv-product-subgroup-has-finite-shear-core-proof`.

**Setting.** `C = {0,1}^ω`, `n ≥ 2`, `T_n ≤ nV` the triangular subgroup of
`brin-thompson-triangular-subgroup-is-undistorted`, and `V^n ≤ nV` the coordinatewise product.
For a permutation `σ` of `{1, ..., n}` let `σ̂(x)_k = x_{σ^{-1}(k)}`, a homeomorphism of `C^n`
normalising `nV`, and `α_σ = Ad σ̂`. Write `ε = 1_{C(1)}`. For `s ∈ V` and `i ≠ j` the *shear*
`t = t^{(i,j)}_s ∈ nV` replaces `x_j` by `s(x_j)` when `x_i ∈ C(1)` and fixes `x` otherwise.

**Statement.**

1. `⋂_σ α_σ(T_n) = V^n`.
2. Let `S ⊆ V ∖ {1}` be a finite generating set of `V`. For each `j` fix some `i(j) ≠ j`. Then

   ```text
   F = V^n ∩ ⋂_{j ≤ n} ⋂_{s ∈ S} (t^{(i(j),j)}_s)^{-1} V^n t^{(i(j),j)}_s
   ```

   has at most `2^n` elements.
3. Hence there are finitely many automorphisms `α_1, ..., α_r` of `nV` (coordinate permutations
   composed with inner automorphisms by shears) such that `α_1(T_n) ∩ ... ∩ α_r(T_n)` is finite.

**Key computation (item 2).** For `h = (a_1, ..., a_n) ∈ V^n` and `t = t^{(i,j)}_s`, the
element `t h t^{-1}` lies in `V^n` if and only if either `a_i` fixes `C(0)` and `C(1)` and
`a_j s = s a_j`, or `a_i` swaps `C(0)` and `C(1)` and `a_j^{-1} s a_j = s^{-1}`.

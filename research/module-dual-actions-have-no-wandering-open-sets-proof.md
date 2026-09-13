---
rg: 2
id: module-dual-actions-have-no-wandering-open-sets-proof
kind: route
title: Invariant Haar measure and pigeonhole recurrence
target: module-dual-actions-have-no-wandering-open-sets
requires: []
---

1. **Haar measure.** Let `m` be normalized Haar measure on `X`.
   - A continuous automorphism pushes `m` to a normalized Haar measure, which is `m` itself by
     uniqueness. So `m` is `G`-invariant.
   - Finitely many translates of a nonempty open `B` cover the compact group `X`, so
     `m(B) > 0`.
2. **Recurrence.** Fix a finite `F ⊆ G` and an integer `N > 1/m(B)`.
   - Choose `g_1, ..., g_N` inductively with `g_j ∉ ∪_(i<j) g_i (F ∪ F^-1)`. This is possible
     because `G` is infinite. Then `g_i^-1 g_j ∉ F` for `i ≠ j`.
   - The sets `g_i B` have total measure `N m(B) > 1 = m(X)`, so `g_i B ∩ g_j B ≠ ∅` for some
     `i ≠ j`.
   - Then `B ∩ gB ≠ ∅` with `g = g_i^-1 g_j ∉ F`. As `F` was arbitrary, infinitely many such
     `g` exist.
3. **Item 1.**
   - *No proper open part.* Suppose `U` is open, invariant, nonempty and proper. Pick
     `x ∈ U` and an open `B ∋ x` whose closure `K` is compact and lies in `U`. Properness makes
     `{g : gK ∩ K ≠ ∅}` finite, but that set contains the infinite set of step 2.
   - *No disjoint translates.* A compact open set with pairwise disjoint translates contradicts
     step 2 directly.
4. **Item 2.**
   - The conditional expectation `E : C(X) ⋊_r G -> C(X)` is faithful, and `m` has full
     support. So `tau(x^*x) = ∫ E(x^*x) dm = 0` forces `E(x^*x) = 0`, hence `x = 0`.
   - Invariance of `m` makes `tau` tracial.
   - For `X = V^`, `tau(u_(v,g)) = ∫ xi(v) dm(xi) · [g = 1] = [v = 0][g = 1]`. That is the
     canonical trace of `C*_r(V ⋊ G)`.
   - `tau ⊗ Tr` is faithful on `M_n`, so nonzero projections have positive trace.

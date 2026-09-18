---
rg: 2
id: finite-similarity-types-bound-minimal-invariant-sets-proof
kind: route
title: "Find a similarity type that recurs at a point of each minimal set, and transport invariant sets along bisections"
target: finite-similarity-types-bound-minimal-invariant-sets
requires: []
---

Setting and definitions as in `finite-similarity-types-bound-minimal-invariant-sets`.

1. **Transport.** Let `Z ⊆ X` be `G`-invariant, and let `S` be a bisection with
   `s(S) = B_j` and `r(S) = U`. Suppose `Z ∩ B_j ≠ ∅`, and pick `z` in it. Take
   `γ ∈ S` with `s(γ) = z`. Then `r(γ) ∈ U`, and `r(γ) ∈ Z` by invariance, so
   `U ∩ Z ≠ ∅`. The same argument with `S^{-1}` shows that `U ∩ Z ≠ ∅` implies
   `B_j ∩ Z ≠ ∅`.
2. **A recurring type.** Let `Y` be a minimal closed invariant set and pick
   `y ∈ Y`. Some index `j` has the following property: every neighbourhood of
   `y` contains a basic set `U ∋ y` with `j(U) = j`.
   - Suppose not. Then for each `i ≤ m` there is a neighbourhood `W_i` of `y`
     containing no basic set of type `i` around `y`.
   - `W = W_1 ∩ ... ∩ W_m` is a neighbourhood of `y`. It contains some basic
     set `U ∋ y`, whose type `j(U)` is one of the `i`. That is a contradiction.
   - Fix such a `j` and set `τ(Y) := j`, having chosen `y`. By step 1, applied
     to `Z = Y` and a basic `U ∋ y` of type `j`, `Y ∩ B_j ≠ ∅`.
3. **Injectivity.** Let `Y'` be a minimal closed invariant set with
   `τ(Y') = j = τ(Y)`.
   - By step 2 applied to `Y'`, `Y' ∩ B_j ≠ ∅`.
   - By step 1, `Y'` meets every basic set of type `j`. By step 2 for `Y`, such
     sets around `y` lie inside every neighbourhood of `y`. So `y` lies in the
     closure of `Y'`, which is `Y'`.
   - Hence `Y ∩ Y'` is a nonempty closed invariant subset of both, and
     minimality gives `Y = Y ∩ Y' = Y'`.
4. So `τ` is injective from the set of minimal closed invariant sets into
   `{1, ..., m}`. ∎

---
rg: 2
id: invariant-measure-forbids-finite-similarity-type-systems-proof
kind: route
title: "Disjoint basic sets around many points have the measures of their types, which cannot all exceed a positive constant"
target: invariant-measure-forbids-finite-similarity-type-systems
requires:
  - amenable-full-group-forces-invariant-measure
---

Setting and definitions as in `invariant-measure-forbids-finite-similarity-type-systems`.

1. **Types carry measure.** Let `U` be a basic set, the range of a compact open bisection `S` with
   `s(S) = B_j`. By invariance, `μ(U) = μ(r(S)) = μ(s(S)) = μ(B_j)`. Since `U` contains a point,
   `B_j = s(S)` is nonempty, because `r` and `s` are bijections between `S`, `r(S)` and `s(S)`.
2. **Item 1.** Let `y_1, ..., y_N` be distinct points of `X`.
   - `X` is Hausdorff, so there are pairwise disjoint open sets `W_i ∋ y_i`.
   - Each `y_i` has a basic set `U_i ⊆ W_i` containing `y_i`. The `U_i` are pairwise disjoint and
     Borel, since they are compact open.
   - By step 1, `Σ_i μ(B_{j(U_i)}) = Σ_i μ(U_i) = μ(∪_i U_i) <= 1`, so some `μ(B_{j(U_i)}) <= 1/N`.
   - If `X` is infinite, `N` is arbitrary, so the infimum is `0`.
3. **Item 2.** Suppose the types of basic sets have `μ(B_j) >= c > 0`. For a finite system take
   `c = min {μ(B_j) : B_j ≠ ∅}`, which is positive because `μ` is positive on nonempty open sets and
   compact open sets are open; by step 1, only nonempty `B_j` occur as types. Take `N > 1/c` distinct
   points, possible since `X` is infinite. Step 2 gives a type with `μ(B_j) <= 1/N < c`, a
   contradiction.
4. **Item 3.** Let `μ` be a `G`-invariant probability measure on `X`.
   - `X` is second countable, so the union `O` of all `μ`-null open sets is a countable union of null
     basic open sets. Hence `O` is null and open, and `supp μ = X \ O` is nonempty.
   - **`O` is invariant.** Let `x ∈ O`, and let `γ` be an arrow with `s(γ) = x`. Pick a compact open
     bisection `S ∋ γ`; `G` is étale with totally disconnected unit space, so such bisections form a
     basis. Put `S' = S ∩ s^{-1}(O)`, an open bisection containing `γ`.
   - `r(S')` is open and contains `r(γ)`. The map `s` is a homeomorphism from `S'` onto the open set
     `s(S') ⊆ X`, so `S'` is second countable with a basis of compact open bisections. Hence
     `S' = ∪_n S_n` for countably many compact open bisections `S_n`. Invariance gives
     `μ(r(S_n)) = μ(s(S_n)) <= μ(O) = 0`, so `μ(r(S')) <= Σ_n μ(r(S_n)) = 0`. Thus `r(S')` is a null
     open set, and `r(γ) ∈ O`.
   - So `supp μ` is a nonempty closed invariant set, and minimality gives `supp μ = X`. Thus `μ` is
     positive on nonempty open sets.
   - Item 2 then forbids a finite similarity type system. Contrapositive: a finite system excludes
     every invariant probability measure.
5. **Item 4.** `G` is minimal on the infinite space `X`. A finite orbit would be a closed invariant
   proper subset, so every orbit is infinite and in particular has at least three points. Now
   `amenable-full-group-forces-invariant-measure`, item 2, applies: an amenable group realizing
   moving bisections yields a `G`-invariant probability measure. That contradicts item 3. By item 1
   of the same node, `D([[G]])` realizes moving bisections, and so does every group containing it,
   including `[[G]]`. ∎

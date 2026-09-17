---
rg: 2
id: free-group-sft-host-units-have-doubly-exponential-wp-proof
kind: route
title: Recode to a pruned nearest-neighbour tree SFT, compute ball languages by local checking, and multiply coefficient tables
target: free-group-sft-host-units-have-doubly-exponential-wp
requires: []
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

This is Theorem C of the artifact (Section 4).

1. **Recoding.** The `r`-block map is a conjugacy onto a nearest-neighbour SFT. It induces an
   isomorphism of crossed products fixing every `u_g`, so assume `X` is given by edge relations
   `R_s`.
2. **Pruning and extension.** Restrict to the largest alphabet `A_∞` in which every letter has an
   `R_s`-successor for each `s`. Every point of `X` uses only `A_∞`. On the Cayley tree, a locally
   legal `A_∞`-pattern on a finite connected set extends vertex by vertex. Each new vertex, taken in
   order of distance, has exactly one earlier neighbour. So `L_(B_M)(X)` is the set of locally legal
   patterns, decidable in time `O(|A|^((2d+1)^M) * (2d+1)^M * d)`.
3. **Tables.** Represent `Σ_(g∈B_K) φ_g(x|_(B_M)) u_g` by the table `(g, p) -> φ_g(p)` on
   `B_K × L_(B_M)(X)`. Two tables represent the same element iff they agree on the language, since
   every language pattern occurs in a point and the `u_g` are a basis. If the generators have radius
   `R`, a word of length `j` has a table of radius `(Rj, Rj)`, and right multiplication by a
   generator uses `(f u_g)(f' u_h) = f (f'∘g^(-1)) u_(gh)`, where `f'∘g^(-1)` depends on
   `x|_(B_(|g|+R))`.
4. **Decision and time.** `w = 1` iff the table of `w` is `1` at `g = 1` and `0` elsewhere, on
   `L_(B_(Rl))(X)`. The total time is `poly((2d+1)^(Rl)) * |A|^((2d+1)^(Rl)) * l <= C * 2^(2^(C l))`.
   `∎`

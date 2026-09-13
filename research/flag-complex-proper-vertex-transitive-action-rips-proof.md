---
rg: 2
id: flag-complex-proper-vertex-transitive-action-rips-proof
kind: route
title: Collapse twin vertices of the Cayley flag complex onto the flag complex acted on
target: flag-complex-proper-vertex-transitive-action-rips
requires: []
---

Let `φ : G → X^0`, `φ(g) = g v`. It is surjective by vertex transitivity, and
its fibres are the cosets `g G_v`, which are finite.

1. **`S` is finite and symmetric.** `S ∖ G_v` maps into the finitely many
   neighbours of `v`, each fibre is a coset of the finite group `G_v`, and
   `G_v ∖ {1} ⊆ S`. If `g v` is adjacent to or equal to `v`, then applying
   `g^-1` shows the same for `g^-1 v`.
2. **Adjacency.** For `g, h ∈ G`, `g^-1 h ∈ S ∪ {1}` iff `g^-1 h v` is equal or
   adjacent to `v`. Applying the automorphism `g`, this holds iff `φ(h)` is equal
   or adjacent to `φ(g)`. So a finite set `σ ⊆ G` is a simplex of
   `K = P_1(G,S)` iff the points of `φ(σ)` are pairwise equal or adjacent in `X`.
3. **`S` generates.** `X` is contractible, so its 1-skeleton is connected. Given
   `g`, take an edge path `v = u_0, ..., u_k = g v` and choose `g_i` with
   `φ(g_i) = u_i`, `g_0 = 1`, `g_k = g`. By item 2 every `g_(i-1)^-1 g_i` lies in
   `S ∪ {1}`, so `g ∈ ⟨S⟩`.
4. **Section.** Choose a map `s : X^0 → G` with `φ ∘ s = id`, and let `T = s(X^0)`.
   By item 2 and since `X` is flag, `φ` restricts to an isomorphism from the full
   subcomplex `K[T]` onto `X`: a finite subset of `X^0` is a simplex of `X` iff
   its points are pairwise adjacent.
5. **Retraction.** `r = s ∘ φ : K^0 → T` is simplicial `K → K[T]`, since by
   item 2 it sends pairwise equal-or-adjacent sets to pairwise equal-or-adjacent
   sets. Let `i : K[T] → K` be the inclusion. Then `r ∘ i = id`, because
   `s(φ(t)) = t` for `t = s(x)`.
6. **Contiguity.** For a simplex `τ` of `K`, the set `τ ∪ r(τ)` is a simplex:
   `φ(r(h)) = φ(h)`, so all images are pairwise equal or adjacent. Hence `i ∘ r`
   and `id_K` are contiguous. Contiguous simplicial maps are homotopic, by the
   straight-line homotopy inside the simplex `τ ∪ r(τ)`, which is continuous in
   the weak topology.

So `i` is a homotopy equivalence and `K ≃ K[T] ≅ X`, which is contractible.

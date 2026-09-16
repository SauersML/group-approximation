---
rg: 2
id: contractible-2-complex-torsion-free-gives-spine-images-avoid
kind: route
title: A simplicial coarse lift embeds SL(2,5) in the fundamental group of any small-fiber image, which torsion-freeness forbids
target: spine-epsilon-images-avoid-contractible-2-complexes
requires:
  - contractible-2-complex-subcomplexes-have-torsion-free-pi1
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

Let `L` be the flag triangulation of the Poincaré-spine, with the unit metric. Let `δ > 0` be a
Lebesgue number of its open vertex-star cover. We show NE with `ε = δ`. Suppose `Y` is a
contractible simplicial 2-complex, `K ⊆ Y` a finite connected subcomplex, and `g: |L| → |K|` a
surjection whose fibers have diameter `< δ`. PL is not needed.

**Step 1: a simplicial coarse lift.** This is Lemma 1 of the artifact, §2, with the proof given in
full.

- *(a) Controlled neighbourhoods.*
  - For `y ∈ |K|`, the fiber `F_y = g^{-1}(y)` is nonempty and compact, with `diam F_y < δ`.
  - Put `η_y = (δ − diam F_y)/3` and `U_y = {x : d(x, F_y) < η_y}`, so `diam U_y < δ`.
  - `g` is closed, so `V_y = |K| − g(|L| − U_y)` is an open neighbourhood of `y` with
    `g^{-1}(V_y) ⊆ U_y`.
- *(b) Choice of `λ` on vertices.*
  - Let `μ` be a Lebesgue number of `{V_y}`. Take an iterated barycentric subdivision `K'` whose
    closed vertex stars have diameter `< μ`.
  - For a vertex `u`, `g^{-1}(St u)` lies in some `U_y`. So it has diameter `< δ` and lies in some
    open star `st(w)` of `L`. Put `λ(u) = w`.
- *(c) `λ` is simplicial.*
  - Let `y` be interior to `[u_0, ..., u_k]` and `x ∈ F_y`. Then `x ∈ st(λ(u_i))` for all `i`.
  - So the `λ(u_i)` are vertices of the carrier `supp(x)` and span a simplex of `L`.
- *(d) Homotopy.*
  - For every `x`, both `x` and `λ g(x)` lie in `supp(x)`, by (c).
  - The straight-line homotopy, computed affinely in each closed simplex, gives `λ ∘ g ≃ id_L`.

**Step 2: torsion.**
- A free homotopy `λ ∘ g ≃ id` makes `λ_* ∘ g_*` an isomorphism on `π_1`. So
  `g_*: SL(2,5) → π_1(K)` is injective.
- By `contractible-2-complex-subcomplexes-have-torsion-free-pi1`, `π_1(K)` is torsion-free, yet it
  contains the nontrivial finite group `g_*(SL(2,5))`.
- This is a contradiction, so no such `(Y, K, g)` exists.

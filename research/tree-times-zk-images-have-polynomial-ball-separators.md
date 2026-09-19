---
rg: 2
id: tree-times-zk-images-have-polynomial-ball-separators
kind: claim
title: A graph with a bounded-fibre Lipschitz map to T×Z^k has balanced separators of size O(D^k) for every subset of a D-ball, so Kazhdan orbits with a copy of Z^(k+2) or F₂×F₂ admit no bounded-displacement injection into Z^k×F_d
distinct_from:
  translation-like-hosts-are-capped-by-separation-profiles: that caps FREE realizations by the global separation profile sep(n); this is a ball-local bound (separators of subsets of radius-D balls are O(D^k), i.e. polylogarithmic in the ball size), proved directly by a tree-centroid slab, and applied to NON-free transitive orbits of the target group Z^k×F_d.
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that kills virtually free scaffolds by pulled-back tree walls (finite cuts) and notes that one-endedness and nonamenability survive over T×Z^2; this gives a graph invariant that T×Z^k-images must satisfy although T×Z^k is one-ended and nonamenable.
---

**ESTABLISHED** (lane proof, swarm-0917-w11-w11-z-break; elementary; not reviewed).
Route: `tree-times-zk-images-have-polynomial-ball-separators-proof`.
Only item 3 uses recalled facts: isoperimetry of boxes in Z^m, and Benjamini–Schramm–Timár's lower bound
for sep(T×T), which is attained on products of tree balls.

## Setting

- `T` is a tree of bounded degree. The graph `T×Z^k` is the Cartesian product, with metric
  `d_T + |·|₁`. For `d ≥ 2`, `Cay(Z^k×F_d)` with standard generators is `T_(2d)×Z^k`.
- `X` is a connected graph, and `f : V(X) → V(T×Z^k)` is `L`-Lipschitz with fibres of size at most `m`.
- A *balanced separator* of a finite `A ⊆ V(X)` is a set `S ⊆ A` such that every connected component of
  `X[A∖S]` has at most `|A|/2` vertices.
- `bsep_X(D)` is the maximum, over `x` and over finite `A ⊆ B_X(x, D)`, of the least size of a balanced
  separator of `A`.

## Statement

1. **(Slab lemma.)** `bsep_X(D) ≤ m·|B_T(L)|·(2LD+1)^k` for all `D ≥ 0`.
2. **(Left displacement is Lipschitz.)** Suppose `G = ⟨S⟩` acts on the right on `Z`, and an injective
   `φ : Z → Z^k×F_d` has bounded left displacement, meaning `φ(z·s) ∈ B·φ(z)` for a finite `B` and all
   `z, s`. Then `f(z) = φ(z)^(−1)` is injective and `L`-Lipschitz from `Sch(G, Z, S)` to
   `Cay(Z^k×F_d)`, where `L = max |b|` over `b ∈ B`. So `bsep_(Sch)(D) = O(D^k)`.
3. **(Class kill for need d2d6a0cb, k = 2.)** Let `G` act transitively on `Z`. Suppose some `x ∈ Z` and
   some subgroup `Q ≤ G` have `Q ∩ G_x` finite, where `Q ≅ Z^4`, or `Q ≅ F₂×F₂`, or more generally `Q` is
   finitely generated with `bsep_Q(D) / D^2 → ∞`. Then there is no injective bounded-left-displacement map
   `Z → Z^2×F_d`.
   - In particular this holds when `G` acts freely and contains `Z^4` or `F₂×F₂`. Examples are `SL_n(Z)`
     for `n ≥ 4`, via the block unipotent `Z^4`, or via `F₂×F₂` inside the block-diagonal
     `SL₂(Z)×SL₂(Z)`.

## Consequence

A graph invariant does constrain the need. Every transitive Schreier graph that answers need `d2d6a0cb`
positively has balanced ball-separators of size `O(D^2)`. That is polylogarithmic in the ball volume,
which grows exponentially because (T) gives a Cheeger bound
(`kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds`, item 1). The remaining question is
isolated in `kazhdan-schreier-graphs-have-superquadratic-ball-separation`.

---
rg: 2
id: marked-graph-action-not-residually-finite-proof
kind: route
title: The graph charts are exact two-point data at the marked pair
target: marked-graph-action-not-residually-finite
requires: [exact-models-cannot-separate-marked-pair]
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

## Why sufficient

Let `ε₀ > 0` and `F₀ = S_Γ ∪ S_Γ^{-1} ∪ {h}` be as in the prerequisite, and
fix any `ε < ε₀`.  Suppose the action `G ↷ (X,S)` were residually finite in
the sense of Definition 2.6 of `arXiv:2607.29571`.  Apply the definition with
`F = F₀` and `W = {p,q} = {Γ, hΓ}`.  It returns a finite graph `Θ`, a finite
set `A`, a homomorphism `φ : G → Sym(A)`, and graph embeddings
`π_a : (W, E|_{W×W}) ↪ Θ` with `π_{φ(g)a}(v) = π_a(g^{-1}v)`.

Read this as two-point data in the sense of `two-point-orbit-approximation`:

* `A` is finite and `φ` is a genuine action of `G` on it — in particular
  unital and `(F₀,ε)`-multiplicative for every `ε`, so the model is *exact*;
* take `S = A`, so `|S| = |A| > (1−ε)|A|` and the density clause holds with
  room to spare — there is no deleted set at all;
* take `B = V(Θ)` and `j_a = π_a`.  A graph embedding is injective on
  vertices, so `j_a(p) ≠ j_a(q)` for every `a ∈ A`, which is the distinctness
  clause;
* the displayed identity is the equivariance clause, in the stronger form
  where it holds for all `a` rather than only where both sides are defined.

So an exact model with an empty deleted set carries two-point label data at
the marked pair for the window `F₀`.  The prerequisite says no exact model
does, at any `ε < ε₀`.  Contradiction.

Injectivity of `π_a` is what the argument uses, so the conclusion does not
depend on the marked edge lying in `S`: the obstruction is already in the
underlying `G`-set `X`, and it therefore covers every `G`-invariant graph
over it at once.  The marked pair is where the prerequisite has teeth, which
is why `W` is chosen there.

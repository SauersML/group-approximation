---
rg: 2
id: marked-graph-action-not-residually-finite
kind: claim
title: No invariant graph over the Kun--Thom coset space has a residually finite action in the graph-wreath sense
distinct_from:
  exact-models-cannot-separate-marked-pair: that is the quantitative theorem about exact finite G-actions with an epsilon-density deleted set at the marked pair; this is the identification of one published hypothesis — Definition 2.6 of arXiv:2607.29571 — as a special case of the data that theorem forbids, which is what deletes the graph-wreath MF theorem from this lane's toolbox.
  coordinate-action-not-sofic: that refutes soficity of the coordinate action, an approximate property with a deleted set; this refutes an exact property, and it is about the charts a specific published MF theorem requires.
  two-point-approximation-fails: that is the general refutation over all approximately multiplicative models; this reduces one exact, genuine-homomorphism hypothesis to the exact-model theorem, which is cheaper and gives an explicit window.
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

Let `Γ < G` be the Kun--Thom Theorem E pair, `X = G/Γ`, and let `S` be any
`G`-invariant graph on `X` — the empty graph, the minimal marked graph
`S_min`, the complete graph, or anything between.

**Claim.**  The action `G ↷ (X, S)` is **not** residually finite in the sense
of Gao--Kunnawalkam Elayavalli--Mj, `arXiv:2607.29571`, Definition 2.6: there
is a finite `F ⊆ G` and a two-element `W ⊆ X` for which no finite graph `Θ`,
finite set `A`, homomorphism `φ : G → Sym(A)` and family of graph embeddings
`π_a : (W, E|_{W×W}) ↪ Θ` satisfy `π_{φ(g)a}(v) = π_a(g^{-1}v)`.

One may take `W = {Γ, hΓ}` the marked pair and `F = S_Γ ∪ S_Γ^{-1} ∪ {h}`,
the explicit window of `exact-models-cannot-separate-marked-pair`.

**Consequence.**  The graph-wreath MF theorem of [GKM26] does not apply to any
Kun--Thom invariant-graph lamp model, `S_min` included; nor does their
generalized-wreath/Bernoulli line, whose separable-stabilizer hypothesis
plays the same role.  Together with `lamp-coordinate-collision-obstruction`
this closes the whole finite-coordinate family of architectures for this pair
from two independent directions: the set-theoretic charts cannot exist, and
even if one ignored the charts and only asked for tracial convergence, a
coordinate identification would already be wrong at second moments.

The claim is not a criticism of [GKM26]: their theorems hold under their
hypotheses, and the Kun--Thom pair simply fails those hypotheses — as it must,
since a residually finite action in their sense makes the coset action sofic,
which `coordinate-action-not-sofic` forbids.

## Scope

This is about exact data — a genuine homomorphism into a finite symmetric
group with no deleted set.  It therefore says nothing new about approximate
models, where the live statement remains `two-point-approximation-fails`, and
it does not restrict which *quantum* finite-dimensional models may exist.

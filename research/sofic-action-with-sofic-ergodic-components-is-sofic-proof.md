---
rg: 2
id: sofic-action-with-sofic-ergodic-components-is-sofic-proof
kind: route
title: Finite models of the components, weighted by the ergodic decomposition, assemble by disjoint union into models of the action
target: sofic-action-with-sofic-ergodic-components-is-sofic
requires:
  - paunescu-sofic-action-class-permanence
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md
---

Full proofs: artifact Sections 2 (Lemma LC) and 3 (Lemma ED, Corollary ED).

**Lemma LC (finite models).** Fix increasing finite generating partitions `P_m` of `X` and finite sets
`F_m ↑ G`. Let `𝒲_m` be the words of length `<= m` in `u_g, u_g^*` (`g ∈ F_m`) and `1_p`
(`p ∈ P_1 ∪ ... ∪ P_m`). A model of level `m` and error `ε` is a finite set `Y` with permutations
`σ(g)` (`g ∈ F_m`) and a partition `(Y_p)_(p ∈ P_m)` whose normalized traces of all words in `𝒲_m`
are within `ε` of `τ(w)`. The action is sofic iff models of every level and error exist.
(⇒) lift a sofic embedding, lifting partitions of unity in the diagonal ultraproduct to partitions as
in Păunescu Lemma 1.6. (⇐) an ultraproduct of models reproduces every word trace; since words are
closed under products and adjoints, this defines a trace-preserving ∗-embedding of a weakly dense
∗-subalgebra, which extends to the crossed product with the base in the diagonal and `u_g` in the
permutations.

**Lemma ED.** A word `w` equals `1_(B_w) u_(h_w)`, so `τ_μ(w) = δ_(h_w,1) μ(B_w)` is affine in `μ`, and
`τ_μ(w) = ∫ τ_(μ_t)(w) dν(t)`. Given `m, ε`, the finite vector `(τ_μ(w))_(w ∈ 𝒲_m)` lies in the closed
convex hull of the vectors of the sofic components. Pick finitely many components and rational
weights `a_j/b` within `ε/2`, take models of error `ε/2` for each, and form the disjoint union of
`c_j = a_j N/|Y_j|` copies of the `j`-th model (`N = Π|Y_i|`). Normalized traces of words on the union
are the weighted averages, so the union is a model of error `ε` for `μ`. Lemma LC (⇐) finishes.

**Corollary.** If `G ∉ 𝒮`, Păunescu Theorem 3.1 (imported in `paunescu-sofic-action-class-permanence`)
gives a free nonsofic action. By Lemma ED, the nonsofic components are not contained in any null set,
so one of them is ergodic and essentially free.

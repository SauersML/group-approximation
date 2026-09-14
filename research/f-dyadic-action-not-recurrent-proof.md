---
rg: 2
id: f-dyadic-action-not-recurrent-proof
kind: route
title: Transience of the dyadic Schreier graph gives a positive escape probability, so the mean inverted orbit grows linearly
target: f-dyadic-action-is-not-recurrent
requires: []
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**Sources.**
- K. Juschenko, N. Matte Bon, N. Monod, M. de la Salle, arXiv:1503.04977, the lemma quoted below (read at
  source 2026-09-14).
- P. Mishchenko, *Boundary of the action of Thompson group F on dyadic numbers*, arXiv:1512.03083, for
  transience of the dyadic Schreier graph (already pinned in
  `thompson-f-dyadic-action-is-extensively-amenable`; not re-read here).

**Step 1 (mean inverted orbit and escape probability).** Verbatim from JMBMdlS: "Assume that `G` is finitely
generated and the action `G ↷ X` is transitive. Then `G ↷ X` is recurrent if and only if `(1/n) E|O_n| → 0`
for some (equivalently for any) non-degenerate symmetric, finitely supported probability measure `μ` on
`G`." Their proof computes, with `T = min{n ≥ 1 : g_n x_0 = x_0}`,

`E|O_{n+1}| − E|O_n| = P(g_{n+1}⁻¹ x_0 ∉ O_n) = P(T > n+1)`,

using that by symmetry `(h_{n+1}⁻¹, h_n⁻¹h_{n+1}⁻¹, …, h_1⁻¹⋯h_{n+1}⁻¹)` has the same law as
`(g_1, …, g_{n+1})`. Summing and using monotone convergence, `(1/n) E|O_n| → P(T = ∞)`.

**Step 2 (transience of the dyadic action).** `F ↷ D` is transitive and finitely generated. Its Schreier
graph at `x_0` is the dyadic Schreier graph. Recurrence/transience of simple random walk on a graph of
bounded degree is independent of the non-degenerate symmetric finitely supported step measure with
generating support, so it is a property of the graph. A recurrent graph is Liouville (trivial Poisson
boundary). Mishchenko proves the dyadic Schreier graph has nontrivial Poisson boundary; hence it is not
recurrent, i.e. it is transient. Therefore the induced walk `g_n x_0` is transient and `P(T = ∞) > 0`.

**Step 3 (conclusion).** By Step 1, `(1/n) E|O_n| → P(T = ∞) > 0`, so `F ↷ D` is not recurrent, and the
mean-confinement condition `(1/n) E|O_n| → 0` fails for every admissible `μ`. This leaves only the
rare-event condition (ii) of `f-dyadic-ea-iff-inverted-orbit-confinement` as a route to extensive
amenability through the inverted orbit.

**No novelty.** The lemma is quoted from the source; the only added step is combining it with the already
pinned transience result.

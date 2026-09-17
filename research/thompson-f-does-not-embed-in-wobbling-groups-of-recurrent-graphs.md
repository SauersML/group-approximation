---
rg: 2
id: thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs
kind: claim
title: "For every connected recurrent graph of bounded degree and every homomorphism from F to its wobbling group, F′ acts trivially; so F does not embed in such a wobbling group, and no group containing F acts faithfully by bounded displacement on one"
distinct_from:
  thompson-f-confined-subgroups-fix-finite-sets: that imports Chaudkhari's non-embeddability of F into wobbling groups of graphs with uniformly subexponential growth; this settles the recurrent case, which Chaudkhari's final remarks leave open.
  thompson-f-recurrent-f-sets-factor-through-the-abelianization: that is the statement about recurrent Schreier graphs of F; this transfers it to bounded-displacement actions on recurrent graphs through rough embeddings.
  thompson-f-point-orbits-are-transient: that proves transience of particular F-sets; this forbids every faithful bounded-displacement action of F on a recurrent graph.
---

**ESTABLISHED.** **Setting.**
- `Γ` is a connected graph with vertex set `V`, degrees at most `D < ∞`, and unit conductances. It is
  recurrent.
- The wobbling group `W(Γ)` is the group of bijections `g` of `V` with
  `sup_(v ∈ V) d_Γ(v, g v) < ∞`.

**Statement.**
1. For every group `G ⊇ F` and every homomorphism `ρ : G → W(Γ)`, the subgroup `ρ(F′)` is trivial.
   In particular `F` does not embed in `W(Γ)`.
2. The same holds for any finitely generated `G ⊇ F` acting on `V` whose generators move each vertex
   a bounded distance.

**Context.** Chaudkhari (arXiv:1809.05146v2, final remarks, read from the arXiv source on 2026-09-17)
writes: "We still do not know whether $F$ could be embedded into a wobbling group of a recurrent
graph with bounded degree". Item 1 answers this negatively.
- Embeddings into `W(Γ)` with `Γ` recurrent are the standard engine for extensive amenability, as
  in Juschenko–Monod and Juschenko–Matte Bon–Monod–de la Salle.
- So that engine cannot reach `F`, nor any group containing `F` faithfully, through a recurrent graph.

**Scope.** Elementary given `thompson-f-recurrent-f-sets-factor-through-the-abelianization` and
Lyons–Peres Theorem 2.17. Graphs of uniformly subexponential growth, such as `Z^d`, are covered by
Chaudkhari's Theorem 4.1 (see `thompson-f-confined-subgroups-fix-finite-sets`). The question for
transient graphs of subexponential but non-uniform growth is untouched.

Proof route: `thompson-f-not-in-recurrent-wobbling-groups-proof`.

---
rg: 2
id: oyakawa-graph-wreath-hyperbolic
kind: claim
title: Oyakawa's graph-wreath products over large-girth hyperbolic graphs are hyperbolic
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Oyakawa, *Infinite graph product of groups I: Geometry of the extension
graph*, arXiv:2409.09527v3 (v1 2024-09-14, v3 2026-03-13), Corollary 1.4,
read verbatim from source 2026-08-17:

> Suppose that Γ is a locally finite hyperbolic graph with girth(Γ)>20 and
> that a group G acts on Γ properly and cocompactly.  Let H be a finite group
> and define 𝒢={G_v}_{v∈V(Γ)} by G_v=H for any v∈V(Γ).  Then, Γ𝒢⋊G is
> hyperbolic.

Here `Γ𝒢` is the graph product of the vertex groups over the defining graph,
so `Γ𝒢⋊G` is a graph-wreath product: distinct **adjacent** coordinates
commute, distinct non-adjacent ones generate freely, and `G` permutes them.

The same paper's Theorem 1.3 gives a relative version — for a fine hyperbolic
graph of girth `>20` with finite edge stabilizers and finitely generated
vertex stabilizers, the graph-wreath product is hyperbolic relative to an
explicit finite collection of subgroups `⟨Stab_G(v), G_w ∣ w ∈ St_Γ(v)⟩`.

Both hypotheses are sharp in the way one expects: with `|H| = ∞` or with short
cycles the product contains `ℤ^2`, which no hyperbolic group does.

## Why this graph carries it

Because it is a genuinely new source of hyperbolic groups — the construction
postdates every no-go in `notes/OBSTRUCTIONS.md` — and because Oyakawa points
at exactly the question this region is about, recording that studying residual
finiteness of these groups "might shed light on the long-standing open problem
asking whether every hyperbolic group is residually finite".  That suggestion
is answered, negatively, by
`oyakawa-graph-wreath-rf-iff-acting-group-rf`.

Imported, not proved here: the statement was read verbatim from the source,
the proof was not audited.

---
rg: 2
id: needham-graph-wreath-rf-criterion
kind: claim
title: Needham's exact residual finiteness criterion for graph wreath products
distinct_from:
  wreath-compression-mf-radical: that computes MF radicals of this program's compression wreath products — an operator approximation invariant of a specific Kazhdan family; this is an imported residual finiteness criterion for graph wreath products over an arbitrary graph action, purely group-theoretic, with the separability of the action carrying all of the content
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Needham, *Residual Finiteness of Graph Wreath Products*, arXiv:2509.11170
(2025-09-14).  Abstract, read from source 2026-08-17: "We prove necessary and
sufficient conditions for when graph wreath products are residually finite,
generalising known results for the permutational wreath product and free
product cases."

Theorem 1.1, conditions as read from the source: for groups `Γ, Δ` and a graph
`G = (V,E)` on which `Γ` acts, the graph wreath product `G(Δ) ⋊ Γ` is
residually finite **if and only if**

1. `Γ` and `Δ` are residually finite;
2. either `Δ` is abelian and for all neighbouring `v, w ∈ V` there is a finite
   index subgroup `K ≤ Γ` with `w ∉ Kv`; or for all `v` there is a finite
   index `K ≤ Γ` with `Kv ∩ N(v) = ∅`;
3. for all `v, w` not neighbouring and not equal there is a finite index
   `K ≤ Γ` with `Kw ∩ (N(v) ∪ {v}) = ∅`.

Note the shape: two separation conditions on the **action**, both of the form
"a finite-index subgroup moves this vertex away from that neighbourhood", plus
residual finiteness of the two group inputs.  Conditions 2 and 3 are where the
criterion can fail for residually finite `Γ` and `Δ` — the failure is a
profinite-separability failure of the action, not of either group.

Imported, not proved here: statement read from source, proof not audited.

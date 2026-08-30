---
rg: 2
id: amenable-action-invariant-trace-amenability-proof
kind: route
title: Nuclearity of the crossed product and a finite injective expectation
target: amenable-action-invariant-trace-forces-amenability
requires: []
---

Since `α` is amenable and `A` nuclear, `A ⋊_r G` is nuclear
(Anantharaman-Delaroche, Théorème 4.5).  The invariant trace `τ`
composed with the canonical expectation `E : A ⋊_r G → A` is a tracial
state `τ̃` on the crossed product, and its restriction to the canonical
copy of `C*_r(G)` is the canonical trace (for `g ≠ e`,
`τ̃(a u_g) = τ(E(a u_g)) = 0`).  The GNS von Neumann algebra
`M = π_{τ̃}(A ⋊_r G)''` is injective because `A ⋊_r G` is nuclear, and
it is finite with the faithful normal trace extending `τ̃` on the weak
closure of the (unitalized) image.  The weak closure `N` of
`π_{τ̃}(C*_r(G))` is a von Neumann subalgebra of the finite injective
`M`, so the trace-preserving conditional expectation `M → N` exists
and `N` is injective.  Since `τ̃` restricts to the canonical trace on
`C*_r(G)`, `N` is (a quotient corresponding to) `L(G)` — the GNS
representation of the canonical trace — so `L(G)` is injective, and by
Connes `G` is amenable.

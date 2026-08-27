---
rg: 2
id: shift-raag-family-rf-proof
kind: route
title: Fold a closure point onto an edge in every finite quotient, and separate through right-angled Artin groups of cyclic graphs
target: shift-raag-family-is-rf-iff-symmetrized-index-set-closed
requires:
  - shift-raag-family-classifies-amenability
---

By [[shift-raag-family-classifies-amenability]], `G_J = A(Gamma_J) x| <t>`
with `a_i = t^i a t^-i`, `Gamma_J` the graph on `Z` with `u -- v` iff
`v - u in J^s \ {0}`.

**Not closed implies not residually finite.**  Let
`d in cl(J^s) \ J^s`; then `d != 0` and `{0, d}` is a non-edge, so
`g = [a_0, a_d] != 1` (two non-adjacent vertices of a right-angled Artin
group generate `F_2`).  Let `chi` be a homomorphism to a finite group and
`m` the order of `chi(t)`.  Closedness gives `j in J^s` with `d = j + km`,
so `chi(a_d) = chi(t^{d} a t^{-d}) = chi(t^{j} a t^{-j}) = chi(a_j)`.  If
`j = 0` this is `chi(a_0)`; if `j in J u (-J)` then `{0, j}` is an edge.
Either way `chi(a_0)` commutes with `chi(a_d)`, so `chi(g) = 1`.

**Closed implies residually finite.**  Let `g = n t^k != 1` with `n in
A(Gamma_J)`.  If `k != 0`, the quotient `Z/m`, `t |-> 1`, `a |-> 0`, with
`m` not dividing `k`, separates `g`.  If `k = 0`, `n` is a nontrivial
reduced word in the `a_i` with `|i| <= r`.  For each pair `i, i'` in that
window with `i - i' notin J^s` choose `m_{i,i'}` with
`(i - i' + m_{i,i'} Z) n J^s` empty, and let `m > 2r` be a common
multiple of these moduli.  The assignment `a |-> a_0`, `t |-> ` the
generator of `Z/m`, defines a homomorphism `G_J -> A(Gamma_{J,m}) x| Z/m`
because every edge `{i, i+j}` of `Gamma_J` maps to an edge.  On the
window it is injective on vertices (`m > 2r`), sends edges to edges, and
sends non-edges to non-edges (a difference `d` with `(d + mZ) n J^s`
empty is neither `0` nor in `J mod m` nor in `-J mod m`).  So the window
maps isomorphically onto a full subgraph of `Gamma_{J,m}`, whose
right-angled Artin group is a retract of `A(Gamma_{J,m})`; hence `n` maps
to a nontrivial element.  Finally `A(Gamma_{J,m})` is a finitely generated
right-angled Artin group, residually finite, and its extension by the
finite group `Z/m` is residually finite, so some finite quotient
separates the image of `g`.

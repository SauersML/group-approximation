---
rg: 2
id: finite-stencil-pauli-periodization-proof
kind: route
title: Periodize the finite stencil on a longer cyclic Pauli tape
target: finite-stencil-pauli-tape-has-marked-periodizations
requires: []
---

For nonempty `D`, choose `m>max_{r in D}|r|`; for empty `D`, choose any
positive `m`.  On `(C^2)^(tensor m)`, let `p_i` and `q_i` be Pauli `X` and
`Z` on tensor factor `i`, and put `J=-I`.  These generate a finite central
product `K_m`: same-site pairs have commutator `J`, distinct sites commute,
and every displayed involution and centrality relation holds.

Let `P` cyclically permute the tensor factors.  Conjugation by `P` sends
`p_i,q_i` to `p_(i+1),q_(i+1)` and fixes `J`, so it defines an automorphism
of order `m`.  Map

```text
t |-> P,       p |-> p_0,       q |-> q_0,       J |-> -I.
```

For every `r in D`, the residue `r mod m` is nonzero because
`0<|r|<m`.  The translated letter therefore lies at a site distinct from
zero and commutes with either base Pauli letter, exactly verifying every
stencil relation.  The target `K_m rtimes <P>` is finite, while the marked
central involution remains `-I` and satisfies normalized
`||J-I||_2=2`.

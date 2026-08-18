---
rg: 2
id: basis-free-polynomial-unitary-observables-are-word-tracial
kind: claim
title: Polynomial basis-free observables of a unitary tuple contain only trace-word data
---

Fix a matrix size `d` and finitely many unitary variables `U_1,...,U_m`.
Every polynomial function of their matrix entries and conjugate entries that
is invariant under simultaneous unitary conjugation

```text
(U_1,...,U_m) |-> (Q U_1 Q^*,...,Q U_m Q^*)
```

is a polynomial in traces of `*`-words

```text
Tr(U_(i_1)^(eps_1) ... U_(i_k)^(eps_k)),   eps_j in {1,*}.
```

Consequently, on a hyperlinear group microstate, every fixed-degree
polynomial simultaneous-conjugacy invariant is asymptotically determined by
ordinary word traces once the finite window has been enlarged to contain the
finitely many group words occurring in the trace generators.

In particular a basis-free **polynomial** replacement for raw branching
traffic cannot create a new bounded-window correlation beyond character/word
trace data.  Any successful traffic-style reconstruction must therefore use
non-polynomial structure or extra synchronized variables (for example a
Cartan/basis, a POVM, a point cloud, or a relative distribution), not merely
average an entrywise traffic polynomial over conjugacy.

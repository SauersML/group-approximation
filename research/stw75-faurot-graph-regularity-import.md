---
rg: 2
id: stw75-faurot-graph-regularity-import
kind: route
title: Import Faurot's acyclic and finite-ideal graph regularity theorems
target: stw75-acyclic-or-finite-ideal-graph-regularity-package
requires: []
---

Faurot, *Z-stable Graph Algebras*, arXiv:2511.02760v2, Theorem C, proves for
every countable row-finite graph `E` that

```text
Condition (K) + distinct detours
  <=> no elementary subquotients
  <=> purity.
```

Under either hypothesis in the claim, Faurot's Theorem A proves

```text
distinct detours
  <=> no elementary subquotients
  <=> C*(E) tensor Z isomorphic to C*(E).
```

The observation following Theorem A supplies Condition (K) in these cases, so
Theorems A and C combine to give the four stated equivalences.

Faurot--Schafhauser, *Nuclear dimension of graph C-star algebras with
Condition (K)*, Proc. Amer. Math. Soc. 152 (2024), 4421--4435,
Theorem A (arXiv:2310.15073v2), gives nuclear dimension at most two.
In the acyclic case the graph algebra is AF, hence has nuclear dimension zero.

Finally, for a Z-stable algebra the absorbing isomorphism can be chosen
approximately unitarily equivalent to the first-factor embedding. Functoriality
and approximate-unitary invariance of `Cu` therefore make the displayed
first-factor Cu morphism an isomorphism. QED

This does not prove Faurot's Conjecture 4.1 for arbitrary row-finite graphs and
does not settle Problems LXXV or LXXVI outside the stated subclass.

---
rg: 2
id: harris-three-dimensional-llp-witness-citation
kind: route
title: Import Harris's three-dimensional hyperrigid LLP witness
target: llp-failure-has-three-dimensional-hyperrigid-witness
requires: []
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

## Source theorem and finite-dimensional equivalence

Harris, arXiv:2607.11001v1, Theorem 2.4 constructs from finitely many
unitary generators of a unital C-star algebra `A` a three-dimensional
hyperrigid operator system

```text
S = span{I,D,G} subset M_(n+2)(A)
```

which generates the full matrix algebra.  Proposition 3.4(2) states that
for a hyperrigid subsystem, LLP of `S` implies LLP of its ambient C-star
algebra.  Since `S` is finite-dimensional, LP and LLP coincide for `S`.
Thus LP of this Harris system implies LLP of `M_(n+2)(A)`, hence LLP of
`A` by matrix/corner permanence.

Conversely, LLP of `A` passes to `M_(n+2)(A)`; applying the definition of
LLP to the finite-dimensional subsystem `S` gives LP of `S`.  Therefore
for this particular Harris system

```text
LP(S) <=> LLP(A).
```

If `A` fails LLP, Corollary 3.5 consequently gives the same explicit
three-dimensional hyperrigid `S` failing LP, which is exactly the target
claim.

---
rg: 2
id: finite-relator-profile-synthesis-is-cnf
kind: claim
title: Finite bad-profile relator synthesis is an exact monotone-CNF problem with collapse-avoidance clauses
distinct_from:
  finite-moment-random-relator-sparsification: that theorem proves a probabilistic all-dimensions sparsification once a robust relator menu is available; this claim compiles any already-discretized finite selection problem into a checkable Boolean instance.
  robust-locally-satisfiable-relator-code: that is the mathematical existence of a robust noncommutative code; this claim is only the exact finite synthesis backend after profile and collapse certificates have been supplied.
---

Let `P` be a finite set of bad profile cells and `R` a finite relator menu. For
`r in R`, let `V_r subset P` be the cells on which `r` witnesses the required
violation. Let `C_1,...,C_t subset R` be finite collapse certificates, with the
meaning that selecting every relator in `C_j` is forbidden because it destroys
a protected short-ball condition.

Then a selected set `S subset R` hits every bad profile and contains no complete
collapse certificate if and only if its Boolean incidence vector satisfies

```text
AND_(p in P)  ( OR_(r : p in V_r) x_r )
AND
AND_j         ( OR_(r in C_j) not x_r ).
```

Thus the discretized synthesis stage is exactly a CNF/SAT instance: positive
hitting clauses for soundness and negative hyperedge clauses for local
satisfiability. Any satisfying assignment is a directly checkable finite
certificate.

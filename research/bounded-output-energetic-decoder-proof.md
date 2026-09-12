---
rg: 2
id: bounded-output-energetic-decoder-proof
kind: route
title: Pass to one output dimension and use compactness of its unitary tuple space
target: bounded-output-energetic-decoder-gives-the-canonical-ceiling
requires: []
---

Assume `G` is hyperlinear and choose a canonical-profile sequence `U_n`.
Finite trace-polynomial moment convergence gives

```text
E(U_n)->E_reg.                                           (1)
```

Apply `(BOD1)`.  Since `r_n` takes only the values `1,...,D`, pass to a
subsequence on which `r_n=r` is constant.  Compactness of the finite product
`U(r)^X` gives a further subsequence converging entrywise to a tuple
`V in U(r)^X`.  Continuity of every defining word and
`def_R(V_n)->0` show that

```text
r(V)=I                  for every r in R,
```

so `V` is an exact `r`-dimensional representation of `G`.  Continuity of
`E`, `(BOD1)`, and `(1)` give

```text
E(V)=lim E(V_n)>=E_reg.
```

Therefore `beta_fd>=E_reg`, proving `(BOD2)`.  Notice that neither the choice
of subsequences nor the convergence rate must be effective; reverse Kleene
uses exact finite-dimensional excess search only after the qualitative
NONHALT implication has been established.


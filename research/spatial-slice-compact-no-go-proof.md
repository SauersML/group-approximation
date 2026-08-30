---
rg: 2
id: spatial-slice-compact-no-go-proof
kind: route
title: A nonzero compact slice would make one pure factor non-nowhere-scattered
target: spatial-pure-factor-reps-have-no-joint-compacts
requires: []
---

Assume that a nonzero compact operator

```text
k in pi_A(A) tensor_min pi_B(B)
```

exists.  Normal slice maps separate operators on `H_A tensor H_B`, so there
are vectors `xi,eta in H_B` for which

```text
t=(id tensor omega_(xi,eta))(k)
```

is nonzero.  Slicing a compact operator gives a compact operator on `H_A`,
while slicing an element of the minimal C-star tensor product gives an element
of `pi_A(A)`.  Hence

```text
0 != t in pi_A(A) intersect K(H_A).
```

But purity implies nowhere scatteredness, and nowhere scatteredness says that
every irreducible image is disjoint from the compact operators.  This is a
contradiction.  (Slicing in the other direction gives the symmetric
contradiction in `B`.)

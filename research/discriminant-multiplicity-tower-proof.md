---
rg: 2
id: discriminant-multiplicity-tower-proof
kind: route
title: Within-block root pairs pull back a power of the earlier discriminant, which is nilpotent
target: discriminant-obstruction-dies-in-multiplicity-towers
requires: []
---

**Factorization.**  Write `F_i=lambda_i^* E_j tensor V_i`, with roots
`lambda_i^* t_a + v_(i,c)`.  The pairs of roots with the same `i` and the same
`c` contribute `prod_c prod_(a<b) (t_a-t_b)^2 = Delta(E)^(rank V_i)`.  All
remaining pair differences form a product symmetric under permuting roots
inside each `E`-copy and each `V`-copy, hence a universal integral class `W`.
Pulling back along classifying maps and using naturality
`lambda^* Delta(E_j)=Delta(lambda^* E_j)`,

```text
Delta(E_(j+1)) = prod_i lambda_i^*( Delta(E_j)^(rank V_i) ) * W.
```

All classes are in even degree, so the cohomology ring involved is commutative.

**Induction.**  If `Delta(E_j)^e=0` then `Delta(E_j)^(e rank V_i)=0`, and the
displayed factorization gives `Delta(E_(j+1))^e=0`.  Contrapositively,
`Delta(E_j)^e != 0` implies `Delta(E_(j0))^e != 0` for any earlier stage
`j0`.

**Nilpotence.**  Fix `j0` with `N_(j0)>=2`.  Since `X_(j0)` is compact,
`E_(j0)` is a summand of a trivial bundle of finite rank, so it is pulled back
from a finite Grassmannian `G`.  The class `Delta(E_(j0))` is the pullback of
the universal discriminant in `H^(2N(N-1))(G; Z)`, positive degree on a
finite-dimensional manifold, so some power `e_0` vanishes on `G` and hence on
`X_(j0)`.

**Conclusion.**  For every `j` with `floor(N_j/2)>=e_0`, the induction gives
`Delta(E_j)^(floor(N_j/2))=0`.  Such `j` exist and include all large `j`
because `N_j -> infinity`.

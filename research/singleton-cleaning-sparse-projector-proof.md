---
rg: 2
id: singleton-cleaning-sparse-projector-proof
kind: route
title: Assemble singleton erasure cleaners into a sparse code projection
target: full-row-rank-cleaning-forces-zero-code
requires: []
---

Full row rank makes `H` surjective.  For each row basis vector `e_a`, choose
`x_a` with `H x_a=e_a`.  Applying `(FRC1)` gives

```text
x_a=c_a+y_a,  c_a in ker(H),  supp(y_a) subset S_a,
H y_a=e_a,  wt(y_a)<=ceil(K/rho).
```

Let `Y:F_2^M -> F_2^L` have columns `y_a`.  Then `HY=I_M`.  Define

```text
P=I_L-YH.
```

We have `HP=0`, while `Pc=c` for every `c in ker(H)`.  Thus `P` is a
projection onto `C`.  For a coordinate vector `e_j`, the column `He_j`
has at most `d` nonzero entries, so

```text
wt(Pe_j) <= 1+d ceil(K/rho).
```

Each `Pe_j` belongs to `C`.  If the code minimum distance exceeds this
bound, every `Pe_j` is zero.  Hence `P=0`, and because `P` is the identity
on `C`, the code is zero.

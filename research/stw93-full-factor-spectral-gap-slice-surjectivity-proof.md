---
rg: 2
id: stw93-full-factor-spectral-gap-slice-surjectivity-proof
kind: route
title: Use full-factor spectral gap to push every tracial central sequence into the hyperfinite tensor factor
target: stw93-jiang-su-slice-exhausts-tracial-central-quotient
requires:
  - stw93-super-mcduff-tracial-central-quotient
---

Write

```text
N=L(F_2),        M=N tensor_bar R.
```

The free group is not inner amenable.  Equivalently, its conjugation
representation on `ell^2(F_2 minus {e})` has spectral gap.  Under the
canonical identification of this representation with the adjoint action on
`L^2(N) minus C1`, this gives group unitaries `u_1,...,u_m in N` and a
constant `C` such that

```text
norm(xi)_2^2 <= C sum_j norm(u_j xi-xi u_j)_2^2          (1)
```

for every `xi in L^2(N) minus C1`.  Tensoring the positive-operator
inequality behind (1) with the identity on `L^2(R)` gives the same estimate
on

```text
(L^2(N) minus C1) tensor L^2(R).
```

Let `E_R:M->1 tensor R` be the trace-preserving conditional expectation.
For `x in M`, the vector `x-E_R(x)` lies in this tensor-product subspace,
and `E_R(x)` commutes with every `u_j tensor 1`.  Hence (1) gives

```text
norm(x-E_R(x))_2^2
  <= C sum_j norm([x,u_j tensor 1])_2^2.                 (2)
```

Now represent an element of `M^omega intersect M'` by a norm-bounded
sequence `(x_n)`.  Centrality and (2) imply

```text
lim_(n->omega) norm(x_n-E_R(x_n))_2=0.                  (3)
```

Put `y_n=E_R(x_n)`, viewed in `R`.  The sequence remains norm bounded.  For
every `r in R`, bimodularity and `2`-norm contractivity of `E_R` give

```text
norm([y_n,r])_2
  =norm(E_R([x_n,1 tensor r]))_2
  <=norm([x_n,1 tensor r])_2 ->_omega 0.
```

Thus `[(y_n)]` belongs to `R^omega intersect R'`, and (3) says that its
image in `M^omega intersect M'` is the original class.  Therefore the
canonical map

```text
R^omega intersect R' -> M^omega intersect M'
```

is onto.

Kirchberg--Rordam central surjectivity applied to the faithful unique trace
of `Z` says that

```text
F(Z) -> R^omega intersect R'
```

is onto.  Combining the two surjections with the canonical identification

```text
D/I ~= M^omega intersect M'
```

from `stw93-super-mcduff-tracial-central-quotient` proves that
`F(Z)->D/I` is onto.

Its kernel is exactly `E`.  Indeed, tensoring representatives with the unit
of `C*_r(F_2)` preserves the tracial `2`-norm, so

```text
iota(z) in I  iff  tau_(Z,omega)(z*z)=0  iff  z in E.
```

The first isomorphism theorem gives `F(Z)/E ~= D/I`.  Surjectivity is
equivalent to `D=I+iota(F(Z))`, and the kernel computation gives the
intersection formula in `(Q)`.

**Trust boundary.**  The only factor-theoretic input beyond the established
tracial-quotient identification is the standard adjoint spectral gap for the
non-inner-amenable free group, which is also the spectral gap underlying
fullness of `L(F_2)`.  Inequality (2) makes explicit why that estimate
survives tensoring for this purpose.  The result does not split the extension
`0->I->D->D/I->0` and does not imply that quasitraces annihilate `I`.

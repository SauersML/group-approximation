---
rg: 2
id: direct-ck-corner-core-infinite-bi-index-proof
kind: route
title: Separate double cosets by the elementary root subgroup in the unused matrix corner
target: direct-ck-corner-core-has-infinite-bi-index
requires: []
---

Write `D=d(H)` and `x_a=e_23(a)`.  Since every element of `D` is supported
on the first matrix coordinate while `x_a` is supported in position `(2,3)`,

```text
[D,x_a] = 1
```

for every `a in U`.  Moreover

```text
D cap {x_a : a in U} = {1}.
```

Indeed, if `diag(h,1,...,1)=e_23(a)`, comparison of the `(1,1)` entry gives
`h=1`, and comparison of the `(2,3)` entry gives `a=0`.

Suppose `D x_a D = D x_b D`.  Then there are `d_1,d_2 in D` with
`x_b=d_1 x_a d_2`.  Commutation gives

```text
x_(b-a) = x_a^(-1)x_b = d_1 d_2 in D.
```

The trivial-intersection calculation forces `b-a=0`.  Thus `a=b`, proving
injectivity of `a |-> D x_a D`.

For the CK specialization, the primary construction embeds
`[Gtilde,Gtilde]` in `EL_n(Z[Gtilde])` by putting a group element in the
upper-left corner.  The repository's universal-sandwich theorem embeds
`Z[Gtilde]` in `U`; therefore the same corner copy of the simple core lies
in `EL_4(U)`.  Since `Z[Gtilde]` is infinite, so is `U`, and the theorem
gives infinitely many simple-core double cosets.  QED

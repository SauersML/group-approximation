---
rg: 2
id: two-grade-unitary-collapse-proof
kind: route
title: Compare the source and range partitions of a two-grade crossed-product unitary
target: cyclic-aperiodicity-collapses-two-actor-grade-unitaries
requires: []
---

Assume `g!=h`. Since `H` is torsion-free, the two
nonidentity grades `g^(-1)h` and `h^(-1)g` are distinct. The off-diagonal
Fourier coefficients of `X^*X=1` therefore vanish separately:

```text
a^*b=0,                                                (TGU1)
```

while the identity coefficient of `XX^*=1` is

```text
|a|^2+|b|^2=1.                                        (TGU2)
```

Pointwise, `(TGU1)`--`(TGU2)` say that `p=|a|^2` and `q=|b|^2` are
complementary characteristic functions. In particular `a` and `b` are
unimodular on their respective supports.

The identity coefficient of `X^*X=1` also gives

```text
alpha_(g^(-1))(p)+alpha_(h^(-1))(1-p)=1.              (TGU3)
```

Applying `alpha_h` yields

```text
alpha_(h g^(-1))(p)=p.                                (TGU4)
```

The element `h g^(-1)` is nonidentity, so `(CAT1)` makes its dual action
ergodic. The invariant projection `p` is therefore `0` or `1`, which proves
`(CAT4)`.

For completeness, the equivalence used above is the standard character
criterion for ergodicity of a compact abelian automorphism: `r` is ergodic on
`dual(A)` exactly when every nonzero character `a in A` has an infinite
`<r>`-orbit, equivalently when `(r^n-1)a!=0` for every `n>=1`.
---

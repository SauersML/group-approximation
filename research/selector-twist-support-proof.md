---
rg: 2
id: selector-twist-support-proof
kind: route
title: Tensor packet irreducibles by edge-trivial characters
target: selector-edge-type-support-is-twist-invariant
requires: []
---

Let

```text
X_E={chi in Hom(L,{+1,-1}):chi|_E=1},
H_E={chi|_A:chi in X_E}.
```

Tensoring by any `chi in X_E` permutes `Irr(L)` and does not change the
restriction to `E`.  Thus an irreducible `pi` contains `sigma` on `E` iff
`pi tensor chi` does.  Its `A`-weight set is the weight set of `pi`
multiplied by `chi|_A`.  Taking the union over all such `pi` proves
`R_sigma H_E=R_sigma`.

For `L=P times A` and `E<=P times B`, every character in `B^perp` extends
trivially over `P`, hence belongs to `H_E`.  Exact selected support `R`
therefore requires `B^perp<=Stab(R)`, or

```text
rank(B)>=rank(A)-rank(Stab(R)).
```

Under gauge doubling, let `ell:F_2^(2r)->F_2^r` add each pair of shares.
The lifted truth set is `R'=ell^-1(R)` and directly
`Stab(R')=ell^-1(Stab(R))`.  Rank-nullity gives

```text
rank(A')-rank(Stab(R'))=rank(A)-rank(Stab(R)),
```

so the private gauge kernel does not change the required logical rank.

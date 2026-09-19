---
rg: 2
id: a4-regular-context-is-centralizer-product-proof
kind: route
title: Compare the two implementers of the named regular A4 pair
target: a4-regular-context-is-centralizer-product
requires: []
---

Put `A=rho(a)` and `B=rho(b)`.

Assume first that the mixed pair `(A,U B U^*)` is equivalent to `(A,B)` with
the named generators fixed.  Thus there is a unitary `W` such that

```text
W A W^*=A,
W B W^*=U B U^*.
```

The first equality says `W in C_A`.  The second gives

```text
(U^*W) B (U^*W)^*=B,
```

so `U^*W in C_B`.  Therefore

```text
U=W (U^*W)^* in C_A C_B.
```

Conversely, write `U=X Y` with `X in C_A` and `Y in C_B`.  Then

```text
U B U^*=X B X^*,
X A X^*=A,
```

so `X` implements an equivalence from the canonical named pair `(A,B)` to the
mixed pair `(A,U B U^*)`.

Nothing in the argument depends on matrix size or multiplicity, so tensoring
all operators by an arbitrary identity preserves the equivalence verbatim.

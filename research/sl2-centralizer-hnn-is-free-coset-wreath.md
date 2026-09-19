---
rg: 2
id: sl2-centralizer-hnn-is-free-coset-wreath
kind: claim
title: The SL2 centralizer HNN is the free generalized wreath product over the dyadic vertex orbit
---

Let

```text
A=SL_2(Z[1/2]),   C=SL_2(Z),   X=A/C,
G=<A,t | [t,c]=1 for c in C>.
```

Then there is a canonical isomorphism

```text
G ~= ( *_(x in X) Z_x ) rtimes A = Z wr^*_(A curvearrowright X) A.   (FWH1)
```

Under this isomorphism `t` is the generator of the free factor at the base
coset `C`, and `a t a^(-1)` is the generator at `aC`.  Thus the full
canonical HNN character does not describe an ordinary Bernoulli lamp: the
distinct conjugate lamps are freely independent at the group level.

This identification is important for the Iwahori route.  The soficity of
the coset action is exactly an available sufficient condition for soficity
of the proposed HNN witness, by the free generalized wreath-product theorem.
The central element acts trivially on `X`, so this is the same set action as
the projective dyadic Bruhat--Tits vertex action.

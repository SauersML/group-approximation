---
rg: 2
id: relation-cocycles-preserve-full-group-rectangles
kind: claim
title: Relation cocycles preserve fixed-point traces and full-group rectangles
distinct_from:
  full-group-subgroup-trace-generation-dichotomy: that treats the canonical untwisted full-group unitaries and separates regular trace from Cartan generation; this proves that every normalized finite-rank relation-local-system twist retains both the fixed-point trace and a disjoint-support algebraic kernel.
  inverse-semigroup-globalization-cannot-groupify-nonru-bcs: that blocks amalgamating incompatible BCS support idempotents before groupification; this assumes full transformations already exist and detects a linear dependence after relation-local holonomy is added.
  projective-basis-character-criterion: that characterizes when an arbitrary GNS family gives a projective orthonormal basis; this rules out one natural twisted full-group family by an explicit four-term dependence without excluding unrelated projective bases.
---

Let `R` be a countable pmp equivalence relation on `(X,mu)`, let
`A=L^infinity(X)`, and let `Lambda <= [R]`.  Fix `n>=1` and a normalized
measurable unitary relation cocycle

```text
c:R -> U(n),
c(x,y)c(y,z)=c(x,z),             c(x,x)=1.
```

For the canonical full-group unitary `u_g in L(R)`, put

```text
a_g(x)=c(x,g^(-1)x),
w_g=a_g (u_g tensor 1_n) in M_n(L(R)).                 (RCR1)
```

Then `g |-> w_g` is a unitary representation and its normalized trace is
exactly the original fixed-point character:

```text
tau_n(w_g)=mu(Fix(g)).                                  (RCR2)
```

Moreover, if nonidentity `g,h in Lambda` have disjoint supports, then

```text
(w_g-1)(w_h-1)=0,
1+w_(gh)=w_g+w_h.                                      (RCR3)
```

The four group elements `1,g,h,gh` are distinct.  Hence the induced linear
map from `C[Lambda]` has a nonzero kernel.  More generally, for arbitrary
scalars `z_k in T`, `z_1=1`, the rephased projective family
`v_k=z_k w_k` satisfies the nontrivial dependence

```text
1+z_(gh)^(-1)v_(gh)-z_g^(-1)v_g-z_h^(-1)v_h=0.         (RCR4)
```

It therefore cannot be a regular or projective-regular orthonormal group
basis.  Relation-local holonomy and scalar rephasing leave every
fixed-point coefficient unchanged in absolute value; in the presence of
disjoint supports they also retain this algebraic kernel.

This conclusion is specific to cocycles descending to the principal
relation groupoid.  An arbitrary transformation-group cocycle
`b in Z^1(Lambda,U(A tensor M_n))` need not equal `1` on fixed-point
isotropy, so neither `(RCR2)` nor the support localization behind `(RCR3)`
is asserted for it.

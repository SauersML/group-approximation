---
rg: 2
id: binary-jacobson-finitary-whitehead-shift-lef-proof
kind: route
title: Close the inspected part of the bilateral Whitehead orbit into a long finite cycle
target: binary-jacobson-finitary-whitehead-shift-is-marked-lef
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - lef-implies-operator-mf
---

Use the standard basis `(k,n)`, `1<=k<=5`, `n>=0`, of the Jacobson module.
The Whitehead involution and constant swap act on the chosen two rays by

```text
W(j,n)=(i,n+1),             W(i,n+1)=(j,n),
W(i,0)=(i,0),
```

and `P(i,n)=(j,n)`.  Therefore `a=WP` translates by one step the
bi-infinite chain

```text
...,(j,2),(j,1),(j,0),(i,0),(i,1),(i,2),... .          (JWS2)
```

It fixes the other three coordinate rays.  Conjugation by this permutation
normalizes the finitary general linear group `L`.  No nonzero power of `a`
is finitary, so `L intersect <a>=1`, proving the semidirect normal form in
`(JWS1)`.

Fix a finite subset `C` of `H`, enlarged by every product whose local table
is to be retained.  Write its elements uniquely as

```text
g=lambda_g a^(m_g),                lambda_g in L.
```

Only finitely many basis points occur in the matrix supports of the
`lambda_g`, in the supports produced during the selected products, and in
their translates by the finitely many shift exponents involved.  On the
chain `(JWS2)` they lie in one bounded interval.  Choose a cycle length `N`
larger than twice that interval and larger than twice every inspected shift
exponent.  Embed the interval injectively in `C_N`, let `abar` be cyclic
translation on `C_N`, and keep every inspected point on the three fixed rays
as a separate fixed point.

Copy each retained finitary matrix to the resulting finite-dimensional
`F_2`-space, extending it by the identity.  Call the copy `lambdabar_g` and
set

```text
gbar=lambdabar_g abar^(m_g).
```

No inspected support or exponent wraps around the cycle.  Hence every
retained conjugation and matrix product is identical to the corresponding
one on the infinite chain, so `g->gbar` preserves the complete selected
multiplication table.  If two selected elements have different exponents,
the choice of `N` keeps those exponents distinct; if their exponents agree,
their distinct finitary parts remain distinct on the copied support.  Thus
the partial map is injective.  Its target is a finite general linear group,
which proves LEF.

The head root `z_Q=x_13(E_00)` is a nonidentity transvection in `L`.  Include
its two basis points in the copied interval; every resulting finite model
keeps it nontrivial.  Applying `lef-implies-operator-mf` yields an injective
norm-corona representation of `H`, and precomposition with the Steinberg
projection gives the asserted marked model of `Htilde`.

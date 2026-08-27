---
rg: 2
id: single-finite-type-promotion-no-go-proof
kind: route
title: Pull covariant context PVMs through the finite factor and cancel every multiplicity operator
target: single-finite-type-promotion-forces-a-finite-perfect-strategy
requires: []
---

Take the finite-type promotion datum `(SFT2)--(SFT7)` in the target claim.
Schur covariance writes every context transport as

```text
S_c=s_c tensor U_c.
```

Since the context atoms reduce the range of `s_c`, the operators

```text
tilde p_(c,a)=s_c^*p_(c,a)s_c
```

form a finite-dimensional PVM on the common finite source `V`.  Direct
tensor multiplication gives

```text
S_c^*(p_(c,a) tensor I)S_c
 =tilde p_(c,a) tensor I.
```

Thus every multiplicity isometry cancels.  Pulling back the predicate row
shows that the forbidden atoms have zero projection.  Pulling back the
incidence row gives

```text
B_x=(s_c^*a_(c,x)s_c) tensor I.
```

Because `B_x` is one common source operator, the finite involutions
`s_c^*a_(c,x)s_c` agree for every pair of contexts containing `x`.  The
finite PVMs `tilde p_(c,a)` and these common finite involutions, played on a
maximally entangled state over `V`, therefore win every predicate and
incidence test with probability one.  This contradicts the assumed strict
finite-dimensional game gap.

Nothing in the argument uses finite-dimensional multiplicity spaces.  It
therefore also rules out exact infinite completeness obtained merely by
amplifying one covariantly preserved finite type.

In the tautological hyperoctahedral case, the finite transports are signed
permutations and all pulled-back atoms lie in one coordinate MASA.  Reading
one coordinate gives a global classical assignment satisfying every
context.  The one-global packet

```text
({src} union contexts) times assignment labels times duplicate
```

is precisely this case.  Multiplicity factors are coordinate-independent
and cancel in the D8 row; gauge doubling changes the shares but not their
common logical products.  Neither modification avoids the global-assignment
conclusion.

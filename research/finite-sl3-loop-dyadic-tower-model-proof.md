---
rg: 2
id: finite-sl3-loop-dyadic-tower-model-proof
kind: route
title: Build the all-depth covariant dyadic tower from virtually free finite quotients
target: finite-sl3-loop-packets-are-dyadic-tower-neutral
requires:
  - free-hnn-outlier-has-dyadic-a2-pvm-tower
---

Let `C_0=C intersect hCh^(-1)`.  It has finite index in `C`, so the core

```text
N=intersection_(c in C) cC_0c^(-1)                            (1)
```

also has finite index.  Put `F=C/N` and `X=C/C_0`.  Then `F` acts faithfully
on `X`, and this is precisely the action of `C` on the orbit of `hC` in
`A/C`.  If a finite loop packet meets starting cosets `a_1C,...,a_lC`, use
instead the finite disjoint union

```text
X'=disjoint-union_i C/(C intersect a_iCa_i^(-1)).              (1a)
```

Each stabilizer has finite index because every element of
`SL_3(Z[1/2])` commensurates `SL_3(Z)`.  Intersecting their cores gives one
finite quotient `F` acting on all of `X'`.  The rest of the proof is
unchanged, so we write `X` for either finite `C`-set.

Fix `R>=1`.  For every `x in X`, let `z_x` generate a cyclic group of order
`2^R`, and form

```text
K_R=(*_(x in X) <z_x | z_x^(2^R)=1>) semidirect F,             (2)
f z_x f^(-1)=z_(fx).
```

The free product in `(2)` is virtually free.  Its finite extension `K_R`
is virtually free as well, hence residually finite.

Let `Omega` be a finite collection of nonidentity reduced words whose
canonical lamp moments are to be retained.  Enlarge it by

```text
F\{1},  {z_x^j: x in X, 1<=j<2^R},
{z_x z_y^(-1): x!=y}.                                        (3)
```

Residual finiteness, followed by taking the product of finitely many
separating quotients, gives a finite quotient

```text
r:K_R -> Q                                                    (4)
```

in which every element of `(3)` and every word of `Omega` remains
nontrivial.  Thus every `r(z_x)` has exact order `2^R`, the actor copy `F`
is retained, and distinct lamps remain distinct.

Use the normalized left regular representation `lambda_Q`.  Left
multiplication by an element of exact order `2^R` is a disjoint union of
cycles of length `2^R`; consequently every `2^R`-th root of unity occurs as
an eigenvalue of `lambda_Q(r(z_x))` with equal multiplicity.  Group these
spectral projections into consecutive blocks of size `2^(R-r)` and call the
result `q_(r,j)^x`.  Then, exactly,

```text
sum_j q_(r,j)^x=1,       tr(q_(r,j)^x)=2^(-r),
q_(r,j)^x=q_(r+1,2j)^x+q_(r+1,2j+1)^x,                       (5)
lambda_Q(r(f)) q_(r,j)^x lambda_Q(r(f))^*=q_(r,j)^(fx).       (6)
```

Every word retained by `(4)` has regular trace zero.  Hence any prescribed
finite part of the free product trace table of the lamp algebras is exact.
Every lattice word acts through the genuine quotient `C -> F`, so all
lattice relations and all competing `A_2` loops are exact simultaneously.

Finally choose `R_n -> infinity` and exhaust the nonidentity reduced words
of `(*_(x in X) Z_x) semidirect F` by finite windows `Omega_n`.
Apply `(4)--(6)` at stage `n` and take a tracial matrix ultraproduct.  For a
fixed `r`, the projections in `(5)` are defined for all `n` sufficiently
large and give an exact ultraproduct projection.  The resulting family is
nested through every depth, its distinct lamp algebras are freely
independent, and `F` acts covariantly.

Thus all-depth spectral coherence is compatible with every lattice-only
loop on the finite orbit `X`.  What is absent is an image of the denominator
element `h` transporting this model to the next `C`-orbit.  That is exactly
why this construction invalidates a six-lattice-loop rank argument without
producing an ambient counterexample.

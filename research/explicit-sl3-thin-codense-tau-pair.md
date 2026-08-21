---
rg: 2
id: explicit-sl3-thin-codense-tau-pair
kind: claim
title: Two displayed matrices generate a free profinitely dense property-tau subgroup of SL_3(Z)
distinct_from:
  sln-z-thin-codense-tau-pair: that gives a four-generated existence theorem uniformly for every n at least three; this gives a literal two-generator pair in SL_3(Z), together with a torsion-certified outsider.
---

Put `A = SL_3(Z)` and let `C = <a,b>`, where

```text
a = [ -176379047    1936571625   -17817867 ]
    [ -1941616205  21318171799  -196142682 ]
    [         10          -121           1 ]

b = [ -40193888    -3684209   -44180039 ]
    [ 396162230    36312596   435450841 ]
    [   3829559      351021     4209349 ].
```

Detinko--Flannery--Hulpke, *Experimenting with Zariski dense subgroups*
(arXiv:2303.06236, Section 3.3), construct these matrices inside Humphries's
free subgroup `G_4 < SL_3(Z)` and verify that `C` surjects onto
`SL_3(Z/q)` for `q = 4` and for every prime `q`.  Their profinite-generation
criterion then gives

```text
pi_m(C) = SL_3(Z/m) for every m > 1.                    (ES1)
```

Since `C` is a subgroup of the free group `G_4`, it is free.  It is not
cyclic, because `(ES1)` gives noncyclic finite images; since it is generated
by `a,b`, it is free of rank two.  It has infinite index in `A`: a
finite-index subgroup of the Kazhdan group `SL_3(Z)` has property `(T)`,
whereas a nonabelian free group does not.

Every finite-dimensional unitary representation `rho` of `A` has finite
image and factors through a congruence quotient.  Thus `(ES1)` implies

```text
rho(C) = rho(A),
rho(C)' = rho(A)'.                                      (ES2)
```

Profinite density implies Zariski density.  Bourgain--Varju's arbitrary-
modulus expansion theorem therefore supplies property `(tau)` for `C` on
the complete congruence family through which all finite-dimensional unitary
representations of `A` factor.  Hence `(A,C)` is an explicit co-dense pair
with a uniform finite-dimensional conjugation gap.

Finally set

```text
r = [ 0 -1 0 ]
    [ 1 -1 0 ]
    [ 0  0 1 ].                                         (ES3)
```

Then `r^3 = 1` and `r != 1`.  The free group `C` is torsion-free, so
`r notin C`.  Consequently the HNN extension

```text
G_exp = < SL_3(Z), t | [t,a]=1, [t,b]=1 >              (ES4)
```

is a literal finitely presented group and Britton's lemma gives the explicit
nonidentity marked word

```text
w_exp = [t,r] != 1.                                     (ES5)
```

The exact finite-dimensional endpoint is complete: in every exact
finite-dimensional representation of `A`, a unitary centralizing `a,b`
centralizes all of `A`, and hence centralizes `r`.


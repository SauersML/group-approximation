---
rg: 2
id: product-clock-global-hard-bridge-has-finite-orbit
kind: claim
title: A product clock finitely compiles global hard signs into independent site bridges
distinct_from:
  point-stabilizer-local-hard-share-compiles-bridge-orbit: that assumes the source hard share itself is attached to the Thompson site; this leaves the source word global and advances it with its original clock while advancing only the pulse endpoint with Thompson V.
  product-clock-synchronizes-fanizza-and-e5: that equates a conjugated hard commutator with an overlapping E5 boundary word; this adds an intertwiner between a global hard involution and an independent site involution and derives all prefix commutators from the two Thompson pair-orbits.
  gauge-covariant-hard-shares-admit-site-bridges: that constructs unrelated exact bridge operators after amplification; this compiles the whole infinite family from finitely many prototype generators and proves polynomial relator area.
---

Let `G=<S:R>` be finitely presented with named central involution `J`, let
`U in G`, and let `A^(1),...,A^(m)` be a fixed finite menu of involutive
words.  For each role `r`, take an independent copy `Gamma_r` of the Thompson
site-pulse group whose local source involution is balanced in its marked
`J=-I` model, with
base-site words

```text
a_(r,0), B_(r,0), s_(r,0)
```

and a standard infinite-order element `g_r in V_r` such that
`x_(r,n)=g_r^n x_(r,0)` are distinct and have address length `O(n)`.  Form the
central product of `G` and the finitely many `Gamma_r`, identify their common
central sign, and impose cross commutation between `G` and every pulse factor
and between distinct pulse factors.

For every role adjoin one bridge generator `u_(r,0)`.  It is enough to impose
the finite prototype relations

```text
a_(r,0)u_(r,0)=u_(r,0)A^(r),                          (PGB1)
[u_(r,0),h_(r,j)]=1                                   (PGB2)
[u_(r,0),B_(r,y)]=1                                   (PGB3)
[u_(r,0),q]=1.                                        (PGB4)
```

Here the `h_(r,j)` generate the point stabilizer of `x_(r,0)`, `y` is one
fixed site different from `x_(r,0)`, and `(PGB4)` ranges over finite
generating sets of the pulse factors with role different from `r`.  Put

```text
T_r=Ug_r,
A_(r,n)=U^n A^(r) U^-n,
u_(r,n)=T_r^n u_(r,0) T_r^-n.                         (PGB5)
```

Then, with `a_(r,n),B_(r,n),s_(r,n)` denoting the pulse words at
`x_(r,n)`, the finite presentation implies

```text
a_(r,n)u_(r,n)=u_(r,n)A_(r,n),                        (PGB6)
[u_(r,n),B_(q,k)]=1              if (r,n)!=(q,k).      (PGB7)
```

For the fixed menu, the words and van Kampen derivations in `(PGB6)--(PGB7)`
have size polynomial in `n+k`.  Thus any linear ordering of the pairs `(r,n)`
gives the prefix-preserving bridge family required by the Thompson first-hit
reservoir with a dimension-independent polynomial normalized-HS modulus.

Exact completeness requires no localization of the original logical tuple.
If an exact marked representation makes every `A^(r)` spectrally balanced,
amplify it and use the independent pulse-site tensor model.  On the original
factor tensored with the `r`th base-site factor, choose `u_(r,0)` to match the
spectral subspaces of `A^(r)` and `a_(r,0)`.  The point stabilizer fixes that
site coordinate, and every other pulse factor acts elsewhere, so
`(PGB1)--(PGB4)` hold simultaneously.  In particular the global BCS words
are never copied into commuting lamp sites.

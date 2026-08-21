---
rg: 2
id: heisenberg-chamber-clocks-escape-until-root-gluing
kind: claim
title: Heisenberg chamber clocks keep interior overlap until Weyl chambers share the same root reservoir
distinct_from:
  periodic-dyadic-root-clocks-keep-weyl-overlap: that uses six independent abelian root clocks and fails the first adjacent-root commutator; this imposes exact nonabelian Heisenberg multiplication in every Weyl chamber and identifies cross-chamber root equality as the next missing input.
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that treats a corrector already in one full coefficient commutant; this proves that gluing the chambers into one finite Chevalley reservoir creates exactly such a common corrector and then evaluates the triangle.
  commuting-conjugate-involution-transfer-for-sl3-pair: that has globally named arithmetic root groups shared by all chambers; this isolates the quantitative shared-root synchronization that arbitrary matrix microstates must retain.
---

Let `W=S_3` and let `Lambda=(Z/4)^2` be the coweight module from
`periodic-dyadic-root-clocks-keep-weyl-overlap`.  For every `w in W`, take a
copy `N_w` of the finite Heisenberg group over `F_5`, written

```text
N_w=<x_w(s),y_w(t),z_w(r) :
      [x_w(s),y_w(t)]=z_w(st), z_w central>.             (HCC1)
```

Put

```text
N = product_(w in W) N_w.                                (HCC2)
```

The coweight `mu` acts on the `w`-factor with the three root weights

```text
x_w(t) |-> x_w(2^(mu_(w1)-mu_(w2)) t),
y_w(t) |-> y_w(2^(mu_(w2)-mu_(w3)) t),
z_w(t) |-> z_w(2^(mu_(w1)-mu_(w3)) t).                  (HCC3)
```

The third exponent is the sum of the first two, so `(HCC3)` preserves the
Heisenberg commutator exactly.  The Weyl group permutes the factors by left
translation.  The weight formula is equivariant, hence

```text
L = N rtimes (Lambda rtimes W)                           (HCC4)
```

is a finite group.  Let

```text
C_0=N rtimes W < L.
```

For the coweight `mu=(1,0,-1)`, the element `h=(0,mu,1)` satisfies all six
dyadic scaling equations on every chamber factor.  Its two simple-Weyl
conjugates `h',h''` satisfy

```text
h(h'')^-1=h'                                             (HCC5)
```

exactly.  Conjugating `(HCC1)` by the Weyl group supplies the adjacent-root
Steinberg multiplication packet in every chamber, with all transports and
depth shifts exact.

## Exact lamp countermodel

Let `X=L/C_0` and form

```text
B=(direct_sum_(x in X) C_2) rtimes L.                    (HCC6)
```

The group `C_0` fixes the base coset.  Therefore its base lamp `c_0`
commutes with all Heisenberg root packets and with the Weyl group.  The
`h`-translated lamp is a distinct commuting coordinate.  In the left regular
representation of the finite group `B`, their half projections satisfy

```text
tr(P)=tr(hPh^-1)=1/2,
[P,hPh^-1]=0,
tr(P hPh^-1)=1/4.                                       (HCC7)
```

Thus one adjacent-root commutator, even imposed equivariantly and exactly in
every Weyl chamber together with all six dyadic shifts and the rank-two
triangle, does not force a scalar payment.

## The escape is duplicated root identity

The root represented by `z_1` in the identity chamber also occurs as a
simple-root coordinate `x_w` or `y_w` in a neighboring chamber.  In `(HCC2)`
these are independent elements in different direct factors.  The actual
Steinberg system identifies them as one globally named root subgroup.
That equality is the first relation the model omits.

This is not cosmetic.  If all chamber occurrences are glued into the common
finite Chevalley reservoir

```text
F=SL_3(F_5),                                             (HCC8)
```

then the dyadic coweight automorphism is inner.  With

```text
d=diag(2,1,3) in F,
```

let `rho:F->U(D)` be any exact unitary representation and let `V` implement
the same root scaling:

```text
V rho(f) V^*=rho(d f d^-1).                              (HCC9)
```

Then

```text
Z=rho(d)^*V in rho(F)'.                                  (HCC10)
```

Because the Weyl elements lie in `F`, all three Weyl-conjugate lifts carry
the same `Z`.  The internal diagonal slots `d,d',d''` satisfy
`d(d'')^-1=d'`; substituting `rho(d)Z,rho(d')Z,rho(d'')Z` into `(HCC5)`
forces `Z=1`.  Consequently

```text
V=rho(d),
P in rho(F)'  ==>  V P V^*=P.                            (HCC11)
```

So the common-reservoir exact sector has overlap `1/2`, not `1/4`, in every
matrix dimension and with arbitrary representation multiplicity.

## Exact remaining normalized-HS interface

The finite calculations prove the following sharp dichotomy:

```text
local Heisenberg multiplication in separately named chambers
    admits an exact a=1/4 model;
one common Chevalley root reservoir
    forces a=1/2 exactly.                                 (HCC12)
```

For a fixed finite `F`, finite-group Hilbert--Schmidt exactification makes
the second implication robust with a dimension-independent modulus.  That
does not solve the arithmetic problem, because canonical microstates of
`SL_3(Z)` do not satisfy a fixed `F_5` quotient relation and need not decode
all chamber occurrences into one finite quotient block.

The next and now minimal gate is therefore a **shared-root gluing estimate**:
the approximate operators decoded for one global arithmetic root through
two adjacent Heisenberg/Weyl chambers must agree on a positive amount of the
same four-atom multiplicity reservoir, with error controlled independently
of the ambient matrix dimension and of the periodic clock length.  Once that
gluing is available, `(HCC10)--(HCC11)` is the finite scalar endgame.

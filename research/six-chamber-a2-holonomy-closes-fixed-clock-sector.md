---
rg: 2
id: six-chamber-a2-holonomy-closes-fixed-clock-sector
kind: claim
title: The six-chamber A2 holonomy closes every fixed period-five root-clock sector
distinct_from:
  adjacent-a2-chambers-share-only-commuting-wall: that proves one wall admits an exact central/simple multiplicity rotation; this proves the rotation cannot be continued consistently around the minimal closed chamber gallery.
  periodic-dyadic-root-clocks-keep-weyl-overlap: that keeps the six roots in independent abelian reservoirs; this adds all six Weyl-conjugate Heisenberg relations, completing the fixed root packet to SL3(F5).
  odd-congruence-lambda-exact-sector-collapses: that closes arbitrary exact congruence representations by an inner slot and the coweight triangle; this identifies the minimal finite root-gallery presentation producing that slot and its explicit holonomy word.
---

Write a chamber of the `A_2` Coxeter complex as an ordered triple `ijk` and
associate the Heisenberg packet

```text
H_(ijk)=<x_(ij),x_(jk),x_(ik) :
          [x_(ij)(s),x_(jk)(t)]=x_(ik)(st)>.             (SCH1)
```

Alternating the two simple reflections gives the minimal closed gallery

```text
123 -> 213 -> 231 -> 321 -> 312 -> 132 -> 123.           (SCH2)
```

The six packet relations are therefore

```text
[x_12(s),x_23(t)]=x_13(st),
[x_21(s),x_13(t)]=x_23(st),
[x_23(s),x_31(t)]=x_21(st),
[x_32(s),x_21(t)]=x_31(st),
[x_31(s),x_12(t)]=x_32(st),
[x_13(s),x_32(t)]=x_12(st).                              (SCH3)
```

Adjacent packets share the two commuting wall roots listed in
`adjacent-a2-chambers-share-only-commuting-wall`.  No shorter closed gallery
exists in the chamber graph: `(s_1s_2)^3=1` is the first Coxeter relation.

## The explicit holonomy word

Over `F_5`, put

```text
n_12=x_12(1)x_21(-1)x_12(1),
n_23=x_23(1)x_32(-1)x_23(1).                             (SCH4)
```

These are the signed simple-Weyl matrices.  The gallery holonomy is

```text
Omega=(n_12 n_23)^3.                                    (SCH5)
```

Directly on the standard basis, `n_12n_23` is a signed three-cycle and its
cube is the identity.  Equivalently, the additive root relations, the
commuting-wall relations, and `(SCH3)` are the Steinberg relations for
`St_3(F_5)`.  The kernel of

```text
St_3(F_5) -> SL_3(F_5)
```

is `K_2(F_5)=0`; hence

```text
Omega=1                                                  (SCH6)
```

already in the universal packet.  There is no residual scalar or central
cocycle around the hexagon.

This is precisely why the two-wall swap from
`adjacent-a2-chambers-share-only-commuting-wall` cannot be assigned
consistently to all six edges: its product would be a nontrivial multiplicity
holonomy, while the literal root words force `(SCH6)`.

## Exact fixed-clock collapse

Let `F=SL_3(F_5)` and

```text
d=diag(2,1,3) in F.                                     (SCH7)
```

The six dyadic root-clock equations are conjugation by `d`.  Let
`rho:F->U(D)` be any exact finite-dimensional representation and let `V`
implement those equations.  Then

```text
Z=rho(d)^*V in rho(F)'.                                  (SCH8)
```

The Weyl words `(SCH4)` belong to the same literal packet, so their conjugates
of `V` carry the same corrector `Z`.  If `d',d''` are the two simple-Weyl
conjugates of `d`, then

```text
d(d'')^-1=d'.                                           (SCH9)
```

Substituting `rho(d)Z,rho(d')Z,rho(d'')Z` in the lifted version of `(SCH9)`
forces `Z=1`.  Therefore

```text
V=rho(d),
P in rho(F)'  ==>  VPV^*=P.                             (SCH10)
```

In particular a balanced commuting-conjugate lamp has overlap `1/2`; the
periodic `1/4` escape is impossible once all six chambers use one literal
root reservoir.

## Dimension-independent robust form for the fixed packet

The conclusion is uniformly robust in matrix dimension for this **fixed**
finite packet.  More precisely, there is a modulus `omega_5(epsilon)->0`
depending only on the multiplication table of `F` such that the following
holds after the standard flexible finite-group exactification.  If

1. the six chamber root tables have total normalized-HS defect at most
   `epsilon` and exactify to one representation `rho` of `F`;
2. `V` implements the six dyadic conjugacies and the coweight triangle with
   defect at most `epsilon`; and
3. a projection `P` commutes with the root generators with defect at most
   `epsilon`,

then

```text
||VPV^*-P||_2 <= omega_5(epsilon).                       (SCH11)
```

Indeed finite-group stability gives `rho`; averaging puts
`rho(d)^*V` within `O_F(epsilon)` of the full coefficient commutant; the two
fixed Weyl words and the triangle force that averaged corrector within
`O_F(epsilon)` of `1`; and word telescoping transfers the commutator bounds
from the roots to `rho(d)`.  Every constant depends on this fixed finite root
table, never on the ambient matrix dimension or spectator multiplicity.

Equivalently, if `Q=VPV^*` and `tr(P)=tr(Q)=1/2`, then `(SCH11)` gives

```text
|tr(PQ)-1/2| <= omega_5(epsilon).                        (SCH12)
```

## Scope and the remaining arithmetic gate

This theorem closes every fixed common period-five clock sector and, with the
same proof, every fixed odd finite Chevalley packet.  It does not yet supply a
uniform modulus over periods tending to infinity, nor does it prove that
independently rounded chamber packets in an arbitrary arithmetic microstate
exactify to one common finite quotient packet.  The wall-rotation
countermodel shows why pairwise overlap cannot provide that step.

The remaining `G_cc` interface is therefore a multiscale version of the
hexagon: charge nontrivial six-edge multiplicity holonomy uniformly when the
root clock periods and congruence depths vary.  Once that charge aligns the
directionwise packets on one carrier, the Weyl-orbit kernel joins generate
the common shallower principal layer and the fixed `Lambda_0` property-T gap
can drive the conductor recurrence.  At fixed period the explicit holonomy
`(SCH5)` already supplies the complete finite-dimensional endgame.

---
rg: 2
id: passive-core-quotient-has-relative-rational-h2
kind: claim
title: Adding the two passive cubics carries a nonzero relative rational H2 class
distinct_from:
  sl2-half-rational-h2-refutes-torsion-normalized-op-basin: that uses absolute rational H2 to refute the exact-torsion global basin; this computes the mapping-cone class for the opposite exact-BS-core normalization.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for a positive mixed-norm splitting throughout the passive region; this proves that such a continuation is not a formal consequence of the exact-zero derivative geometry.
  authenticated-core-union-basin-is-relative-liftability: that identifies the normalized-HS basin with relative ultraproduct liftability; this computes the rational topological class carried by the quotient which adds the two cubic rows.
---

**ESTABLISHED; TOPOLOGICAL FIREWALL, NOT YET A COUNTERSEQUENCE.**  Let

```text
K=<R,S,X |
     RSR^(-1)=S^4, X^2=1, XRX=R^(-1)>                 (PRH1)
```

be the exact passive-core group, before imposing the two cubic Iwahori
rows, and let

```text
q:K -> G=PSL_2(Z[1/2])                                (PRH2)
```

be the quotient obtained by imposing those rows.  Then

```text
H_1(K,Q)=H_2(K,Q)=0,                                  (PRH3)
H_2(Cone(Bq),Q)=Q.                                    (PRH4)
```

Here `(PRH4)` is relative homology for the map `Bq:BK->BG`; injectivity of
`q` is neither asserted nor required.

The identification of `q` is exact.  By
`iwahori-square-root-presentation-is-bs14-plus-one-involution`, the full
group has presentation

```text
<X,R,S | X^2, (XR)^2, (XS^2)^3,
           RSR^(-1)=S^4, (XRS)^3>.                    (PRH5)
```

Since `X^2=1`, the row `(XR)^2=1` is equivalent to
`XRX=R^(-1)`.  Deleting precisely the two cubic rows in `(PRH5)` therefore
gives `(PRH1)` and proves that their attachment induces `(PRH2)`.

## Homology of the exact passive core

The presentation `(PRH1)` is the amalgam

```text
K=BS(1,4) *_(<R>) D_infinity,                         (PRH6)
```

where

```text
BS(1,4)=<R,S | RSR^(-1)=S^4>,
D_infinity=<R,X | X^2=1, XRX=R^(-1)>.
```

The Baumslag--Solitar presentation complex is aspherical.  In its rational
cellular chain complex the two-cell boundary has augmentation coordinates
`(0,1-4)`, so

```text
H_2(BS(1,4),Q)=0,       H_1(BS(1,4),Q)=Q<R>.          (PRH7)
```

The infinite dihedral group is virtually cyclic with finite
abelianization, hence

```text
H_2(D_infinity,Q)=H_1(D_infinity,Q)=0.                (PRH8)
```

The relevant part of the Mayer--Vietoris sequence for `(PRH6)` is

```text
0 -> H_2(K,Q) -> Q --(id,0)--> Q (+) 0 -> H_1(K,Q)
  -> Q --(1,-1)--> Q (+) Q.                           (PRH9)
```

The first displayed map out of `Q` is an isomorphism onto the only nonzero
summand, while the final `H_0` map is injective.  Exactness proves `(PRH3)`.

## Homology after attaching the cubics

Use the standard one-edge Bruhat--Tits amalgam

```text
G=PSL_2(Z) *_(Gamma_0(2)) PSL_2(Z),                   (PRH10)
PSL_2(Z)=C_2*C_3,       Gamma_0(2)=C_2*Z.
```

Both vertex groups and the edge group have zero rational `H_2`; the vertex
groups have zero rational `H_1`, while
`H_1(Gamma_0(2),Q)=Q`.  Mayer--Vietoris now reads

```text
0 -> H_2(G,Q) -> Q -> 0 -> H_1(G,Q)
  -> Q --(1,-1)--> Q (+) Q.                          (PRH11)
```

Consequently

```text
H_2(G,Q)=Q,             H_1(G,Q)=0.                   (PRH12)
```

The mapping-cone exact sequence contains

```text
H_2(K,Q) -> H_2(G,Q) -> H_2(Cone(Bq),Q) -> H_1(K,Q). (PRH13)
```

Using `(PRH3)` and `(PRH12)` proves `(PRH4)`.

## Consequence and exact limit

Uniform cb/right-inverse bounds at all exact endpoints plus the fixed-word
Hessian bound give a uniform Newton tube *around* the zero locus.  They do
not rule out operator-small tuples in a different asymptotic component.
Equation `(PRH4)` shows that the two cubic attaching rows carry a genuine
rational relative two-class after the exact BS and inversion rows have
already been imposed.  Its dimension is one: the calculation detects one
nonzero linear combination of the two attachment classes, not two
independent classes.  In particular, the local infinitesimal estimates do
not themselves erase the quotient's relative topology.

This claim does **not** prove that the desired passive splitting is false.
Turning `(PRH4)` into a countersequence exact on `K` requires a relative
operator-norm quasirepresentation or almost-flat-bundle theorem with a
specified exact trivialization over `K`; the absolute Dadarlat theorem used
for `G` does not state that refinement.  Conversely, a positive passive
theorem would be a substantive relative lifting result which defeats this
class, not a formal consequence of the homology calculation.  No
countersequence or normalized Hilbert--Schmidt obstruction is asserted.

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

## Proof

The presentation `(PRH1)` is the amalgam

```text
K=BS(1,4) *_(<R>) D_infinity,                         (PRH5)
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
H_2(BS(1,4),Q)=0,       H_1(BS(1,4),Q)=Q<R>.          (PRH6)
```

The infinite dihedral group is virtually cyclic with finite
abelianization, hence

```text
H_2(D_infinity,Q)=H_1(D_infinity,Q)=0.                (PRH7)
```

In the Mayer--Vietoris sequence for `(PRH5)`, the map

```text
H_1(<R>,Q) ->
H_1(BS(1,4),Q) (+) H_1(D_infinity,Q)                  (PRH8)
```

is `x |-> (x,0)` and therefore an isomorphism onto the only nonzero
summand.  Equations `(PRH6)--(PRH8)` prove `(PRH3)`.

On the other hand,
`sl2-half-rational-h2-refutes-torsion-normalized-op-basin` computes

```text
H_2(G,Q)=Q,             H_1(G,Q)=0.                   (PRH9)
```

The mapping-cone exact sequence contains

```text
H_2(K,Q) -> H_2(G,Q) -> H_2(Cone(Bq),Q) -> H_1(K,Q).
```

Using `(PRH3)` and `(PRH9)` proves `(PRH4)`.

## Consequence and exact limit

Uniform cb/right-inverse bounds at all exact endpoints plus the fixed-word
Hessian bound give a uniform Newton tube *around* the zero locus.  They do
not rule out operator-small tuples in a different asymptotic component.
Equation `(PRH4)` shows that the two cubic attaching rows carry a genuine
rational relative two-class after the exact BS and inversion rows have
already been imposed.  Thus no argument based only on contractibility of
the exact-core presentation, separate spectral rounding of the cubics, or
the infinitesimal inverse at their common zeros can make the off-zero basin
automatic.

This claim does **not** prove that the desired passive splitting is false.
Turning `(PRH4)` into a countersequence exact on `K` requires a relative
operator-norm quasirepresentation or almost-flat-bundle theorem with a
specified exact trivialization over `K`; the absolute Dadarlat theorem used
for `G` does not state that refinement.  Conversely, a positive passive
theorem would be a substantive relative lifting result which defeats this
class, not a formal Newton corollary of the now-controlled exact Jacobian.

---
rg: 2
id: atlas-ck-dual-pair-cell-proof
kind: route
title: Intersect the first D8 fibers with the four CK dual-pair triangles
target: atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity
requires:
  - atlas-root-triangle-is-heisenberg-character-fibers
  - atlas-steinberg-rank-five-translation
  - atlas-steinberg-spare-index-independence
---

The Steinberg convention is

```text
[x_ij(a),x_jk(b)] = x_ik(ab).                          (CKR1)
```

Apply `(CKR1)` at `(i,j,k)=(1,5,2)` to the four ordered coefficient pairs
`(E,e)`, `(F,f)`, `(E,f)`, `(F,e)`.  The Leavitt relations

```text
Ee=Ff=1,       Ef=Fe=0
```

give exactly `(CKP3)`.  Same-source and same-target Steinberg commutation
give `[X_E,X_F]=[Y_e,Y_f]=1`; the orthogonal-root rows centralize `Z`; the
emitted involutivity rows make every displayed root an involution.

On a reducing sector where `Z=-1`, the commutator form on

```text
span_F2{X_E,X_F,Y_e,Y_f}
```

is the standard nondegenerate symplectic form: its only nonzero pairings are
`<X_E,Y_e>=<X_F,Y_f>=1`.  Hence the generated finite group is the two-pair
extraspecial group, and finite Stone--von Neumann theory gives one central
character `Z=-1` irreducible, of dimension four.  Since every `Q_chi` from
the first-root decomposition commutes with these four side-root words, its
negative sector is a multiple of that irreducible.  This proves
`(CKP4)--(CKP5)`.

In the Schrodinger realization one may take

```text
X_E = sigma_x tensor I,       Y_e = sigma_z tensor I,
X_F = I tensor sigma_x,       Y_f = I tensor sigma_z.  (CKR2)
```

The four joint Fourier atoms of `(X_E,X_F)` have rank one on the `C^4`
factor.  Schur's lemma puts every packet-commuting projection in
`I_4 tensor B(M_chi)`, proving `(CKP6)`.

For the partition refinement, spare-index independence defines the roots
for the monomials `p=eE` and `q=fF` independently of the chosen commutator
chain.  Root additivity and `eE+fF=1` give `C_p C_q=Z`.  These are same-root
involutions, hence commute.  The Steinberg (St2) pattern also makes both
commute with the side-root actors in `(CKP1)`.  Therefore on `Z=-1`,
`C_q=-C_p`, and the two negative spectral projections in `(CKP9)` are
orthogonal complements inside the extraspecial commutant.  Schur's lemma
then gives `(CKP10)`.

Finally, fix arbitrary finite-dimensional spaces `M_p,M_q`, use `(CKR2)`
on `C^4`, put `M=M_p direct-sum M_q`, and define

```text
C_p = I_4 tensor (-I_(M_p) direct-sum I_(M_q)),
C_q = -C_p,        Z=-I_(C^4 tensor M).                (CKR3)
```

Equations `(CKP1)--(CKP3)` and `(CKP8)` hold exactly for every choice of
`dim M_p,dim M_q`.  This is a countermodel only to the stated local CK cell,
not to the full 4,624-word Atlas packet.  Its precise conclusion is that the
next useful full-packet word must leave this local commutant and compare the
two branches; no further argument internal to this dual-pair/partition cell
can do so.

---
rg: 2
id: stw99-xciv-commuting-column-diagonal-proof
kind: route
title: Diagonalize one local block into commuting norm-central columns and absorb its infinite tensor power
target: stw99-xciv-single-prime-block-centrality-is-exact
requires:
  - stw99-xciv-separable-zstability-iff-local-norm-central-z
artifacts:
  - research/artifacts/stw99-xciv-single-block-diagonal-audit-2026-08-30.md
---

Assume first that every norm-separable subset of `B` has a separable
`Z`-stable hull.  Given `F` and `epsilon`, choose such a hull `C` containing
`F`.  A central sequence embedding `Z->C_infinity intersect C'`, together
with a fixed unital embedding `D=I_(2,3)->Z`, gives a unital copy of `D`
whose chosen lift is as norm-central on `F` and `H` as required.  Equivalently
one may invoke `stw99-xciv-separable-zstability-iff-local-norm-central-z` and
compose its local `Z` copy with `D->Z`.  This proves `(1)=>(2)`.

Conversely assume `(2)` and fix a norm-separable seed `S subset B`.  Start
with `C_0=C*(S,1)`.  We recursively build separable unital algebras

```text
C_0 subset C_1 subset ... subset B
```

and, at stage `n`, unital homomorphisms

```text
psi_(n,j):D->B,                    1<=j<=n.             (3)
```

Choose dense sequences in the unit balls of `C_0,C_1,...` and in `D`.  At
stage `n`, form a finite test containing the first `n` scheduled elements of
the earlier `C_m`.  Choose `psi_(n,1)` by `(2)`.  Having chosen the first
`j-1` maps in `(3)`, enlarge the test by the images under those maps of the
first `n` scheduled elements of `D`, and choose `psi_(n,j)` by `(2)`.
Take the commutator tolerance sufficiently small that polynomial
approximation from the fixed generating set `H` gives

```text
||[psi_(n,j)(d_p),psi_(n,l)(d_q)]||<1/n
```

for `j!=l` and the first `n` scheduled `d_p,d_q`, and gives the analogous
`1/n` bounds against the scheduled elements of the earlier `C_m`.  Such a
tolerance exists because `H` generates `D`; all sets involved at stage `n`
are finite.  Put

```text
C_n=C*(C_(n-1),psi_(n,1)(D),...,psi_(n,n)(D)),
C=closure(union_n C_n).
```

For fixed `j`, the column `(psi_(n,j))_(n>=j)` defines a unital homomorphism

```text
Psi_j:D->C_infinity intersect C'.                       (4)
```

(Fill the finitely many coordinates `n<j` with any one of the already chosen
unital maps.)  The diagonal tests give norm centrality in `(4)`.  They also
show that the ranges of `Psi_j` and `Psi_l` commute for `j!=l`.  Since `D`
is nuclear, multiplication of these commuting representations is continuous
for the minimal tensor product.  The compatible finite products therefore
give a unital homomorphism

```text
Psi:D^(tensor infinity)->C_infinity intersect C'.       (5)
```

Dadarlat--Toms, *Z-stability and infinite tensor powers of C*-algebras*,
Adv. Math. 220 (2009), Theorem 1.1 (arXiv:0707.4050), says that `A^(tensor
infinity)` is `Z`-stable whenever it contains unitally a subhomogeneous
algebra without characters.  Apply this with `A=D`: its infinite tensor
power contains the first tensor factor `D`, which is subhomogeneous and has
no one-dimensional representations.  Hence `D^(tensor infinity)` is
`Z`-stable and in particular admits a unital homomorphism

```text
eta:Z->D^(tensor infinity).
```

Composing `eta` with `(5)` gives a unital central sequence embedding
`Z->C_infinity intersect C'`.  The strongly self-absorbing absorption
criterion yields `C~=C tensor Z`.  Thus `C` is the required separable
`Z`-stable hull of `S`.

Finally `(2)` in the claim is the literal logical negation of the local
condition because `H` is fixed and finite.  No compactness or attainment is
used.

Every limit above is in operator norm.  If the commutators converged only in
tracial `2`-norm, the columns would commute only in the tracial sequence
quotient; `(4)` and `(5)` would not land in `C_infinity intersect C'`, and
the absorption criterion would not apply.

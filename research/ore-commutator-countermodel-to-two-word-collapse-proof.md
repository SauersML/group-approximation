---
rg: 2
id: ore-commutator-countermodel-to-two-word-collapse-proof
kind: proof
title: Use Ore surjectivity in PSL28 over F2 to build an exact finite countermodel
target: two-jacobson-commutators-plus-perfectness-have-finite-model
requires:
  - scalar-rephased-toeplitz-sections-still-collapse-head
---

Because `F_2^times={1}`, the groups

```text
GL_28(F_2)=SL_28(F_2)=PSL_28(F_2)
```

coincide. This is a finite nonabelian simple group.

The Ore conjecture, proved by
Liebeck--O'Brien--Shalev--Tiep, says that every element of every finite
nonabelian simple group is a single commutator. Apply it to the nonidentity
transvection

```text
C=x_13(1).
```

There are `U,V in K` with

```text
[U,V]=C.                                                 (OCC1)
```

For the second pair one may take `U'=V'=1). If nonidentity actors are
desired, take `U'=V'=A` for any fixed nonidentity `A in K); an element
commutes with itself. In either case

```text
[U',V']=1.                                              (OCC2)
```

Equations `(OCC1)--(OCC2)` prove `(TCF1)--(TCF2)`.

Let `lambda` be the left regular representation of `K). It is an
exact representation of the entire finite scalar group, and the first
word in `(TCF2)` is literally the identity. Since `C` is nonidentity,

```text
tau(lambda(C))=0,
||lambda(C)-I||_2^2=2.                                  (OCC3)
```

This proves `(TCF3)`.

The primary source is Liebeck, O'Brien, Shalev and Tiep, *The Ore
conjecture*, J. Eur. Math. Soc. 12 (2010), 939--1008,
doi:10.4171/JEMS/220, Theorem 1.

The countermodel deliberately does not satisfy the full Jacobson root
chart: it does not assert that the four actors arise from one pair of
ring letters or have the required conjugation relations with every scalar
root. That is exactly its purpose. Any proof using only the two displayed
commutators and perfectness would apply to this finite model and contradict
`(OCC3)). Therefore those inputs cannot by themselves yield the desired
head modulus; a global proof must consume the omitted root-type relations.

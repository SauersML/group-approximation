---
rg: 2
id: literal-blr-weyl-metapixel-collapse-proof
kind: route
title: Complete the BLR and Weyl prototypes to the extraspecial multiplication table
target: literal-blr-weyl-metapixel-is-nonhyperlinear
requires:
  - uniform-bounded-area-clifford-tables-force-mark-collapse
---

Write `Area` for van Kampen area over `R`.  We use only

```text
Area(uv) <= Area(u)+Area(v),
Area(gug^-1)=Area(u),
Area(u^-1)=Area(u).                                           (LBW3)
```

Fix `N` and suppress its subscript.  The BLR relation at `(0,0)` freely
reduces to `x(0)`, so `Area(x(0))<=L`; similarly
`Area(z(0))<=L`.  The relation at `(a,a)`, followed by the zero relation,
gives

```text
Area(x(a)^2)<=2L,       Area(z(phi)^2)<=2L.                   (LBW4)
```

There is also a universal bounded-area derivation of the centrality needed
inside this packet.  For nonzero `a`, choose `phi` with `phi(a)=1`.  The four
relations

```text
X^2=Z^2=J^2=1,             [X,Z]=J                         (LBW5)
```

present the one-qubit dihedral Pauli group and imply `[J,X]=[J,Z]=1`.
Choose once and for all van Kampen diagrams for those two consequences over
the fixed four-relator presentation `(LBW5)`.  Substitute
`X=x(a), Z=z(phi), J=j`.  By `(LBW2)` and `(LBW4)`, every cell of those fixed
diagrams costs at most `2L`.  Hence

```text
Area([j,x(a)])<=C_0 L,
Area([j,z(phi)])<=C_0 L                                    (LBW6)
```

for one numerical constant `C_0`, independent of `N,a,phi`.  Zero labels use
the already bounded zero-word diagrams.  For a nonzero covector, choose a
vector on which it is one and apply the same argument.  Notice that no
centrality along the spelling length of `x(a)` or `z(phi)` is used; `(LBW6)`
is a fixed one-qubit diagram.

Let `E_N` be the extraspecial Pauli group on `F_2^N` and its dual, written as
triples `(c,a,phi)`, with multiplication cocycle `phi(b)`.  Choose word
representatives

```text
sigma_N(c,a,phi)=j^c x(a) z(phi).                            (LBW7)
```

For two such representatives, move the second central bit to the front using
at most two diagrams `(LBW6)`, move `z(phi)` past `x(b)` using one twisted
relation in `(LBW2)`, and apply one X-BLR and one Z-BLR relation.  Moving the
new phase to the front uses only another bounded number of `(LBW6)` diagrams.
Therefore a constant `C`, depending only on the fixed diagrams `(LBW5)` and
not on `N`, satisfies

```text
Area(sigma_N(g)sigma_N(h)sigma_N(gh)^-1)<=C L                (LBW8)
```

for every `N` and every `g,h in E_N`.  Also `sigma_N(J)=j`.

Thus `(LBW7)--(LBW8)` are exactly the uniformly bounded complete Clifford
tables in `uniform-bounded-area-clifford-tables-force-mark-collapse`, with
bound `A=CL`.  That theorem says that any finite-dimensional tuple of
presentation defect `epsilon` obeys

```text
||j(U)-I||_2 <= 42 C L epsilon.                              (LBW9)
```

If `Gamma` were hyperlinear and `j!=1`, microstates could make `epsilon` tend
to zero while keeping `j` a fixed distance from the identity, contradicting
`(LBW9)`.  Hence `Gamma` is nonhyperlinear.

For completeness, the asserted finite orbit count is elementary.  Ordered
BLR input pairs have the five types

```text
(0,0), (a,0), (0,b), (a,a), (a,b independent),               (LBW10)
```

and vector--covector pairs have the five types determined by which entries
are zero and, when both are nonzero, whether `phi(a)` is zero or one.  Hence
linear or affine addressing removes the incidence-count problem.  It does
not remove `(LBW8)`: contextual conjugates must first be identified with the
single global words `(LBW1)`, and any hyperlinear exact model forces the areas
of those identifications to be unbounded.

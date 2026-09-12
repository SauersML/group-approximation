---
rg: 2
id: monomial-game-pair-compatibility-is-projective-color-rigid
kind: claim
title: Monomial-game pair compatibility factors through projective phase colors
distinct_from:
  harris-circulant-one-matrix-compiler-forces-affine-support: that specializes a direct Harris translation completion and derives affine-coset support; this classifies the projected compatibility relation of every one-matrix monomial game before any Harris specialization.
  bisynchronous-to-monomial-game-algebra-compiler: that permits auxiliary vertices and a trace-preserving full-corner encoding; this rules out only a direct encoding by one or finitely many common-phase entry-color tests.
---

Fix `s`, matrices `A,B in M_n(C)`, and the associated `s`-monomial
isomorphism game.  Color an off-diagonal pair by

```text
col_A(i,j)=0                    if A_(ij)=0,
col_A(i,j)=mu_s A_(ij)         otherwise.             (MCR1)
```

There exist phases `a,b in mu_s` satisfying the monomial winning equation

```text
a A_(ij)=b B_(kl)                                      (MCR2)
```

if and only if `col_A(i,j)=col_B(k,l)`.  Consequently, after forgetting the
phase outputs, the compatible target-pair sets for two source pairs are
either identical or disjoint: the projected compatibility graph is a
disjoint union of complete bipartite projective-color classes.

If one common monomial matrix is constrained by finitely many equations
`uA^(q)=B^(q)u`, the same conclusion holds with entry-color vectors in
`C^r`, modulo common multiplication by `mu_s`.  Hence finitely many direct
intertwiner matrices still give a projective color partition, not an
arbitrary bisynchronous pair relation.  Auxiliary incidence vertices or a
genuine full-corner gadget remain possible.


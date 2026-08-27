---
rg: 2
id: binary-leavitt-finite-actor-minimal-atom-proof
kind: route
title: Use the finite dual permutation model and the infinite Leavitt parabolic orbit
target: binary-leavitt-finite-actor-minimal-atom-dichotomy
requires:
  - surviving-leavitt-corona-character-has-infinite-parabolic-orbit
---

For the finite-packet half, let `A^=Hom(A,{+1,-1})`.  The formulas `(FAM1)`
give unitary matrices because `M_a` is diagonal and `P_k` permutes the
standard basis.  For `chi in A^`, direct evaluation gives

```text
P_k M_a P_k^(-1) delta_chi
 =chi(k a)delta_chi
 =M_(k a)delta_chi,
```

which is `(FAM2)`.  Character duality for the finite vector space `A`
provides `chi(a_0)=-1`.  Its joint atom is the line `C delta_chi`.
All joint atoms are lines, conjugation carries the `chi` line to the
`k chi` line, and hence every member of the orbit has the same least
possible nonzero rank.

After tensoring by a representation `sigma:K->U(V)`, use
`M_a tensor 1` and `P_k tensor sigma(k)`.  The same computation proves
covariance, while each atom is `C delta_chi tensor V`.  A stabilizer element
compresses to `sigma(k)` on this fiber, so covariance leaves its unitary
gauge completely unconstrained.

If `(FAM3)` held in a nonzero finite corner, `t_i s_i=1` would make each
`s_i` invertible and hence `s_i t_i=1`.  The final row would then read
`2I=I`, a contradiction.  Equivalently, taking the ordinary trace in
`(FAM3)` gives twice the corner dimension equal to the corner dimension.
Thus the exact finite covariant model disproves the proposed local
compiler already at zero defect.

For the root-opposite calculation, restrict the elementary matrices to the
ordered coordinates `(i,j)`.  In characteristic two,

```text
y=[[1,0],[1,1]],       x=[[1,q],[0,1]],       y^(-1)=y.
```

Multiplying the three displayed matrices yields

```text
yxy^(-1)=[[1+q,q],[q,1+q]].
```

Because `q!=0`, this has a nonzero lower-root entry and is not a member of
the upper additive root subgroup.  Hence the usual spectral-atom covariance
argument is unavailable as soon as the packet includes an actor genuinely
opposite to its selected root.  This computation uses only elementary
matrix multiplication; passing from the Steinberg group to its elementary
matrix image is enough to disprove normalization upstairs.

For the literal application, the prerequisite proves internally from the
binary Leavitt dimension equation that a nontrivial character of the full
last-column root module has infinitely many pairwise orthogonal parabolic
translates.  Therefore the coefficient orbit responsible for that equation
cannot be captured by the finite dual packet above.  Enlarging finite
windows can approximate longer initial orbit segments, but the radius then
depends on the matrix coordinate; atom minimality supplies no uniform word
bound.  This proves the stated dichotomy and its exact scope.

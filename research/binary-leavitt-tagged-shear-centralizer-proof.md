---
rg: 2
id: binary-leavitt-tagged-shear-centralizer-proof
kind: route
title: Compute the tagged transvection and apply fixed-mark area properness
target: tagged-shift-shear-has-unbounded-fixed-mark-area
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Write `N=B_iA_j`.  Orthogonality gives

```text
N^2=B_i(A_jB_i)A_j=0,
A_iN=(A_iB_i)A_j=qA_j=A_j,
A_jN=(A_jB_i)A_j=0.                                    (TSCP1)
```

Also `A_j(B_i+D_(ij))=0`, hence

```text
N(B_i+D_(ij))=B_i A_j(B_i+D_(ij))=0.                    (TSCP2)
```

Equations `(TSCP1)--(TSCP2)` prove `(TSC3)`.  Conjugation by
`diag(1,u,1)` right-multiplies an `x_12` coefficient by `u^(-1)=u`,
left-multiplies an `x_23` coefficient by `u`, and fixes the `x_13`
coordinate.  Root additivity then gives `(TSC4)`.  Central ambiguity in the
choice of Steinberg lift has no effect on conjugation.

For the area obstruction, fix one address `i` and vary `j` through infinitely
many orthogonal main addresses.  The elementary images of the `r_(ij)` are
distinct: equality of `u_(ij)` and `u_(ik)` would give

```text
B_iA_j=B_iA_k,
```

and left multiplication by `A_i` would imply `A_j=A_k`.  They also occupy
distinct cosets modulo `<z>`.  Indeed the quotient of two such elementary
images is diagonal with possibly nontrivial second-coordinate unit, whereas
the nonidentity image of `<z>` is the off-diagonal matrix
`1+qE_13`.  Equality is possible only for the identity powers and then only
when the two shears coincide.

Hence the `r_(ij)` give infinitely many distinct cosets in
`C_Delta(z)/<z>`.  The properness theorem says every fixed sublevel set of

```text
r<z> |-> Area([r,z])                                    (TSCP3)
```

is finite, uniformly over the representing words.  Consequently `(TSC6)`
is unbounded.  Conjugating `delta_0` by `r_(ij)` changes its terminal literal
mark from `z` to `r_(ij)zr_(ij)^(-1)`; any bounded same-mark shear comparison
would include a bounded filling of precisely `(TSCP3)`, contradicting this
unboundedness.

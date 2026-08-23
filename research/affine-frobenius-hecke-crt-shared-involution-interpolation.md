---
rg: 2
id: affine-frobenius-hecke-crt-shared-involution-interpolation
kind: claim
title: Interpolate each shared BCS involution across the large affine Frobenius right ideals
distinct_from:
  affine-frobenius-packets-solve-local-row-mask-storage: that produces the fixed context PVMs and their local marginals; this must construct one global group-algebra involution agreeing with all occurrences on private masks.
  signed-hecke-block-escaping-cycle-holonomy: that closes exact marginal equality in one common signed corner; this asks only rowwise right-ideal agreement with a weighted deficit budget.
  free-relative-placement-closes-one-balanced-chord: that may choose a new joint coordinate placement for one edge; this cannot change the already fixed context PVM or use a separate shared involution on each edge.
---

OPEN.  Starting with the affine Frobenius context packets of
`affine-frobenius-packets-solve-local-row-mask-storage`, enlarge their free
product by finitely many group elements and finite-support Hecke coefficients
so that for every variable `x` there is one element

```text
B_x=B_x^*=B_x^(-1)                                    (AFI1)
```

and, for every incident context, a projection `q_(c,x)` with

```text
(B_x-A_(c,x))q_(c,x)=0.                               (AFI2)
```

The same fixed context PVM supplies all `A_(c,x)`, and the weighted sum of
canonical deficits of the masks, together with predicate deficits, is below
the finite game gap.

## Attempts

- A literal group element cannot implement arbitrary matrices on the whole
  faithful Frobenius block; `finite-support-one-sided-stabilizers-are-torsion`
  gives the general support obstruction.  More sharply,
  `literal-involution-agreement-mass-at-most-half`
  shows that one distinct literal involution already spends deficit at least
  `1/2`.  The shared `B_x` must be a genuinely additive group-algebra unitary.
- Direct orthogonal patching spends total trace at least one.  A common mask
  recreates the stronger signed-corner problem.  The intended room is a
  multi-piece self-adjoint Hecke unitary on several noncommuting large right
  ideals.
- The context blocks cannot remain freely independent while that unitary is
  added.  `rowwise-shared-involution-forces-pairwise-marginal-closeness`
  gives the necessary inequality
  `(1/4)||A_(c,x)-A_(d,x)||_2^2<=delta_(c,x)+delta_(d,x)`.
  For unbiased marginals in distinct free factors the left side is `1/2`.
  The overlap relations must therefore create the required canonical
  correlation among the fixed marginals, not merely attach `B_x` afterward.
- Independent uses of the one-chord transport cell may change the context
  PVM from incidence to incidence.  Such a construction does not feed the
  ambient identity-Gram BCS gap and is invalid.
- A finite graph of finite groups remains virtually free and therefore
  cannot realize a strict row-mask budget.  At least one overlap cycle must
  use a non-Bass--Serre relation or infinite edge algebra.

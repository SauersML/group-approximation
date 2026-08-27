---
rg: 2
id: dirac-average-is-a-sharp-near-extra-clifford-generator
kind: claim
title: The Dirac average is a same-model near-extra Clifford generator at inverse-square-root rank error
artifacts:
  - research/artifacts/section-three-quantitative-no-go-audit-2026-08-21.md
distinct_from:
  clifford-total-energy-ledger-has-inverse-sqrt-log-critical-rate: that derives the critical rate from total row energy and gives an orthogonal-block sharpness example; this constructs the near-extra generator inside one irreducible Clifford block, with no reducing-block localization.
  robust-clifford-capacity-bound: that forbids a sufficiently accurate complete-table representation beyond the exact capacity; this gives an explicit local-relator model at the boundary and shows why a local decoder must lose rank-dependent constants.
  infinite-index-does-not-force-supercritical-site-rank: that uses exact tensor truncations with no supercritical generator; this adds one genuinely new same-space involution which approximately anticommutes with every old generator.
---

**ESTABLISHED.**  Let `X_1,...,X_(2m)` be self-adjoint unitaries satisfying

```text
X_iX_j=-X_jX_i                    (i!=j).              (DAG1)
```

Define the normalized Dirac average and chirality operator

```text
A=(2m)^(-1/2) sum_(i=1)^(2m) X_i,
Gamma=i^m X_1X_2...X_(2m).                             (DAG2)
```

Then exactly

```text
A=A^*,       A^2=1,       Gamma=Gamma^*,       Gamma^2=1,
{A,X_i}=sqrt(2/m) 1,      {A,Gamma}=0.                (DAG3)
```

Thus on the irreducible `2^m`-dimensional Clifford module, `A` is a literal
involution in the same matrix algebra which behaves like an additional
Clifford generator with per-old-generator anticommutation defect

```text
sqrt(2/m)=Theta(1/sqrt(log d)),        d=2^m.          (DAG4)
```

It even anticommutes exactly with chirality.  This is a stronger sharpness
test than padding failures into reducing blocks: the error is coherent inside
one irreducible Clifford factor.

## Coefficient audit

The linear Clifford-basis expansion in `(DAG2)` has exact coefficient norms

```text
||coeff(A)||_2=1,              ||coeff(A)||_1=sqrt(2m). (DAG5)
```

Accordingly a claimed upper bound `sqrt(2m)` for the coefficient `l1` mass is
verified, in fact with equality.  A dimension-independent `l1` or ordinary
word-telescoping bound is false and must be weakened to `(DAG5)`.  Substituting
`A` into a product of length `L` can have the naive coefficient-mass bound
`(2m)^(L/2)`; the cancellation proving `A^2=1` is algebraic Clifford
cancellation, not bounded coefficient mass.

There is a robust expansion identity, but it also displays growing local
loss.  For arbitrary self-adjoint matrices `X_i`, the same definition gives

```text
||A^2-1||_2
 <=(1/(2m))(
      sum_i ||X_i^2-1||_2
      +sum_(i<j)||X_iX_j+X_jX_i||_2).                 (DAG6)
```

If every displayed old relation has defect at most `delta`, the right side is
at most `(m+1/2)delta`.  Likewise

```text
||{A,X_k}-sqrt(2/m)1||_2
 <=(1/sqrt(2m))(
      2||X_k^2-1||_2
      +sum_(j!=k)||X_jX_k+X_kX_j||_2),                (DAG7)
```

which is at most `(2m+1)delta/sqrt(2m)`.  Hence the exact Dirac example
validates the critical scale but does not provide a dimension-uniform
approximate-presentation compiler.

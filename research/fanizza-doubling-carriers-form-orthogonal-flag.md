---
rg: 2
id: fanizza-doubling-carriers-form-orthogonal-flag
kind: claim
title: The Fanizza doubling carriers form an orthogonal flag with a group-word skeleton
distinct_from:
  fanizza-bcs-polynomial-doubling-tape: that imports the projection recurrence and its polynomial certificates; this extracts its exact finite-prefix Boolean geometry and the corresponding involution word.
  nested-schur-multiplicity-wire-globalizes-selectors: that forbids commuting all past and future context selectors; this proves that commuting only the derived carrier and first-hit flags is valid in the exact source model.
  binary-cut-projection-recurrence-gives-bfe1: that cuts the target by an arbitrary involution and derives a scalar balance; this identifies the canonical symmetric-difference word and computes its sole missing overlap term.
---

Let `P_n` be projections and `X_n` unitaries in a unital C-star algebra, and put

```text
R_n=X_n P_n X_n^*.
```

Assume the exact Fanizza recurrence

```text
P_n+R_n=P_(n+1).                                          (FOF1)
```

Then

```text
P_n R_n=0,                 P_n,R_n<=P_(n+1),             (FOF2)
P_n=P_0+sum_(j<n)R_j.                                   (FOF3)
```

Consequently the projections

```text
P_0,R_0,R_1,...
```

are pairwise orthogonal, every `P_n` is their initial sum, and all carrier
and first-hit projections commute.  For

```text
Z_n=1-2P_n,                 Y_n=X_n Z_n X_n^*,
```

one therefore has the literal group-word identity

```text
[Z_n,Y_n]=1,                Z_(n+1)=Z_n Y_n.              (FOF4)
```

The exact amount forgotten by `(FOF4)` is also explicit.  For arbitrary
commuting self-adjoint involutions `Z,Y`, put

```text
A=(1-Z)/2,       B=(1-Y)/2,       C=(1-ZY)/2.
```

Then

```text
A+B-C=2AB,                  ||A+B-C||_2^2=4 tau(AB).      (FOF5)
```

Thus a finite group presentation may carry the entire finite carrier flag by
commuting involution words.  It still has to make the positive overlap `AB`
pay normalized-HS energy.  The affine word skeleton does not enforce
orthogonality; it isolates orthogonality as the sole nonlinear local datum.

This distinction permits a carrier-only finite-depth Schur bridge: retaining
the corrected child sign that labels `P_n` is compatible with exact
completeness, while retaining the original context selector centers remains
forbidden.  Any proposed completion must be tested on `(FOF5)` rather than
credited with the exact recurrence merely from `(FOF4)`.

---
rg: 2
id: one-s3-row-rounds-joint-source-pvm
kind: claim
title: One commuting target row rounds both source signs to a joint Q-corner PVM
artifacts:
  - research/artifacts/labelled-pvm-lin-gram-audit-2026-08-23.md
distinct_from:
  labelled-pvm-branch-gram-gives-lin-corner: that starts after a labelled source PVM is available, or avoids the issue by anchoring only one source bit; this constructs the four-atom source PVM when both original covariance rows are retained.
  de-la-salle-full-pinching-rounds-one-reflection: that rounds one reflection against an already exact arbitrary PVM with constant twenty; this first compresses to a nonreducing Q-corner and gives explicit two-reflection constants by one binary pinch.
  common-source-covariance-locks-binary-marginals: that needs no joint source measurement and extracts only marginal traces; this proves an operator-level joint PVM on the common source corner.
---

**ESTABLISHED.**  Let `Q` be a projection and let `Z_X,Z_Y` be reflections
in a finite tracial matrix algebra.  Put

```text
c_j=||[Q,Z_j]||_2,
c_XY=||Q[Z_X,Z_Y]Q||_2.                               (SJP1)
```

There are commuting reflections `R_X,R_Y` in the corner `QMQ`, with corner
unit `Q`, such that

```text
||R_X-QZ_XQ||_2<=c_X/sqrt(2),                         (SJP2)
||R_Y-QZ_YQ||_2
 <=(c_Y+c_XY)/sqrt(2)+(3/2)(c_X+c_Y).                 (SJP3)
```

Consequently

```text
E_(a,b)=((Q+aR_X)/2)((Q+bR_Y)/2),  a,b in {+1,-1},   (SJP4)
```

is one exact four-atom PVM summing to `Q`.

Suppose additionally that `V` is a contraction with `V^*V=Q`, that
`A_X,A_Y` are commuting reflections, and

```text
D_j=A_jV-VZ_j,             d_j=||D_j||_2.             (SJP5)
```

Then

```text
c_j<=2d_j,                 c_XY<=2(d_X+d_Y),          (SJP6)
```

so `(SJP2)--(SJP3)` give, explicitly,

```text
||R_X-QZ_XQ||_2<=sqrt(2)d_X,
||R_Y-QZ_YQ||_2
 <=sqrt(2)d_Y+(3+sqrt(2))(d_X+d_Y).                   (SJP7)
```

Thus the original two-row covariance interface `(SEC2)` already pays for
the joint source PVM; it has no additional analytic source-rounding hole.
This conclusion does not follow from positive branch-Gram mass alone.  The
one-bit Lin reduction must retain the unanchored same-Gram covariance rather
than citing `(SJP7)` after discarding `(SEC2)`.

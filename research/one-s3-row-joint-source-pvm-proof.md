---
rg: 2
id: one-s3-row-joint-source-pvm-proof
kind: route
title: Compress, sign, and binary-pinch the two source reflections
target: one-s3-row-rounds-joint-source-pvm
requires:
  - aggregate-cut-compression-stores-boundary-as-involution-defect
  - binary-face-pvm-is-determined-by-coordinate-reflections
---

In `QMQ` put `X_j=QZ_jQ` and let `S_j=sgn_Q(X_j)`, choosing either sign on
the zero eigenspace.  Block compression and the scalar inequality
`(1-|t|)^2<=1-t^2` give

```text
||S_j-X_j||_2^2
 <=tau(Q-X_j^2)=(1/2)||[Q,Z_j]||_2^2.                 (1)
```

Expanding the two compressed products gives

```text
||[X_X,X_Y]||_2
 <=c_XY+(c_X+c_Y)/sqrt(2).                            (2)
```

Indeed, the difference from `Q[Z_X,Z_Y]Q` consists of the two off-diagonal
blocks `QZ_X(1-Q)Z_YQ` and `QZ_Y(1-Q)Z_XQ`, whose norms are at most
`c_X/sqrt(2)` and `c_Y/sqrt(2)`.  Telescoping from `X_j` to `S_j` and using
`||X_j||,||S_j||<=1` yields

```text
||[S_X,S_Y]||_2
 <=c_XY+(3/sqrt(2))(c_X+c_Y).                         (3)
```

Let `p=(Q+S_X)/2` and pinch `S_Y` by the binary PVM `(p,Q-p)`:

```text
Y=pS_Yp+(Q-p)S_Y(Q-p).
```

The exact block-compression identity and sign rounding inside the two
blocks give a reflection `R_Y=sgn_Q(Y)` commuting with `S_X` and

```text
||R_Y-S_Y||_2<=||[S_X,S_Y]||_2/sqrt(2).               (4)
```

Set `R_X=S_X`.  Combining `(1)`, `(3)`, and `(4)` proves
`(SJP2)--(SJP3)`.  The two reflections commute, so the elementary binary
Fourier formula in `binary-face-pvm-is-determined-by-coordinate-reflections`
proves `(SJP4)`.

For `(SJP6)`, direct expansion gives

```text
[Q,Z_j]=D_j^*V-V^*D_j,
```

hence `c_j<=2d_j`.  Commutativity of `A_X,A_Y` also gives

```text
V[Z_X,Z_Y]
 =-(A_XD_Y+D_XZ_Y)+(A_YD_X+D_YZ_X).
```

Since `V^*V=Q`, one has `||VW||_2=||QW||_2` for every `W`; compression on
the right is contractive.  Therefore `c_XY<=2(d_X+d_Y)`.  Substitution in
`(SJP2)--(SJP3)` proves `(SJP7)`.

---
rg: 2
id: damped-cloud-scalar-fixed-sheet-proof
kind: route
title: Preserve every scalar occurrence sign and compute the equality cross term exactly
target: damped-cloud-face-return-has-an-exact-scalar-fixed-sheet
requires:
  - damped-cloud-averaging-contracts-from-exact-faces
  - fixed-parity-faces-exactify-with-loewner-row-square-control
---

For a scalar occurrence sign `a in {+1,-1}` and a cloud mean `s in [-1,1]`,

```text
 a((1-t)a+ts)=1-t+tas >=1-2t>0.                         (DCSP1)
```

Hence `sign((1-t)a+ts)=a` whenever `t<1/2`.  Applied to every occurrence of
one exact scalar face, the first stage of the local exactifier recovers the
entire old face.  It already commutes and has the prescribed product, so the
rest of the construction is stationary.

For the implementation-independent statement, fixed-width telescoping gives
`H_face^sym(X(t))<=C_q'tI` on the scalar block.  If an exact scalar output
changes one sign, its squared displacement from `X(t)` at that coordinate is
at least `(2-2t)^2I`.  Choose `t_*(q)>0` so that

```text
 C_q C_q' t <(2-2t)^2       for 0<t<t_*(q).             (DCSP1a)
```

Then `(LFE2)` excludes every changed scalar face character.  Thus any return
whose only global guarantee is the same local Loewner movement bound is
stationary on this sheet for sufficiently small damping.

For two occurrences in one cloud the mean cancels from both differences:

```text
 X_u-X_v=(1-t)(A_u-A_v),
 (A_u-X_u)-(A_v-X_v)=t(A_u-A_v).                        (DCSP2)
```

Expanding the squared norm proves `(DCF5)` edge by edge.  Weighted summation
over every equality expander proves the exact cancellation for the normalized
equality energy.  The length-three repetition example supplies an explicit
balanced original-plus-pair-sum instance, and central direct-sum weighting
supplies arbitrarily small energy.

For the all-`t<1` version, duplicate each of the three length-three faces and
put opposite constant signs on its two copies.  Every coordinate occurs in
two opposite-sign pairs, hence has regular cloud mean zero.  Equation
`(DCSP1)` then improves to

```text
 sign((1-t)a)=a       for every 0<t<1,                  (DCSP3)
```

which includes the optimized damping parameter of `(DCA3)`.

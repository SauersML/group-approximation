---
rg: 2
id: unstabilized-reset-pencils-have-no-s3-symmetry
kind: claim
title: No compatible rank-fifteen reset plane carries the unstabilized S3 pencil action
artifacts:
  - experiments/reset_plane_pencil_symmetry_audit.py
  - experiments/reset-plane-pencil-symmetry.json
distinct_from:
  fanizza-schur-menu-has-common-codimension-one-residual: that finds seven two-planes whose three nonzero forms are individually nondegenerate on fixed hyperplanes; this tests whether those three restricted forms are coherently permuted on the same residual coordinates.
  s3-reset-plane-has-common-invariant-selector-polarization: that gives a positive S3 action on the selector symplectic coordinates; this is the negative residual-pencil calculation.
---

For every one of the seven compatible reset planes reported by the arity-four
common-residual replay, choose two restricted invertible matrices `B_1,B_2`
and put

```text
T=B_1^(-1) B_2 in GL_15(F_2).                            (URP1)
```

Strict equivalence of the pencil under the two generators of
`GL_2(F_2)=S_3` would require

```text
T similar to T^(-1),
T similar to I+T.                                       (URP2)
```

The exact replay factors the characteristic polynomial over `F_2` and
compares the nullities of every power of every primary polynomial factor,
which is a complete similarity invariant.  For all seven planes both
similarities in `(URP2)` fail.  Thus no choice of left/right bases on the
single rank-fifteen residual makes the three compatible directional forms
one honest `S_3` pencil.

This invalidates the unstabilized equivariant reset shortcut, not the reset
program.  Regular-orbit induction supplies a finite coherent stabilization
without asking `(URP2)`.

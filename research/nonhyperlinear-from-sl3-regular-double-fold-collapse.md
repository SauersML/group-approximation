---
rg: 2
id: nonhyperlinear-from-sl3-regular-double-fold-collapse
kind: route
title: A regular fold-mark collapse makes the arithmetic double non-hyperlinear
target: non-hyperlinear-group
requires:
  - sl3-regular-arithmetic-double-fold-mark-collapse
  - sl3-arithmetic-double-finite-representations-fold
---

The group

```text
D=SL_3(Z[1/2]) *_(SL_3(Z)) SL_3(Z[1/2])
```

is finitely presented.  Its fold-kernel word
`w=i_0(h)i_1(h)^(-1)` is nontrivial by amalgam normal form.  If `D` were
hyperlinear, it would have finite-dimensional approximate representations
with canonical character.  The prerequisite says those assignments satisfy
`|tr(w)|->1`; canonical character says `tr(w)->0`.
This contradiction makes `D` an explicit non-hyperlinear group.

The exact folding theorem records why this is the sharp continuation of the
finite-model calculation: every genuine finite-dimensional representation
already kills `w` (indeed the whole fold kernel), and only the normalized-HS
promotion on full regular microstates remains.

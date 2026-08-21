---
rg: 2
id: local-exterior-square-pauli-proof
kind: route
title: Label a locally rank-one pair by the one-qubit Pauli plane
target: local-exterior-square-kernel-yields-pauli-strategy
requires: []
---

For each coordinate `e`, put

```text
Q_e = P(u_e,v_e),
P(0,0)=I, P(1,0)=sigma_X, P(0,1)=sigma_Z,
P(1,1)=sigma_Y.                                             (LEP1)
```

Condition `(LES1)` says that on a fixed view `S_j` all nonidentity `Q_e`
are the same Pauli reflection.  They therefore commute.  Their joint
spectral measurement has two possible binary answer strings: zero and the
unique nonzero vector spanning `u|S_j,v|S_j`.  Both belong to `C_j`, so this
is a perfect local-codeword PVM.  The observable induced on a coordinate is
always `(LEP1)`, independently of the incident view, hence all overlap tests
are also perfect.

Global independence of `u,v` means the `2` by `|E|` matrix with rows `u,v`
has rank two.  Some two columns therefore have determinant one.  The
corresponding Pauli reflections anticommute, excluding a common global PVM.

More quantitatively, two reflections in `(LEP1)` anticommute precisely when
the determinant in the left side of `(LES3)` is one, while a local view
fails to be commuting precisely when its two restricted rows have rank two.
If an operator decoder had a dimension-independent modulus, applying it to
these Pauli tables would force `(LES3)` (up to an inessential change of
modulus from the triangle inequality).  This proves the asserted necessary
condition.


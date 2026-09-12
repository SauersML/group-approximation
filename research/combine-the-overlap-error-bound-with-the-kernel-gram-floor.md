---
rg: 2
id: combine-the-overlap-error-bound-with-the-kernel-gram-floor
kind: route
title: Push quotient accuracy through the closing face and conjoin the kernel-cycle floor
target: triangle-lifts-avoid-both-tree-anchor-faces
requires:
  - scalar-tree-perturbations-linearly-control-closing-face
  - three-face-ucp-balancing-needs-macroscopic-tree-motion
---

Because `q` is a complete contraction and
`q o E_epsilon^A=E_epsilon^Q`,

```text
r_13(Phi)
 >=||q o Phi|_(B_13)-E_epsilon^Q|_(B_13)||_cb
 >=r_0-||q o Phi|_(B_13)-id_(B_13)||_cb
 >=r_0-zeta(Phi).                                         (1)
```

The linear overlap estimate `(STQ3)` gives

```text
r_13(Phi)<=C_Delta eta(Phi).                              (2)
```

Combining `(1)` and `(2)`, and using `eta>=0`, proves `(TAT3)`.

Equation `(TAT4)` is exactly `(TFB2)`.  It applies to the same `Phi` and does
not use quotient accuracy.  Therefore it can be conjoined with `(TAT3)`.
Substituting `zeta<=r_0/2` gives `(TAT5)`.

Finally `r_0>0`: the identity and scalar augmentation are distinct ucp maps
on the nontrivial finite-dimensional algebra `C^*(P_13)`.  All constants are
fixed by the one triangle and are independent of the codomain representation
or any relator reservoir.

---
rg: 2
id: positive-cycle-near-unitary-edges-force-trivial-holonomy
kind: claim
title: A positive block cycle with near-unitary edges has quantitatively trivial holonomy
distinct_from:
  c2-root-chart-maslov-holonomy-gap: that must construct and synchronize the positive cycle from the arithmetic root charts and identify its product with the Maslov scalar; this is the dimension-free analytic inequality once such a positive cycle kernel is available.
  exel-loring-mark-quantization: that uses a K-theoretic winding index for almost commuting matrices; this is an elementary Gram-isometry telescoping inequality for a finite positive block matrix.
---

Let `K=[K_ij] in M_m(M_d)` be positive with `K_ii=I_d`, indices cyclic
modulo `m`, and let `U_0,...,U_(m-1)` be unitaries in `M_d`.  Put

```text
epsilon_i = ||K_(i,i+1)-U_i||_(2,d).
```

Then

```text
||I-U_0 U_1 ... U_(m-1)||_(2,d)
 <= sum_i sqrt(2 epsilon_i).                              (PCH1)
```

Consequently, if the edge product is the nontrivial Maslov scalar
`omega I`, then

```text
max_i epsilon_i >= |1-omega|^2 / (2m^2).                 (PCH2)
```

Both bounds are independent of `d`.  Thus the holonomy-payment step in the
finite-operator-system/root-chart approach is elementary once the local
positive kernels have been synchronized into one positive cycle matrix.

The proof is `positive-cycle-holonomy-gram-telescoping-proof`.

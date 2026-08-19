---
rg: 2
id: regular-atlas-boundary-tangent-is-h-fixed
kind: claim
title: The regular-A8 atlas boundary tangent kernel is exactly the H-fixed tangent space
artifacts:
  - experiments/atlas_boundary_h_irrep_tangent.py
  - experiments/atlas-boundary-h-irrep-tangent.json
  - experiments/atlas-boundary-h-irrep-greedy.json
---

At the certified classical alignment, let `J_B` be the derivative of the 234
first-boundary collision words with respect to motion of the second chart in
the left regular `A_8` representation, and let `J_H` be the four covariance
derivatives for the standard transvections generating

```text
H=diag(GL_3(2),1).
```

Then for every external multiplicity `k>=1`, on the tangent space of the
amplified regular model,

```text
ker(J_B tensor I_k) = ker(J_H tensor I_k).
```

In fact the five boundary indices

```text
0, 11, 30, 44, 55
```

already have the same common tangent kernel.  Thus the boundary packet has no
infinitesimal escape direction other than motion that already preserves the
`H` covariance; the remaining atlas obstruction is genuinely nonlinear/global,
not an unexamined regular-representation tangent mode.
---
rg: 2
id: point15-boundary-tangent-equals-s3-covariance-kernel
kind: claim
title: In the point15 A8 model the full boundary tangent kernel is exactly the H-covariance tangent kernel
distinct_from:
  atlas-two-s3-covariance-collapse: that is a nonlinear dimension-free theorem for the regular A8 model; this is an exact characteristic-zero infinitesimal certificate in the 15-point permutation representation only
artifacts:
  - experiments/atlas_boundary_h_exact_point15.py
  - experiments/atlas-boundary-h-exact-point15.json
  - experiments/atlas_boundary_h_tangent_screen.py
---

At the certified classical inner alignment, let `J_B` be the derivative of all
234 first-boundary words when only the second `A_8` chart moves in the natural
15-point permutation representation, and let `J_H` be the derivative of the
four adjacent transvections generating

```text
H=diag(GL_3(2),1).
```

Over characteristic zero,

```text
ker(J_B) = ker(J_H).                                   (P15T)
```

Equivalently, for the exact integer Gram matrices

```text
G_B=J_B^*J_B,
G_H=J_H^*J_H,
```

both have rank `212` on the `225`-dimensional endomorphism space, and every
vector in the thirteen-dimensional rational nullspace of `G_B` is killed by
`G_H`.

Thus the modular tangent screen was not a finite-field accident in the
smallest faithful permutation model.  The remaining infinitesimal
certification problem for the live atlas route is now specifically to lift
this exact kernel containment to the regular representation (preferably as a
group-algebra/module identity); even that would still be only the linearized
input to the nonlinear collapse claim.

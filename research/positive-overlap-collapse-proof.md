---
rg: 2
id: positive-overlap-collapse-proof
kind: route
title: Compare the cross-Gram lower and upper bounds
target: positive-overlap-curvature-collapses-carrier
requires: []
---

Put `Theta=||T_1^*T_2||_2^2`.  The source-specific matrix compactness
estimate gives

```text
Theta >= (s-c)/2-Lambda/beta_B^corner.                 (1)
```

For disjoint exact tag types, the finite-group intertwiner gap gives

```text
2Theta=sum_(i!=j)||T_i^*T_j||_2^2
 <=4 E_tag/kappa(H,S_H).                               (2)
```

Thus `Theta<=2E_tag/kappa`.  Substituting in `(1)` and rearranging proves

```text
s-c<=2Lambda/beta_B^corner+4E_tag/kappa(H,S_H).
```

If `s-c>=a tau(P)-o(1)` and `Lambda<=K E_rel+o(1)`, division by `a`
gives the carrier bound

```text
tau(P)<=2K E_rel/(a beta_B^corner)
       +4E_tag/(a kappa(H,S_H))+o(1).
```

The lower estimate is explicitly matrix-only, so this deduction does not
collapse the exact non-CE witness.

---
rg: 2
id: compressed-adjoint-moment-identity-proof
kind: route
title: Expand the squared displacement on the retained projection
target: ir-survival-is-one-compressed-adjoint-moment
requires: []
---

Since `Pi_n(f_0)` is unitary and `P_n` is a projection,

```text
||(Pi_n(f_0)-1)P_n||_(HS)^2
 =Tr_(HS)(P_n(2-Pi_n(f_0)-Pi_n(f_0)^*)P_n)
 =2r_n-2 Re Tr_(HS)(P_n Pi_n(f_0)P_n).
```

Divide by `r_n` to obtain `(CAM3)`, and take the lower limit.  This proves
the equivalence of `(IR3)`, `(CAM2)` and `(CAM4)`.

For `(CAM5)`, identify `HS(C^(d_n))` with its usual Hilbert space and use
the normalized identity vector `1/sqrt(d_n)`.  The left-right action gives

```text
<Pi_n(f_0)1,1>_(HS)/d_n
 =tr_(d_n)(u_n(f_0)v_n(f_0)^*).
```

The right side is the normalized trace of the canonical cross word, proving
the asserted distinction between the distinguished-vector and compressed
adjoint moments.

---
rg: 2
id: group-sos-certificate-survives-hs-adjoint-microstates-proof
kind: route
title: Evaluate the SOS identity through the adjoint defect map
target: group-sos-certificate-survives-hs-adjoint-microstates
requires: []
---

For unitaries `U,V in U(d)`, with `a=tau_d(U*V)`, the normalized trace of
`Ad_(U*V)` on `M_d` is `|a|^2`. Hence

```text
||Ad_U-Ad_V||_(2,H)^2=2-2|a|^2<=2 d_2(U,V)^2.          (1)
```

For finitely supported `u=sum_g u_g g` and `v=sum_h v_h h`, expansion and the
triangle inequality therefore give

```text
||L_phi(u)L_phi(v)-L_phi(uv)||_(2,H)
 <=sqrt(2) delta ||u||_1||v||_1.                       (2)
```

Inverse normalization gives `L_phi(u*)=L_phi(u)*`. Apply `(2)` to
`(Delta,Delta)` and every `(xi_j*,xi_j)`, then subtract the exact linear
evaluation of `(SOS)`. This is `(ASOS)`.

For the Laplacian of an inverse-closed set `S`, the sum of the `T_s` is
self-adjoint and

```text
<Az,z>=(1/(2|S|))sum_s||T_s z-z||_2^2>=0,
```

so `A>=0`.

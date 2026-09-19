---
rg: 2
id: five-fourths-projection-surplus-routing-proof
kind: route
title: Compare traces of projection transports against the parent exit capacity
target: five-fourths-projection-surplus-pays-linear-hs-energy
requires:
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
---

The full V4 packet supplies projections `F_00,F_01,F_11,P_f` with

```text
sum_b tau(F_b)=(5/4)tau(P_f).
```

Unitary transport preserves each source trace.  For two projections `Q,E`,
compression by `E` shows `0<=tau(EQE)<=min(tau(E),tau(Q))`; expanding the
squared normalized-HS distance gives

```text
||Q-E||_2^2>=|tau(Q)-tau(E)|.
```

The scalar triangle inequality then charges the excess of total incoming
trace over total exit trace.  An exit-capacity slack `ell` leaves exactly
`tau(P_f)/4-ell`, proving `(VRE3)` and `(VRE6)`.


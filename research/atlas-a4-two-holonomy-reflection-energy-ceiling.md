---
rg: 2
id: atlas-a4-two-holonomy-reflection-energy-ceiling
kind: claim
title: The A4 packet and 19243 keep the core-reflection energy at most one third
distinct_from:
  atlas-a4-parabolic-c3-bridge-energy-ceiling: that separately budgets the two packet S3 letters, the central C3 letter, and the collision involution; this asks only for the combined core holonomy c=hk and collision-C3 reflection a=zb.
---

Let `U_n` satisfy the normalized exact-regular A4 packet hypotheses and
`q_19243(U_n)->1`.  With

```text
c=hk,
a=zb,
E_2HOL(U)=2 delta_U(c)^2+delta_U(a)^2
```

as in `atlas-t30-is-one-parabolic-c3-bridge`, prove

```text
limsup_n E_2HOL(U_n)<=1/3.                             (A4-2HOL-CEIL)
```

This is sufficient, not asserted established.  The exact two-holonomy
factorization and spherical chord bound give the strict rational estimate

```text
limsup_n x30(U_n)^2<=338/729<1/2.
```

The target is deliberately expressed in the two gauge-invariant combinations
which the exact subgroup geometry singles out.  It does not separately ask
the two disconnected packet components to synchronize `h` and `k`, nor does
it separately decode `z` from the collision involution `b`.

## Attempts

- After the `K_(2,2) disjoint_union K_(2,4)` tree gauge, identify `c=hk` with
  the relative phase between the two component root gauges and `a=zb` with
  the 19243 residual in the commuting `S3` partner.  Seek a two-variable
  connection-Laplacian or trace inequality rather than reconstructing four
  individual letter defects.
- `atlas-two-holonomy-endpoint-localization` makes the required compiler map
  precise: `h` lies on the `K_(2,2)` component, `k,z` lie on `K_(2,4)`, and
  `b` is collision-only.  Thus `c,a` are cross-component endpoint products,
  not individual rectangle variables.  The four rectangles first remove
  internal cycle gauge; two component-root transports and the collision
  endpoint still have to be decoded.
- The natural threshold is non-strict.  Curvature of the unitary sphere gives
  a fixed gap of `1/2-338/729=53/1458` after the bridge.
- The full spherical threshold is actually
  `12 sin^2(pi/18)>1/3`; the rational `1/3` is retained as the clean packet
  budget.
- `atlas-a4-classical-two-holonomy-profile` exhausts the natural 15-point
  classical sector.  The sharp readout coefficient is `5` on the inner
  automorphism branch but `21/4` on the outer branch; ten outer positions
  violate coefficient `5`.  Thus the sharp `5` observed in the 31-point GL5
  screen is not a universal identity and cannot be promoted without retaining
  additional branch or multiplicity information.

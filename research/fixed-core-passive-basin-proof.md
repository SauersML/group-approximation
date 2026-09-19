---
rg: 2
id: fixed-core-passive-basin-proof
kind: route
title: Minimize the cubic loss away from the compact exact endpoint fiber
target: fixed-core-passive-fiber-has-positive-basin
requires:
  - one-core-endpoint-union-is-one-finite-restriction-fiber
  - sublinear-bs-block-surgery-is-invisible-to-relative-liftability
---

The reflection locus is closed and bounded in `M_d`, and the inversion
equation is closed, so `K_beta` is compact.  The function `L_beta` is
continuous and its zero set in `K_beta` is exactly `Z_beta`.  For fixed
`eta>0`, the set

```text
C_eta={X in K_beta:dist_2(X,Z_beta)>=eta}
```

is compact and disjoint from the zero set.  Therefore `L_beta` has a
strictly positive minimum on `C_eta`, proving `(PFB4)--(PFB5)`.

By `one-core-endpoint-union-is-one-finite-restriction-fiber`, every point of
`Z_beta` factors through `A/<<s^N>>` and the possible multiplicity vectors
form one finite restriction fiber.  This identifies the compact zero set
in `(PFB2)` with the desired simultaneous global endpoints rather than the
larger locus obtained by separately rounding the cubic products.

The direct-sum triangular conclusion follows by choosing a point of
`Z_(beta_n)` within `eta_n` and adjoining the already exact active cell.
`sublinear-bs-block-surgery-is-invisible-to-relative-liftability` proves the
sharp scope statement: replacing the active `o(d_n)` block cannot force the
passive sequence below the moving compactness radius.  A uniform assertion
of that kind is precisely the still-open relative lift.

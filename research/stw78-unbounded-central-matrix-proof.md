---
rg: 2
id: stw78-unbounded-central-matrix-proof
kind: route
title: Match a Blackadar--Handelman amplification with a central matrix size and fold
target: stw78-unbounded-central-matrices-close-relative-quasitrace-case
requires:
  - stw78-central-matrix-folding-descends-proper-infiniteness
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

By the Blackadar--Handelman matrix criterion, absence of a normalized
2-quasitrace on `C` gives an integer `m` for which the unit of `M_m(C)` is
properly infinite.  Choose `r>=m` for which

```text
M_r -> A_infinity intersect A'
```

is unital.

Proper infiniteness persists to the larger matrix size.  In Cuntz notation,
write `u=[1_C]`.  Since `m u` is properly infinite, it absorbs every finite
multiple of itself, while `u<=m u`.  Therefore

```text
r u <= r(m u)=m u <=r u.
```

Thus `r u` is Cuntz equivalent to the properly infinite element `m u`, so
the unit of `M_r(C)` is properly infinite.  Now apply
`stw78-central-matrix-folding-descends-proper-infiniteness` with `n=r`.
Its commuting multiplication map carries two orthogonal isometries from
`M_r(C)` into `B_infinity intersect phi(A)'`, proving O-infinity stability.

The only imported input is the Blackadar--Handelman matrix criterion; the
amplification matching and folding are internal.

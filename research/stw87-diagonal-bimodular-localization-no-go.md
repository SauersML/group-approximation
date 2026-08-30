---
rg: 2
id: stw87-diagonal-bimodular-localization-no-go
kind: claim
title: Diagonal-bimodular localization cannot repair the uniform Roe order-zero defect
distinct_from:
  stw87-diagonal-expectation-order-zero-obstruction: that claim computes the commutative two-point defect for the bare diagonal expectation; this claim proves that every normalized diagonal-bimodular localization before taking the expectation leaves that defect exactly unchanged.
artifacts:
  - research/artifacts/stw87-diagonal-bimodular-localization-no-go-audit-2026-08-30.md
---

Let `X` be a countable discrete bounded-geometry metric space, put

```text
A=C*_u(X),    D=ell^infinity(X),
```

and let `E_X:A->D` be the canonical diagonal expectation.

1. The expectation `E_X` is the unique bounded `D`-bimodule map
   `R:A->D` whose restriction to `D` is the identity.
2. If `S:A->A` is any bounded `D`-bimodule map with `S|_D=id_D`, then

   ```text
   E_X S=E_X.
   ```

Consequently, normalized c.p.c. Schur localizations cannot repair the
order-zero loss caused by diagonal averaging.  If `X` has at least two
points, then after any such localization the exact distance to diagonal
c.p.c. order-zero maps remains `1/2` on the canonical commutative
two-point packet and remains `1` on every canonical noncommutative matrix
packet.  This includes the finite-propagation Schur multipliers supplied by
property-A kernels.

---
rg: 2
id: even-congruence-regular-microstates-obstruct-odd-correction
kind: claim
title: Even-level regular representations stay far from every odd-congruence projective correction
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that asserted universal odd-level correction; this gives an explicit exact regular-trace countersequence.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that concerns strict correction to arbitrary exact representations; the present obstruction survives flexible padding but uses the artificial coprime-level target restriction.
---

Let `Gamma=SL_3(Z)`,
`Gamma(N)=ker(Gamma -> SL_3(Z/N Z))`, and

```text
Q_m=Gamma/Gamma(2^m),   d_m=|Q_m|,
sigma_m=lambda_(Q_m) o q_m.
```

Then `(sigma_m)` is an exact regular-trace microstate sequence, but it has
no flexible projective correction through odd congruence levels. This holds
both for the direct-padding and the isometric almost-invariant-corner
formulations of flexible correction.

Direct rather than projective correction is a fortiori impossible. The
obstruction uses coprime congruence kernels plus property `(T)`; it does
not assert any failure of unrestricted flexible HS correction.

**ESTABLISHED 2026-08-31** by
[[even-odd-adjoint-disjointness-proof]].

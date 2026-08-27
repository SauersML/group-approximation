---
rg: 2
id: traced-kazhdan-transport-counterexample
kind: claim
title: The nine-leaf Leavitt group refutes arbitrary traced-coordinate Kazhdan transport
invalidates:
  - finite-traced-kazhdan-transport-proof
artifacts:
  - research/artifacts/traced-kazhdan-transport-counterexample-2026-08-19.md
distinct_from:
  tracial-coordinate-transport-barrier: that records why the full non-MF architecture cannot simply be moved to tracial coordinates; this gives an exact zero-defect group-factor counterexample to the transport statement itself.
---

There exist a finite tracial von Neumann algebra `(M,tau)`, a group `G`, a
property-`(T)` subgroup `Gamma<G`, an element `u in G` with

```text
u Gamma u^{-1} <= Gamma,
```

and an exact homomorphism `pi:G->U(M)` together with a unitary
`x in pi(Gamma)' cap M` such that

```text
pi(u) x pi(u)^* notin pi(Gamma)' cap M.
```

In particular, the statement of `finite-traced-kazhdan-transport` is false for
arbitrary traced coordinates even when every multiplicative defect is exactly
zero.  The counterexample is the established nine-leaf Leavitt configuration
in its left regular group von Neumann algebra.

---
rg: 2
id: directly-finite-ring-images-kill-retracts-proof
kind: route
title: Apply direct finiteness of the target to the image of a one-sided inverse pair
target: directly-finite-ring-images-of-ca-monoids-kill-retracts
requires: []
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Propositions 3.1 and 3.2 of the artifact.

- **Retracts go to 1:** `rho(sigma) rho(tau) = rho(sigma o tau) = 1`, so `rho(tau) rho(sigma) = 1` in
  the directly finite ring `S`. An anti-homomorphism is a homomorphism into `S^op`, which is directly
  finite as well.
- **Criterion:** a strict `tau` would give the idempotent automaton `tau o sigma != id` with image 1.
- **Faithful rank functions:** if `ab = 1`, then `ba` is idempotent with `rk(ba) >= rk(a (ba) b) = 1`,
  so `rk(1 - ba) = 0` and `ba = 1`.
- **K_0:** `x = tau` and `y = sigma` satisfy `x = (tau sigma) x`, `y = y (tau sigma)`, `xy = tau sigma`
  and `yx = 1`. So `[tau sigma] = [1]`, and `[1 - tau sigma] = 0` with `1 - tau sigma != 0`. The
  augmentation sends every monoid element to `1`, so `1 - f` to `0`.
- **Linear restriction:** linear automata over `F_p^n` form the multiplicative monoid of
  `M_n(F_p[G])` or its opposite, so a separating `rho` gives direct finiteness there.

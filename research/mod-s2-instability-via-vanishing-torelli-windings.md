---
rg: 2
id: mod-s2-instability-via-vanishing-torelli-windings
kind: route
title: Pull back a Dadarlat winding and observe that honest representations cannot absorb it on the separating twist
target: mod-s2-is-not-point-norm-matricially-stable
requires:
  - mod-s2-stability-forces-honest-torelli-windings
  - mod-s2-near-identity-torelli-windings-vanish
---

Suppose `Mod(S_2)` were point-norm matricially stable. By (TW2) of the first prerequisite there would be
honest representations `rho_n` with `||rho_n(t_s) - 1|| -> 0` and `kappa(rho_n(t_s)) = -a kappa_n/(10k) != 0`.
For large `n`, `||rho_n(t_s) - 1|| < eta_0`, so the second prerequisite forces `kappa(rho_n(t_s)) = 0`, a
contradiction. Explicitly, the pulled-back Dadarlat maps `V_n o pi` are asymptotic homomorphisms of
`Mod(S_2)` with no honest approximants.

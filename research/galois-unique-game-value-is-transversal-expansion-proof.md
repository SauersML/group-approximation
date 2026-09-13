---
rg: 2
id: galois-unique-game-value-is-transversal-expansion-proof
kind: route
title: Transversal bijection, stabilizer computation, and left-translation symmetrization of the SDP Gram matrix
target: galois-unique-game-value-is-transversal-expansion
requires: []
artifacts:
  - research/artifacts/ugc-galois-games-2026-09-12.md
---

Complete proofs are Theorems 1--3 of the artifact. Sketch:

* **Value.** `f -> T_f = { tau(v) f(v) }` is a bijection from labelings to
  left transversals. The edge `(v,s)` is satisfied iff `s tau(v) f(v)` is the
  point of `T_f` in the coset `s v`, iff `s t_v in T_f`.
* **Perfect.** Value `1` means `Lambda T = T` for `Lambda = <supp mu>`. If
  `lambda in Lambda cap t K t^-1` with `t in T`, then `t` and `lambda t` both lie
  in `T cap tK`, so `lambda = e`. Conversely, under freeness, one right coset
  `Lambda g_O` per `Lambda`-orbit `O` on `G/K` is a `Lambda`-invariant
  transversal.
* **SDP.** `(>=)`: from `phi(g) = <pi(g) xi, xi>` put
  `u_(v,a) = k^(-1/2) pi(tau(v) a) xi`. `(<=)`: left translates of a feasible
  Gram matrix on the lift points are feasible with the same objective, by
  conjugation invariance of `mu`. Their average is `phi(y^-1 y')/k` with `phi`
  as stated.

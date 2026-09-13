---
rg: 2
id: kazhdan-commutant-compression-stability-is-finitary-proof
kind: route
title: Reduce normalization to the compressor generators, then pass counterexamples to and from an ultraproduct
target: kazhdan-commutant-compression-stability-is-finitary
requires: [rigid-compression-defect-normalization-dichotomy, sofic-groups-kill-rigid-compression-defects, weak-mf-groups-can-carry-rigid-defects, kazhdan-asymptotic-commutant-transport]
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

Full derivation: Section 2 of the artifact.

**Lemma (compressor generators suffice).** For `sigma : G -> U`, put
`C = C_U(sigma(Gamma))`.
1. `sigma(Gamma)` fixes every element of `C` under conjugation.
2. For `t in T`, `sigma(t) C sigma(t)^-1 = C_U(sigma(t Gamma t^-1)) >= C`, since
   `t Gamma t^-1 <= Gamma`.
3. If moreover `sigma(t) C sigma(t)^-1 <= C`, then equality holds and `sigma(t)^-1`
   normalizes `C` too.
4. `G = <F cup T>`. So `sigma(G)` normalizes `C` iff `sigma(t) C sigma(t)^-1 <= C` for
   every `t in T`.

**`NORM => UCS`.** Suppose `UCS` fails at some `eta`.
1. For each `k` pick a `(1/k, k)`-model `u^(k)` in `G_(n_k)` and `z_k` with
   `c(z_k, u^(k)_s) <= 1/k` for `s in F`, but
   `c(u^(k)_t z_k (u^(k)_t)^-1, u^(k)_s) > eta` for some `s_k, t_k`.
2. Fix a free ultrafilter. `F` and `T` are finite, so `s_k = s` and `t_k = t` almost
   everywhere.
3. `sigma(g) = [(u^(k)_g)]` is a homomorphism `G -> U`, because the defects tend to `0`
   and every relation lies in some ball.
4. `z = [(z_k)]` commutes with `sigma(F)`, hence with `sigma(Gamma)`.
5. Inverses are coordinatewise, and the metric of `U` is the limit of the `d_n`. So
   `sigma(t) z sigma(t)^-1` fails to commute with `sigma(s)`, and `NORM` fails.

**`UCS => NORM`.** Suppose `sigma(t) z sigma(t)^-1` is outside `C` for some `t in T` and
`z in C` (by the lemma).
1. Since `F` generates `Gamma`, `eta = max_(s in F) d(w sigma(s), sigma(s) w) > 0`,
   where `w = sigma(t) z sigma(t)^-1`.
2. Take `eps, R` from `UCS` for `eta/2`, and representatives `u^(k)_g` for `g` in the
   `R`-ball with `u_1 = 1`, and `z_k` of `z`.
3. Almost everywhere `u^(k)` is an `(eps, R)`-model and `c(z_k, u^(k)_s) <= eps`.
4. `UCS` bounds `c(u^(k)_t z_k (u^(k)_t)^-1, u^(k)_s)` by `eta/2`. In the limit
   `max_s d(w sigma(s), sigma(s) w) <= eta/2`, a contradiction.

**Rows.**
- *Sofic.* `sofic-groups-kill-rigid-compression-defects` is `DD(sofic)`. The dichotomy
  converts it to `NORM` for every pair, hence `UCS`.
- *Weak MF.* Let `rho : H_K -> U(Q)` be an injective corona representation, `k in K \ {1}`,
  `t` a strict compressor and `gamma in Gamma \ t Gamma t^-1`
  (`weak-mf-groups-can-carry-rigid-defects`). Put `sigma = rho|G`. Then
  `rho(k) in C(sigma(Gamma))`, while `rho([t k t^-1, gamma]) != 1` by injectivity. So
  `NORM` fails, hence `UCS`.
- *Operator norm to 2-norm.* The two directions above run with operator-norm models and
  2-norm commutators of contractions. `kazhdan-asymptotic-commutant-transport` supplies the
  ultraproduct side with only `Gamma` Kazhdan.
- *Model test.* If `t` normalizes `Gamma`, each `t^-1 s t` is a word of bounded length in
  `F`. So `u_t^-1 u_s u_t` is `O(eps)`-close to a product of boundedly many `u_(s')`, and
  `z` almost commutes with it.

---
rg: 2
id: kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes
kind: claim
title: For every p >= 5 the seed t-parts (S0) hold and the Witt-carry syzygy of the A~2 ca edge has value exactly 6 alpha_B, so k(p) = 0 and the three edge jumps are independent (E_p), given the lift of the syzygy
distinct_from:
  kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy: that claim reduces (E_p) to the congruence k(p) != 2 mod p, given the seed formula (S0) and the lift, and computes k(p) = 0 only for p = 5, 7, 11, 13. This claim proves (S0) and k(p) = 0 for every p >= 5 symbolically.
  kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations: that claim computes the three edge jumps for p = 5, 7 and reduces the n=1 case of Open 2 to (E_p). This claim proves (E_p) for every p >= 5, given the lift.
  kms-hc1-a2-pro-p-completion-is-iwahori-criterion: that claim states the criterion and Open 2. This claim settles the n=1 case of Open 2 for every p >= 5, given Open 1 and the lift of the syzygy.
artifacts:
  - experiments/kms-hc1-kassel-seed-2026-09-18/seed_derive.py
  - experiments/kms-hc1-kassel-seed-2026-09-18/seed_derive.out
  - experiments/kms-hc1-kassel-seed-2026-09-18/fo_seed.cpp
  - experiments/kms-hc1-kassel-seed-2026-09-18/etilde.out
  - experiments/kms-hc1-kassel-seed-2026-09-18/etilde11.out
---

Notation of `kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy` (below: the
syzygy claim). Fix a prime `p >= 5`.

- `N = N_(kappa,alpha)` is the Kassel extension `L_p + F z`. Its cocycle is
  `kappa * i delta_(i+j,p) tr(xy) z` on `[x t^i, y t^j]`. Its p-map sends root
  vectors to 0 and sends `h t` to `h t^p + alpha(h) z`.
- On the ca edge, `a = E12`, `b = E23`, `c = E31 t` and `e = [c,a] = E32 t`.
  `H = <a,c,e>` is the Heisenberg subalgebra. `M = u(N)/u(N)H^+` and `m0` is
  the class of 1.
- The seeds are `X_210` and `X_012`: the multidegree-`(2,p,0)` and
  `(0,p,2)` components of `rho(r) m0 - m0`, for the relators
  `r = [a,b,a]` and `r = [b,c,c]`, with `rho(x) = E(rho Y_x)` the truncated
  exponential (as in `fo_dual.cpp`).
- The Witt-carry syzygy is `sigma = (U1,U2)`, with
  `U1 = 2c^3e^(p-3)a - 9c^2e^(p-2)` and `U2 = 2ce^(p-3)a^3 + 3e^(p-2)a^2`.
  Its value is `zeta(sigma) z m0 = U1 X_210 + U2 X_012`, and
  `zeta(sigma) = k(p) kappa + 6 alpha_B` defines `k(p)`.

## Statement

> **(S0), every p >= 5.** `X_210 = E23^(p-2) E13^2 m0` and
> `X_012 = -E23^(p-2) (E21 t)^2 m0`.
>
> **(K), every p >= 5.** `U1 X_210 + U2 X_012 = 6 alpha_B z m0`. So
> `zeta(sigma) = 6 alpha_B` and `k(p) = 0`.

**Consequence.** `k(p) = 0` is not `2 mod p`. By (Red) of the syzygy claim,
the three edge jumps are independent. This is `(E_p)` for every `p >= 5`,
given the lift of `sigma` to `I`, which the syzygy claim argues and checks at
`p = 5, 7`. By (R2) of
`kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations`, given Open 1,
this gives `gr I = ker(A -> u(L_p))` through degree `3p`. That is the `n=1`
case of Open 2 of `kms-hc1-a2-pro-p-completion-is-iwahori-criterion`.

## Proof idea

- **(S0).** On `u(<a,b,E13>) m0`, the letter `a` acts as `E13 d/db`, because
  `a m0 = 0`. So `rho(r) m0` is a computation in `F_p[b]/(b^p)`, truncated at
  `E13^3`, with the truncated exponential `beta = E(b)`. Its only defect is
  `d beta/db = beta + b^(p-1)`. Ten steps give `rho(r) m0 = m0 + E13^2 b^(p-2) m0`.
  The bc edge is the same with `c` acting as `-E21 t d/db`.
- **(K).** Conjugate the whole problem by `G = E(lambda b)` over `F_p[lambda]`.
  Modulo `lambda^p`, conjugation by `G` is `exp(lambda ad b)`, an automorphism,
  and it moves `(a,c,e)` to `(a + lambda E13, c - lambda E21 t, e~)`. On `m0`,
  `(a + lambda E13)^2 = lambda^2 E13^2` and `(c - lambda E21 t)^2 = lambda^2 (E21 t)^2`.
  So the coefficient of `lambda^(p-2)`, with `1/(p-2)! = 1`, turns the integral
  identity `U1 a^2 - U2 c^2 = -6 e^p` into `U1 X_210 + U2 X_012 = -6 [lambda^p] G e~^p m0`.
- **The p-th power.** `e~ = t(E32 - lambda hB - lambda^2 E23)` is `t` times a
  square-zero matrix. For a degree-1 element `tX`, the Kassel cocycle adds
  nothing to `(tX)^[p]`: the z-part of every Jacobson word is
  `kappa tr(Y (ad Y)^(p-2) U) = 0`. So `e~^[p] = -lambda^p alpha_B z`.

## Status

- **Proved, every p >= 5:** (S0) and (K). This makes (A) of the syzygy claim
  unconditional.
- **Checked:** (S0) against `seed_derive.py` for `p = 5..31`
  (`seed_derive.out`) and against `SEEDGEN` for `p = 5..13` (syzygy claim).
  The intermediate identity `W = R` of the proof, and `zeta(sigma) = 6 alpha_B`,
  are checked exactly at `p = 5, 7` for three values of `alpha`
  (`etilde.out`) and at `p = 11` for two (`etilde11.out`), with mode
  `ETILDE=1` of `fo_seed.cpp`.
- **Still argued, not formalised:** the lift of `sigma` to `I` (S) of the
  syzygy claim. (E_p) for every `p` depends on it and on Open 1.

## Attempts

1. **Divided powers (fails).** Writing `X_210` as `a^2 E23^p m0 / (p(p-1))`
   loses exactly the torsion term `-6 z m0`, so it cannot see `k(p)`.
2. **Conjugation by `E(lambda b)` (works).** See the route. Only the orders
   `lambda^j` with `j < p` of `G` are used, so nothing is divided by `p`. What
   is left open is the lift of `sigma` to `I` ((S) of the syzygy claim).

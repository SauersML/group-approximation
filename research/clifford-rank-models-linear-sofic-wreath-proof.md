---
rg: 2
id: clifford-rank-models-linear-sofic-wreath-proof
kind: route
title: Tensor a rank model with its transpose along the diagonal lamps and bound Sylvester kernels
target: clifford-skew-ring-rank-models-give-linear-sofic-wreath
requires:
  - linear-sofic-group-algebra-is-stably-finite
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

The proofs are Propositions 3.1–3.3 of the artifact.

- **Doubling.**
  - The two anticommutation signs cancel in `c_x c_y tensor (c_y c_x)^op`.
  - Conjugation in `A^op` by `(u_(g^-1))^op` sends `c_x^op` to `c_(gx)^op`.
  - Distinct `v g` go to distinct basis tensors.
- **Gate.**
  - For `w = v g != 1`, `tau(w) = +- X tensor X^(-T)`, where `X` represents `sigma(c_v u_g)`.
  - `dim ker(X tensor X^(-T) -+ 1) = dim{M : XM = +- MX} <= n max_lambda g_X(lambda)`. So the rank distance is
    at least `min_lambda rho(X - lambda)`.
  - If that tends to `0`, commutators with `X` tend to `0` in rank. Injectivity of `sigma` then makes
    `c_v u_g` central, which faithfulness and nondegeneracy forbid.
  - `E_S` uses the block sum with `sigma`, where `eps -> -1`.
- **Converse.** Linear soficity gives a rank embedding of `F_3[E_S]`
  (`linear-sofic-group-algebra-is-stably-finite`). Compressing by the central idempotent `(1 - eps)/2` gives
  one of `A_S`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 16.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the doubling signs, the homomorphism `u_g tensor (u_(g^-1))^op`, and injectivity;*
- *`X tensor X^-T` acting as `M -> X M X^-1`, and the eigenspace bound;*
- *rank-central implies central, via faithfulness and nondegeneracy.*

*The group-algebra embedding used in the converse was not re-checked.*

---
rg: 2
id: stw01-problem-i-via-modular-group-algebra
kind: route
title: Settle Problem I on the full C*-algebra of the modular group
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-modular-group-algebra-quasitraces-are-traces
---

If every bounded 2-quasitrace on `C*(PSL_2(Z)) = C^3 * C^2` is a trace, then Problem I
holds. Full proof: `research/artifacts/stw01-modular-group-universal-test-2026-09-12.md`.

Outline.
1. If Problem I fails, Steps 0-3 of the reviewed three-projection argument give a type
   `II_1` AW*-factor `M`, its canonical quasitrace `tau`, a projection `q`, `beta > 0`
   and a finite-spectrum `y = sum gamma_i e_i >= 0` with
   `tau(y + beta q) != tau(y) + beta tau(q)`.
2. Take distinct `lambda_i in (0, 1)`, `a = sum lambda_i e_i` (invertible),
   `m = min lambda_i (1 - lambda_i)` and `b = m q <= a - a^2`. In `M_3(M)`, the column
   `c = (a, b^(1/2), (a - a^2 - b)^(1/2))^T` has `c* c = a`, so `r = c a^(-1) c*` is a
   projection with `f_1 r f_1 = a (+) 0 (+) 0` and `f_1 r f_2 r f_1 = b (+) 0 (+) 0`.
3. With `g(0) = 0` and `g(lambda_i) = gamma_i`, the defect lives in
   `C*(1, f_1, f_2, f_3, r)`, a quotient of `C^3 * C^2`. A 3-quasitrace extension on
   `M_3(M)` (Blackadar–Handelman) restricts to this subalgebra and pulls back to a
   non-linear bounded 2-quasitrace on `C^3 * C^2`.

The converse is trivial, so the route is an equivalence.

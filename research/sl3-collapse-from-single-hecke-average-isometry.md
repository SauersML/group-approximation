---
rg: 2
id: sl3-collapse-from-single-hecke-average-isometry
kind: route
title: Strict convexity and expanding generation upgrade one norm equality to the full collapse
target: sl3-pair-relative-commutant-route
requires:
  - hecke-averaging-realizes-commutant-expectation
  - single-hecke-average-isometry-for-lambda-central-unitaries
---

Let `M` be a tracial matrix ultraproduct, `pi` a trace-preserving
regular-trace representation of `Gamma = SL_3(Z[1/2])`, and `k` a
unitary of `pi(Lambda)' cap M`, `Lambda = SL_3(Z)`.  By
`single-hecke-average-isometry-for-lambda-central-unitaries` (at
`n = 3`, `p = 2`, `gamma_0 = h = diag(2, 1, 1/2)`),
`|| S(k) ||_2 = 1`.

`S(k)` is the convex combination `(1/2) k + (1/(2L)) sum_i pi(w_i) k
pi(w_i)^*` of `L + 1` unit vectors of the Hilbert space `L^2(M)`.  A
convex combination of unit vectors has norm one only if all of them
coincide (strict convexity: expand `|| sum a_i v_i ||^2 = 1` against
`sum a_i || v_i ||^2 = 1` to get `sum_(i<j) a_i a_j || v_i - v_j ||^2
= 0`).  Hence `pi(w_i) k pi(w_i)^* = k` for every `i`; writing
`w_1 = lambda h lambda'` with `lambda, lambda' in Lambda` and using
`Lambda`-centrality twice, `k` commutes with `pi(h)`.  Since
`Gamma = < Lambda, h >` (the expanding-conjugation generation recorded
in `sl3-pair-relative-commutant-route`), `k` commutes with
`pi(Gamma)`, i.e. `k in pi(Gamma)' cap M`.  Unitaries span, so
`pi(Lambda)' cap M subseteq pi(Gamma)' cap M`; the reverse inclusion
is automatic.  This is `(RC3)`, the statement of the target.

The role of `hecke-averaging-realizes-commutant-expectation` is to
certify that the isometry claim is the RIGHT single inequality: by its
contraction `(HA3)`, any failure `|| S(k) ||_2 < 1` propagates to
`|| E(k) ||_2 < 1` with geometric iterates, so the isometry claim is
equivalent to (not just sufficient for) the collapse, and a
quantitative attack on it may assume the explicit decay rate
`delta_0(3, 2)` from the start.

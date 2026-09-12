---
rg: 2
id: stw01-problem-i-via-full-free-group-host
kind: route
title: Settle Problem I on its universal test algebra C*(F_2)
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-full-free-group-algebra-quasitraces-are-traces
---

If every bounded 2-quasitrace on `C*(F_2)` is a trace, then every bounded
2-quasitrace on every unital C*-algebra is a trace. The proof is Theorem 3.1,
`(2 => 1)`, of `research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`:

1. Let `sigma` be a bounded 2-quasitrace on a unital `A` that is not a trace.
   There are self-adjoint `a, b` with `sigma(a+b) != sigma(a) + sigma(b)`.
2. Quasitraces are real homogeneous on self-adjoint elements, so scale `a, b` to
   norm `< 1`. Put `u = exp(ia)` and `v = exp(ib)`. Their spectra lie in an arc on
   which `log` is continuous, so `a, b` lie in `B = C*(u, v)`.
3. Restricting the `M_2(A)`-extension of `sigma` to `M_2(B)` shows that
   `sigma|_B` is a bounded 2-quasitrace, and it is still non-additive at `a, b`.
4. Let `pi: C*(F_2) -> B` send the canonical unitaries to `u, v`. It is
   surjective. Then `sigma o pi` is a bounded 2-quasitrace on `C*(F_2)`. At
   self-adjoint lifts `a', b'` it satisfies
   `sigma(pi(a'+b')) != sigma(pi(a')) + sigma(pi(b'))`.

This contradicts the prerequisite. Conversely Problem I implies the prerequisite,
so the route is an equivalence, not a weakening.

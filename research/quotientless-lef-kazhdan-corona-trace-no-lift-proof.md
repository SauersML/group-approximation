---
rg: 2
id: quotientless-lef-kazhdan-corona-trace-no-lift-proof
kind: route
title: "A ucp lift of a trace-realizing corona map makes the canonical trace quasidiagonal, which for Kazhdan groups means residually finite"
target: quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift
requires:
  - lef-group-canonical-trace-is-a-corona-trace
  - kazhdan-trace-amenable-iff-qd-iff-fd-limit
  - lef-kazhdan-group-without-finite-quotients-exists
---

Let (φ_k) be a ucp lift of Φ. Since Φ is multiplicative, φ_k(ab) − φ_k(a)φ_k(b) represents 0 in Q_d, so
it is norm-null. Also lim_ω tr∘φ_k(a) = tr_ω Φ(a) = τ_G(a). C*_max(G) is separable, so choose indices
k_1 < k_2 < … with |tr φ_{k_m}(a_i) − τ_G(a_i)| < 1/m for i ≤ m on a countable dense set (a_i). By
contractivity, tr∘φ_{k_m} → τ_G weak*. So τ_G is quasidiagonal, and
`kazhdan-trace-amenable-iff-qd-iff-fd-limit` makes G residually finite.

For the witnesses: `lef-kazhdan-group-without-finite-quotients-exists` gives an infinite Kazhdan LEF G with
no finite quotients, which is therefore not RF. `lef-group-canonical-trace-is-a-corona-trace` realizes τ_G
in the corona, so no realizing map lifts. S = G/Z(G) is infinite, simple, Kazhdan and LEF (Pestov
artifact §3.3), and the same argument applies. ∎

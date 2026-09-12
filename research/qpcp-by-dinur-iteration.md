---
rg: 2
id: qpcp-by-dinur-iteration
kind: route
title: Alternate BMVZ amplification with an amplifier-independent locality reduction for logarithmically many rounds
target: quantum-pcp-constant-gap-local-hamiltonian
requires: [bmvz-iterable-tensor-gap-amplification, locality-reduction-with-amplifier-independent-loss]
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
---

## Why sufficient

Take `k_0,g_0,omega_0,c`, and for each `t` the constants `S_t,A_t`, from
`locality-reduction-with-amplifier-independent-loss`. Put
`eta_0=1/(20 max{1+C_mu, omega_0})`. Fix `t>=3` satisfying the side conditions
of BMVZ (6.62)-(6.66) and (7.6), and with `c eta_0 sqrt(t/log t)>=2`.

Start from the QMA-complete layered family of BMVZ Corollary 8.4, which lies in
`L(5,36,70)` and hence in `L(k_0,g_0,omega_0)`. Its YES energy is at most
`2^(-p(n))` and its NO energy at least `1/q(n)`. Iterate
`H_(i+1)=RED_t(H_i^(2t))`. Amplification keeps the layer count and
`omega_min` (BMVZ Section 7), and RED keeps the class.

- **NO side.** `lambda_min(H_(i+1))>=c min[(1/3)log t/t, eta_0 sqrt(t/log t) lambda_min(H_i)]>=min[gamma_t, 2 lambda_min(H_i)]`,
  where `gamma_t=c log t/(3t)`. After `l=O(log n)` rounds, `lambda_min>=gamma_t`.
- **YES side.** Proposition 4.1 and (RED2) give
  `lambda_min(H_(i+1))<=2t A_t lambda_min(H_i)+2^(-N_i)`. After `l` rounds this
  is at most `(2tA_t)^l(2^(-p(n))+l 2^(-n))`, which is negligible, since
  `(2tA_t)^l=poly(n)` for fixed `t`.
- **Size.** Qubits multiply by at most `2t S_t` per round and clauses by at most
  `d^(2t) S_t`, so `O(log n)` rounds stay polynomial.
- **Form.** Repeating clauses in proportion to the rational layer weights gives
  the uniform average form (QPCP1). Projections satisfy `0<=h<=I`.

So it is QMA-hard to decide `lambda_min<=negl(n)` versus `lambda_min>=gamma_t`
at constant locality `k_0` on qubits. That is the target. The computation is
written out in Section 3 of the linked artifact.

## Status

This route factors the problem honestly. Its first prerequisite is proved in
the literature, and its second is a statement about one map, not a restatement
of the target. Unlike `qpcp-from-anchored-amplifier`, no instance transformation
satisfies the reducer claim trivially: the positive shift does not change
locality, and the factor unfolding satisfies RED2 but loses `sqrt(log t/t)` in
RED1.

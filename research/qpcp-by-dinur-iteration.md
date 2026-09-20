---
rg: 2
id: qpcp-by-dinur-iteration
kind: route
title: Alternate BMVZ amplification with an amplifier-independent locality reduction for logarithmically many rounds
target: quantum-pcp-constant-gap-local-hamiltonian
requires: [bmvz-iterable-tensor-gap-amplification, locality-reduction-with-amplifier-independent-loss]
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
---

## Why sufficient

Take `k_0,g_0,omega_0,c`, and for each `t` the constants `S_t,A_t`, from
`locality-reduction-with-amplifier-independent-loss`. Put
`eta_0=1/(20 max{1+C_mu, omega_0})`. Fix `t>=3` satisfying the side conditions
of BMVZ (6.62)-(6.66) and (7.6), and with `c eta_0 sqrt(t/log t)>=2`.

Start from the QMA-complete layered family of BMVZ Corollary 8.4, which lies in
`L(5,36,70)` and hence in `L(k_0,g_0,omega_0)`. Its YES energy is at most
`2^(-p(n))` (choose `p(n)>=n` by witness amplification) and its NO energy
at least `1/q(n)`. Pad to at least `n` qubits; the reducer never decreases
site count. Iterate
`H_(i+1)=RED_t(H_i^(2t))`. Amplification keeps the layer count and
`omega_min` (BMVZ Section 7), and RED keeps the class.

- **NO side.** `lambda_min(H_(i+1))>=c min[(1/3)log t/t, eta_0 sqrt(t/log t) lambda_min(H_i)]>=min[gamma_t, 2 lambda_min(H_i)]`,
  where `gamma_t=c log t/(3t)`. After `l=O(log n)` rounds, `lambda_min>=gamma_t`.
- **YES side.** Proposition 4.1 and (RED2) give
  `lambda_min(H_(i+1))<=2t A_t lambda_min(H_i)+2^(-N_i)`. After `l` rounds this
  is at most `(2tA_t)^l(2^(-p(n))+l 2^(-n))`, which is negligible, since
  `(2tA_t)^l=poly(n)` for fixed `t`.
- **Size.** Qubits multiply by at most `2t S_t` per round and clauses by at most
  `d^(2t) S_t`. The reducer's linear bound on maximum bit length, including
  layer weights, puts the entire description vector under one fixed linear
  recurrence. Thus `O(log n)` rounds stay polynomial in size and time.
- **Form.** At the final constant-gap stage, round the full term probability
  vector to denominator `D>=8M/gamma_t`, where `M` is the final term count.
  Largest-remainder rounding changes each weight by at most `1/D`, hence
  the Hamiltonian by operator norm at most `M/D<=gamma_t/8`. Repetition
  according to these integer counts gives (QPCP1) with polynomial size.
  Polynomial-bit rational weights alone do not justify exact denominator
  clearing. Projections satisfy `0<=h<=I`.

After rounding, it is QMA-hard to decide `lambda_min<=gamma_t/4` versus
`lambda_min>=7 gamma_t/8` for sufficiently large inputs
at constant locality `k_0` on qubits. That is the target. The computation is
written out in Section 3 of the linked artifact.

## Status

This route factors the problem honestly. Its first prerequisite is proved in
the literature, and its second is a statement about one map, not a restatement
of the target. Unlike `qpcp-from-anchored-amplifier`, no instance transformation
satisfies the reducer claim trivially: the positive shift does not change
locality, and the factor unfolding satisfies RED2 but loses `sqrt(log t/t)` in
RED1.

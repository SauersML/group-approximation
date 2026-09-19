---
rg: 2
id: fpbs-soft-collapse-kills-stationary-set-gap-proofs-proof
kind: route
title: Uniqueness in the collapse family plus recurrence along the independent set
target: fpbs-soft-collapse-kills-stationary-set-gap-proofs
requires:
  - fpbs-stationary-set-recurrence-separates
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-soft-collapse-kills-relative-gap-proofs
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

Section 5 of the artifact.

1. By `fpbs-soft-collapse-iff-invariant-sparse-spines`, spines give a
   `Gamma`-invariant family with (S1)--(S4). By (S4), `omega_t` has exactly one
   infinite cluster a.s. for `t > p_c`.
2. By invariance, `P(x in C_inf)` is the same for all `x`, and it is positive
   because some `x` lies in `C_inf`. So `theta(t) > 0`.
3. `A` is independent of `omega_t`. So `fpbs-stationary-set-recurrence-separates`
   applies to the invariant law of `omega_t`, giving `V = infinity` on
   `{e in C_inf}`.
4. The family agrees with Bernoulli for `t <= p_c` (S2), so inputs of type (a)
   and (b) cannot tell the two apart. The list of spine pairs is that of
   `fpbs-soft-collapse-kills-relative-gap-proofs`.

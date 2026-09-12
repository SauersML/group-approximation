---
rg: 2
id: leavitt-visible-cyclic-corner-is-full-on-some-host
kind: claim
title: On some finite-field Leavitt host the cyclic averaging idempotent is full in the Leavitt-visible factor
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the single host q = 3 with d = m = 2; this asks for any prime power q, arity d and admissible cycle length m, and every solution of that claim is a solution of this one.
  projective-ternary-swap-idempotent-is-full: that is the corner equation on the trivial-character factor F_3[PG], where the Leavitt evaluation vanishes; this is the corner equation on the Leavitt-visible factor of any host.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

**OPEN.** Exhibit:
- a prime power `q = p^r`;
- an arity `d >= 2`;
- an admissible cycle length `m = 1 + j(d-1)`, `j >= 1`, with `p` not dividing `m`;
- elements `b', c'` of the Leavitt-visible factor `A_iota` of `F_q[L_(F_q)(1,d)^x]` with

      c' e_H b' = eps_iota,   e_H = eps_iota (1/m) sum_k [g^k],

  where `g` is the `m`-cycle permutation unit of an `m`-ary Leavitt family.

When `m` divides `q - 1`, this is a unital `m`-pair Cohn family in the corner `T = e_H A_iota e_H`
(`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`).

## Attempts

- **The image equation holds on every host.** `b = sum_i s_i` and `c = (1/m) sum_i t_i` satisfy
  `c . pi(e_H) . b = 1` in the Leavitt algebra. The lift to `A_iota` is open. Direct finiteness does
  not pass to quotients (`direct-finiteness-not-inherited-by-quotients`), so the image solution alone
  transports nothing. This is where it dies today.
- **Monotone in the field.** A solution over `F_q` gives one over every `F_(q^r)` with the same
  `(d, m)`: multiply by the refined central idempotent (Proposition 4 of the artifact). So work in the
  colimit over finite fields. A finitely supported solution there lives over one finite field.
- **The gate.** If `L_(F_q)(1,d)^x` is `F_q`-linear sofic, then `F_q[G]` is stably finite
  (`linear-sofic-group-algebra-is-stably-finite`) and this host dies. Property (T) gives no rank
  rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`), so the
  gate is not settled that way.
- **What stays silent under the twist.** Augmentation, commutative quotients and the lifted trace. The
  lifted trace forbids `e_H ~ eps_iota` but not `1 <= e_H`.

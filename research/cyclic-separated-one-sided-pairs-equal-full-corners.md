---
rg: 2
id: cyclic-separated-one-sided-pairs-equal-full-corners
kind: claim
title: A one-sided pair whose cyclic cross terms vanish makes the cyclic averaging idempotent full, and under the twist the converse holds
distinct_from:
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is the open existence claim at q = 3 for the swap, with its idempotent and cross-term forms; this is the established equivalence on every finite-field Leavitt host and for every admissible cycle length, and its sufficiency direction needs no twist.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Let `A_iota`, `m`, `g` and `e_H = eps_iota (1/m) sum_k [g^k]` be as in
`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`, over `F_q` with `p` not dividing `m`.

1. **Sufficiency, on every host.** If `a, c` in `A_iota` satisfy

       c a = eps_iota   and   c [g^i] a = 0   for 0 < i < m,

   then `(m c) e_H a = eps_iota`, so `e_H` is full in `A_iota`.
2. **Converse under the twist.** Suppose `m` divides `q - 1`, `zeta` has order `m`, and
   `delta = sum_i zeta^i s_i t_i`. If `c' e_H b' = eps_iota`, then

       a = sum_(j=0)^(m-1) [delta]^j e_H b',   c = (1/m) sum_(j=0)^(m-1) c' e_H [delta]^(-j)

   satisfy `c a = eps_iota` and `c [g^i] a = 0` for `0 < i < m`.

At `q = 3` and `m = 2` this is the equivalence (C) iff (P) of
`ternary-twisted-algebra-has-swap-separated-one-sided-pair`.

ESTABLISHED by `cyclic-separated-pairs-proof` (Section 7 of the artifact).

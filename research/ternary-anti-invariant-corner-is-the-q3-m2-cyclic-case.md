---
rg: 2
id: ternary-anti-invariant-corner-is-the-q3-m2-cyclic-case
kind: route
title: The ternary anti-central swap corner is the cyclic corner problem at q = 3, d = m = 2
target: leavitt-visible-cyclic-corner-is-full-on-some-host
requires:
  - ternary-anti-invariant-swap-corner-is-full
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

For `(q, d, m) = (3, 2, 2)`:
- the identity character of `F_3^x = {1, -1}` gives `eps_iota = 2(1 - [z]) = eps_-`;
- the 2-cycle permutation unit is `g = s1 t0 + s0 t1 = w`;
- the averaging idempotent is `e_H = eps_- . 2(1 + [w]) = e_-`.

So a solution `c e_- b = eps_-` of the ternary claim is literally a solution of the cyclic corner
problem on that host.

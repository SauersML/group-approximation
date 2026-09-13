---
rg: 2
id: burau-kernel-avoids-short-point-pushing-braids-proof
kind: route
title: "Exhaustive meet-in-the-middle search: no Burau kernel word in K_4 of free length at most 24"
target: burau-kernel-avoids-short-point-pushing-braids
requires: []
artifacts:
  - research/artifacts/zp-burau-k4-kernel-search-2026-09-13.md
  - research/artifacts/zp-burau-k4-kernel-search-2026-09-13.py
---

Direct proof by finite computation.

1. **Splitting.** A nontrivial reduced kernel word `w` with `|w| <= 24`
   splits as `w = u v^{-1}`, with `u` and `v` reduced of length `<= 12`,
   `u != v`, and `rho_4(u) = rho_4(v)`.
2. **Enumeration.** The script enumerates all 366,210,937 reduced words of
   length `<= 12` in `A_{14}^{±1}, A_{24}^{±1}, A_{34}^{±1}` and evaluates
   `rho_4` at `t = 123456789` modulo the prime `1000000007`. The evaluation
   is a ring homomorphism, so exact equality forces equal evaluations.
3. **Keys.** It keys each evaluated matrix by a deterministic 64-bit linear
   form and finds no two equal keys. Hence no exactly equal pair `u != v`
   exists.
4. **Controls.** The counts match `1 + 6(5^12 - 1)/4`. A control with free
   letters `sigma_i^{±1}` reports 56 collisions, all confirmed as exact
   kernel words by the `Z[t, t^{-1}]` checker.

Run record, overflow bound and reproduction command:
`research/artifacts/zp-burau-k4-kernel-search-2026-09-13.md`. Machine
computation; a second lane has not re-run it.

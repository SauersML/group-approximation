---
rg: 2
id: mixed-root-two-packet-radius-four-has-no-solution
kind: claim
title: Independent mixed elementary-root conjugators through length four do not solve the two-packet equation
distinct_from:
  inverse-packet-conjugator-must-mix-s-and-t-charts: that gives an unbounded pure-chart obstruction under the specialization y=x inverse; this exhausts two independent genuinely mixed conjugators in one explicitly bounded eight-root family.
  two-packet-solutions-have-odd-intersection: that gives a global necessary parity condition but does not evaluate the remaining pairs; this uses that condition to complete a finite exhaustion through word length four.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/filter_two_packet_len4.py
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Use the eight elementary root involutions

```text
U_(s_0), L_(s_0), U_(s_1), L_(s_1),
U_(t_0), L_(t_0), U_(t_1), L_(t_1).
```

Among the elements represented by words of length at most four, exact Bergman
reduction gives 1,254 distinct nonidentity elements whose recorded reduced
word contains both an `s`-root and a `t`-root.  None of the 1,572,516 ordered
independent pairs `(x,y)` solves

```text
A P_y + P_x B + P_x P_y = Delta.
```

The odd-intersection theorem leaves only 1,394 pairs for full evaluation.
At length at most three, 204 candidates give 41,616 pairs, 208 parity
survivors, and again no solution.

This is a complete result only for the stated bounded generating family.  It
does not exclude longer words or arbitrary elements of `G`.

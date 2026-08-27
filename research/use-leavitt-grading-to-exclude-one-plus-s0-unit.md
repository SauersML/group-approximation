---
rg: 2
id: use-leavitt-grading-to-exclude-one-plus-s0-unit
kind: route
title: Use the highest homogeneous component to exclude an inverse for one plus s0
target: bare-one-hecke-letter-cannot-lift-s0
requires:
  - leavitt-corner-idempotent-unital-surjection
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

Evaluation sends the corner identity to one and a literal group element to
its unit, so the proposed equality forces `y=1+s_0`.  In the standard
integer grading, if the top degree `n` is nonnegative then `s_0b_n` is an
uncancelled nonzero degree `n+1` term.  If `n` is negative, the bottom term
`b_m` is an uncancelled negative-degree term.  This excludes a right inverse.

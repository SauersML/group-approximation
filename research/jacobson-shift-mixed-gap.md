---
rg: 2
id: jacobson-shift-mixed-gap
kind: claim
title: The recursive Jacobson stable-letter presentation has a positive marked matrix gap
distinct_from:
  jacobson-boundary-amalgam-mixed-gap: that asks for a gap in the smaller Xi presentation without a stable letter; this asks for a gap after imposing full boundary packets and exact finite-packet intertwining by the stable letter.
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
---

Prove `gamma_shift>0` for the exact variational problem in
`jacobson-shift-gap-characterizes-mark-collapse`.

The quantifier ranges over every positive matrix dimension and
every complex unitary representation type of the full finite
packets `B,C`, with exact agreement on their entire intersection,
the head mark retained, and the stable letter exactly intertwining
the two specified copies of `F`. The required common positive
lower bound concerns the maximum of the old braid error, the old
TS error, and the remaining stable-letter error involving `h`.

## Attempts

- Exact recursion is established in the new finitely presented
  group, and its head mark survives in an explicit bilateral linear
  action. Neither statement gives a uniform unitary matrix gap.
- Finite-group averaging removes every stable-letter error on `F`
  while retaining the original dimension and changing only the
  remaining `h` error by a controlled amount. The three mixed
  errors in the variational problem remain open.
- Compatible regular representations satisfy the finite-packet
  overlap and the finite intertwining constraint. Character and
  fixed-space data alone do not settle the remaining mixed words.
- The earlier affine-cell countermodel concerns a selected subset
  of the old recursive equations. It neither realizes these new
  stable-letter relations nor refutes this positivity claim.

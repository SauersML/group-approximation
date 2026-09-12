---
rg: 2
id: binary-jacobson-mf-implies-order-two-universal-mf
kind: claim
title: MF of the binary Jacobson elementary group would force MF of the universal order-two one
distinct_from:
  order-two-defect-question-reduces-to-one-universal-ring: that is the equivalence between the class question and the single universal ring; this compares the universal ring with the binary Jacobson ring and is a one-directional implication only.
  order-two-universal-ring-has-finitary-symbol-sequence: that is the structural description of the universal ring; this is the group-level consequence of its fibre-product embedding.
  binary-jacobson-mark-dichotomy-holds-from-rank-two: that is the two-valued alternative for the binary Jacobson group alone; this transports one side of that alternative to a different group.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  For every `n >= 2`, entrywise application of the
injection `(OT3)` embeds

```text
EL_n(A_2)  -->  EL_n(J_(F_2)) x EL_n(Z[z,z^(-1)]).                (CMP1)
```

Consequently

```text
EL_n(J_(F_2)) is MF  ==>  EL_n(A_2) is MF,                        (CMP2)
```

equivalently: proving `EL_n(A_2)` non-MF would also settle the binary
Jacobson case at that rank.

**The reverse implication is not proved.**  The quotient map
`A_2 -> J_(F_2)` cannot supply it: MF is not assumed or known to pass to
arbitrary quotients.  Nor is there a ring-embedding shortcut in the
reverse direction — `order-two-universal-ring-has-no-infinite-corner`
rules out any ring embedding of `J_(F_2)` into `A_2` or a finite
amplification of it.

So the universal order-two problem is at least as hard as the binary
Jacobson problem, and the two are not known to be the same problem.  This
is the precise sense in which the additive-order-two question is not
merely the binary Jacobson question restated.

DERIVATION
binary-jacobson-to-order-two-universal-proof

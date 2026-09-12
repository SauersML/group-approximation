---
rg: 2
id: central-coefficient-kl-failure-over-injective-quotient
kind: claim
title: Some Kervaire--Laudenbach failure over a central extension keeps the quotient adjunction injective
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

**OPEN.** There are a central extension `1 -> Z -> E -> Q -> 1` and a
nonsingular `w in E * <t>` such that `Q` injects into
`(Q * <t>)/<<w->>` but `E` does not inject into `(E * <t>)/<<w>>`.

This is the central shape of a counterexample. It refutes
`kervaire-laudenbach-nonsingular-conjecture`, and by
`central-extension-kl-schur-criterion` it forces a nonzero Schur kernel of
`w-` over `Q`. The reduction package of the root allows counterexamples to
be simple, which have no center, so this shape is not forced. It is where
equations over well-understood quotients, such as residually finite
arithmetic groups, can be tested.

## Attempts

1. **Deligne's triple cover over `Sp_4(Z)`.** By the criterion, a failure
   needs the Schur kernel of the image equation to meet the mod-three
   multiplier. That is `sp4-schur-kernel-meets-the-deligne-triple-class`,
   open. Even if that holds, only the centralized quotient is decided.
   Survival in the plain quotient still has to fail.
2. **Leavitt unit group.** It does not fit this shape. The unit group is
   perfect with trivial center, and its Kervaire--Laudenbach status is being
   decided in its own lane (`kl-violating-equation-over-leavitt-unit-group`).

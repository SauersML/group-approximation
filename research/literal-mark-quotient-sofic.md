---
rg: 2
id: literal-mark-quotient-sofic
kind: claim
title: The literal marked quotient is sofic
distinct_from:
  literal-mark-quotient-mf: That asks for operator-norm microstates of `E/<w>`; this asks for permutation microstates, and the two are not known to imply each other in either direction for this group.
  literal-group-sofic: That is soficity of `E`; soficity does not pass to quotients, so this needs its own proof — which happens to be the same block-tower argument with the central sign deleted.
  literal-telescope-core-lef: That is the LEF property of the shift-free part of `E`; this is soficity of the central quotient of the whole group.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
---

`E/<w> = (*_{i in I} (Z/2)^8) semidirect V` is sofic.

Soficity does not pass to quotients, so this does not follow from
`literal-group-sofic`; it follows from the same block-tower argument with the
Clifford blocks replaced by their central quotients `(Z/2)^8` and the
amalgamation deleted.  The finitely generated invariant lamp subgroups
`M'_J = *_{i in J} (Z/2)^8` are still free products of finitely many finite
groups, hence virtually free and residually finite, and the level still acts on
them through a finite permutation group of the `8|J|` sites.

**The dichotomy this created, and how it resolved.**  Either `E/<w>` is
residually finite — then it is MF by `lem:rfmf`, settling
`literal-mark-quotient-mf` and `literal-mf-radical-exact` — or it is not, in
which case, being sofic, it is not stable in finite actions by
`sofic-stable-implies-residually-finite`.

The second branch is the true one.  `literal-mark-quotient-finite-residual`
computes the finite residual of `E/<w>` to be the nontrivial level-collapse
kernel, and `marked-quotients-not-lef` shows `E/<w>` is not even LEF.  So both
exact-finite-model routes to `literal-mark-quotient-mf` are closed, and the
stability conclusion is `literal-mark-quotient-not-stable-in-finite-actions`.
Soficity and MF have parted company here in the sharpest available way: `E/<w>`
has permutation microstates but no exact finite local models at all.

---
rg: 2
id: two-sided-deletion-corrections-pass-natural-kernel-test
kind: claim
title: Two explicit simultaneous chart corrections have injective auxiliary natural maps
artifacts:
  - research/artifacts/kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md
---

For a=[[1,s_0],[t_0,0]], b=[[1,s_1],[t_1,0]], and
z=omega or omega^2, the binary operator

    H_z=a+m_z^-1 b m_z

is injective on the full free module of actual infinite binary
tails, over either F_2 or F_4. This is proved for every finite
support, including aperiodic and eventually periodic tail classes.

The complete exterior map of diag(H_z,b) is equivalent, by
invertible source and target changes, to the genuine candidate

    P_0[ell_z][g][n_z]f_0,
    ell_z=diag(1,z^-1), n_z=[[0,z^-1],[1,0]], g=diag(a,b).

Both ell_z and n_z belong to K=GL_2(F_4). These simultaneous
choices therefore escape the natural-kernel transfer mechanism
that excluded all right corrections with the left projector fixed.
The auxiliary H_z is not asserted to be a unit. The complete
exterior-square map for z=omega is now proved injective in
`omega-corrected-deletion-passes-full-boundary-exterior-test`;
its group-ring split is now excluded by an exact contragredient
period-two kernel in
`omega-corrected-deletion-has-contragredient-kernel`.
The z=omega^2 candidate is excluded by an exact
period-four exterior kernel, recorded in
`two-sided-omega-square-deletion-candidate-has-no-split`.

The height argument does not extend directly to the exterior
source: its highest creator layer kills (X,Y)=(omega^2 Y,Y)
for every flip-symmetric Y. The generated subgroup <K,g> also
contains an explicit Z^2, excluding a virtually-free shortcut.
Neither observation resolves direct finiteness of that subgroup.

A separate full-operator contraction proof now reduces every
possible exterior kernel to purely periodic support and proves
injectivity when both source tensors are flip-symmetric; see
`two-sided-exterior-kernels-must-be-periodic-and-asymmetric`.
The period-four witness for z=omega^2 lies in this remaining
asymmetric class. The subsequent endpoint and full-target proof
excludes every such source for z=omega. This representation
result remains valid despite the contragredient obstruction.
Neither literal simultaneous choice gives a group-ring split;
Kaplansky's conjecture remains unresolved.

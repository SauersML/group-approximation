---
rg: 2
id: two-sided-omega-square-deletion-candidate-has-no-split
kind: claim
title: The omega-square simultaneous deletion candidate has an exact exterior kernel
artifacts:
  - research/artifacts/kaplansky-two-sided-omega-square-period-four-kernel-2026-09-08.md
---

For z=omega^2, the literal simultaneous chart candidate

    T_z=P_0[ell_z][g][n_z]f_0,
    ell_z=diag(1,z^-1), n_z=[[0,z^-1],[1,0]],
    g=diag(a,b),
    a=[[1,s_0],[t_0,0]], b=[[1,s_1],[t_1,0]],

has a nonzero binary exterior source vector killed by T_z.
Consequently there is no group-ring element L satisfying
L T_z=f_0, regardless of the support of L.

The normalized full two-sector kernel is supported on the
period-four core of (0011)^infinity. Both target coordinates
cancel exactly. Frobenius descent and the inverse source
normalization give an explicit two-wedge binary witness for
the actual candidate, not just an auxiliary natural map.

The auxiliary natural map H_z remains injective. Thus natural
injectivity does not suffice for the full exterior test.
The other simultaneous choice z=omega now passes the full
boundary exterior-square test, as recorded in
`omega-corrected-deletion-passes-full-boundary-exterior-test`.
Its group-ring split is nevertheless excluded by the distinct
contragredient representation, as recorded in
`omega-corrected-deletion-has-contragredient-kernel`. Together
with the inverse-adjoint automorphism, these two certificates
exclude all four literal parameter/orientation choices.
Kaplansky's direct-finiteness conjecture remains open.

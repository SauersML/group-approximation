---
rg: 2
id: omega-corrected-deletion-passes-full-boundary-exterior-test
kind: claim
title: The omega simultaneous correction is injective on the full boundary exterior-square source
artifacts:
  - research/artifacts/kaplansky-omega-corrected-deletion-full-exterior-injectivity-2026-09-08.md
---

For the literal chart candidate

    T_omega=P_0[ell][g][n]f_0,
    ell=diag(1,omega^-1), n=[[0,omega^-1],[1,0]],
    g=diag(a,b),
    a=[[1,s_0],[t_0,0]], b=[[1,s_1],[t_1,0]],

the induced map is injective on the entire source im(f_0)
in the exterior square of the natural free binary-boundary
module. This covers every finite support, including arbitrary
mixtures of actual infinite-tail classes, and follows from an
exact proof rather than finite rank tests.

After the existing support reduction, the endpoint equations
remove every bridge and force the scalar source tensor to be
symmetric. Full target projections then leave only the primitive
011 and 00111 cores, whose residual wedges are explicitly
nonzero. Thus the normalized full source is zero, and the
invertible normalization transfers injectivity to T_omega.

This necessary representation test is now an exact positive
control for an impossible split: the different contragredient
representation has a finite period-two source kernel, proved in
`omega-corrected-deletion-has-contragredient-kernel`. Consequently
no L satisfies L T_omega=f_0. The ordinary exterior-square
injectivity above remains valid and does not establish the
corresponding assertion in other representations. Kaplansky's
direct-finiteness conjecture remains unresolved.

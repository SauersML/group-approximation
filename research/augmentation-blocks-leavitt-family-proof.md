---
rg: 2
id: augmentation-blocks-leavitt-family-proof
kind: route
title: Apply the augmentation, then rank over the rationals
target: augmentation-blocks-unital-leavitt-family
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

*Scalar case.*  Let `eps : R -> Z` be a unital ring homomorphism and suppose
`t_i s_j = delta_{ij}`.  Put `a_i = eps(s_i)`, `b_i = eps(t_i)` in `Z`.  From
`t_0 s_0 = 1`, `b_0 a_0 = 1`, so `a_0` and `b_0` are units of `Z`, in
particular nonzero.  From `t_0 s_1 = 0`, `b_0 a_1 = 0`, and `Z` is a domain,
so `a_1 = 0`.  But `t_1 s_1 = 1` gives `b_1 a_1 = 1`, a contradiction.  The
idempotent relation `s_0t_0 + s_1t_1 = 1` is never used, so the obstruction
applies to the half of the Leavitt relations that expresses `R = R (+) R`
already.  For `R = ZG` take the augmentation `sum n_g g |-> sum n_g`.

*Matrix case.*  Fix `n >= 1` and suppose `S_i, T_i` in `M_n(ZG)` satisfy the
relations.  Apply entrywise augmentation `M_n(ZG) -> M_n(Z)` and extend
scalars to `Q`.  On the finite-dimensional space `Q^n`, `T_0 S_0 = I_n`
forces `S_0` to be invertible with `T_0 = S_0^{-1}`; then `T_0 S_1 = 0` gives
`S_1 = 0`, contradicting `T_1 S_1 = I_n`.  Finite dimension is what does the
work -- this is exactly the step that fails for the Leavitt algebra, which is
its own proper matrix amplification.

Note the matrix case does not follow from the scalar case: `M_n(ZG)` carries
no unital ring homomorphism to `Z` for `n >= 2`, since it has no proper
two-sided ideals coming from such a map.  The rank argument replaces it.

---
rg: 2
id: augmentation-blocks-unital-leavitt-family
kind: claim
title: An augmentation blocks every unital binary Leavitt family
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that is the internal algebra of the Leavitt algebra itself, identifying GL with EL and proving the unit group perfect; this is a no-go saying where those relations can never be found, namely in any ring carrying a unital homomorphism to Z.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
  - GroupApproximation/KOne/ClassicalKOne.lean
---

Call `s_0, s_1, t_0, t_1` in a unital ring `R` a **binary Leavitt family** if

    t_i s_j = delta_{ij},        s_0 t_0 + s_1 t_1 = 1.

These relations are the module self-similarity `R = R (+) R` that powers the
Leavitt `K_1` swindle.

**Claim.**  If `R` admits a unital ring homomorphism `eps : R -> Z`, then `R`
contains no binary Leavitt family.  In particular no integral group ring
`ZG` contains one, via the augmentation.  Moreover, for every group `G` and
every finite `n >= 1`, `M_n(ZG)` contains no unital binary Leavitt family
either.

Both halves are two lines (audit Section D); the first does not even use the
idempotent relation, and the second runs entrywise augmentation into `M_n(Q)`
where `T_0 S_0 = I_n` forces `T_0 = S_0^{-1}` and then `T_0 S_1 = 0` forces
`S_1 = 0`.

## What it rules out

This is the precise reason the repository's `K_1(L_k(1,2)) = 0` -- a real
theorem, kernel-checked over every field
(`leavitt-gl-equals-el-and-perfect-unit-group`) -- cannot be moved to
`K_1(ZG)` by locating Leavitt generators in `ZG` or in a finite matrix ring
over it.  The transfer is not merely unproved; the defining relations are
unavailable in the target at every finite rank.  Any future attempt in this
direction must state at the outset which of the two hypotheses it drops.

**The one loophole, stated honestly.**  A *nonunital* family in a corner
`p M_n(ZG) p` whose augmented idempotent has rank zero is not excluded by the
argument above.  Exhibiting a nonzero such corner is itself a hard statement
about rank-zero projective modules and idempotents over `ZG`, in the same
`K`-theoretic landscape as the target, so the loophole is not a shortcut.
Nothing in this repository supplies one.

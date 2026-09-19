---
rg: 2
id: commuting-lamp-quotient-finite-residual
kind: claim
title: Exact finite residual of the commuting-lamp quotient
distinct_from:
  marked-quotients-not-lef: That claim rules out exact finite models qualitatively; this one computes the finite residual exactly and identifies the residually finite part.
  commuting-lamp-quotient-structure: That claim identifies the group and its site set; this one computes one invariant of that group.
  commuting-lamp-quotient-mf: That is the open operator-norm question; this is a proved statement about finite quotients, which by itself decides nothing about MF.
  corona-hs-radical-is-finite-residual: That claim computes the corona trace-invisible set and only then observes it coincides with this one; the two are proved by different arguments and the coincidence is the content.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

The finite residual of `W/<zeta> = F_2[X] semidirect V` is exactly

```text
L_0 = { lamp configurations with an even number of lamps on each level },
```

the kernel of the level-parity map `F_2[X] -> sum_{n in Z} F_2`.  The
quotient `(W/<zeta>)/L_0 = (sum_{n in Z} F_2) semidirect V`, with `V` acting
through its level homomorphism, is residually finite, hence LEF, hence MF.

So the entire failure of residual finiteness is a locally finite elementary
abelian `2`-group inside the lamp kernel, and the surviving defect `ubar`
lies in it.

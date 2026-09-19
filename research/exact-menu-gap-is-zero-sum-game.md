---
rg: 2
id: exact-menu-gap-is-zero-sum-game
kind: claim
title: Finite exact-relator soundness margin is the value of a zero-sum profile game
---

Let `P` be a finite family of marked bad profile cells and `E` a finite menu of
relators all satisfied exactly by one tracial witness.  Put

```text
R_(p,r)=1  if profile p rejects relator r at the enlarged threshold,
R_(p,r)=0  otherwise.
```

The largest worst-profile rejection margin obtainable by reweighting the exact
relators is

```text
gamma* = max_(mu in Delta(E)) min_(p in P) sum_r mu_r R_(p,r).
```

By finite minimax / linear-programming duality,

```text
gamma* = min_(lambda in Delta(P)) max_(r in E)
         sum_p lambda_p R_(p,r).
```

Thus a primal distribution `mu` is a constructive soundness certificate, while
a dual distribution `lambda` is a quantitative obstruction showing that every
single exact relator rejects only limited mass of a hard mixture of profiles.
In particular `gamma*>0` exactly when every bad profile is rejected by at least
one exact relator.

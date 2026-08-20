---
rg: 2
id: four-child-three-context-exits-preserve-carrier
kind: claim
title: Four recurrence children pay for three contextual exits and preserve one active copy
distinct_from:
  branching-plus-first-hit-exits-forces-hs-floor: that uses two children and at most one exit copy; this batches two binary steps and permits all three rank-one contextual failures to exit.
  robust-rank-one-endpoint-marginal-floor: that lower-bounds the total of three failure masses; this is the scalar branching ledger which absorbs all three.
  mixed-cnot-allowed-active-return: that tries to return the nonlinear complement of one selected exit; this avoids forming that complement at all.
---

Let `q_n,r_n>=0` and suppose one batched recurrence step satisfies

```text
4q_n <= q_(n+1)+r_n+delta_n,                           (FCE1)
r_n  <= 3q_n+zeta_n,                                   (FCE2)
r_n  >= eta q_n-epsilon_n,                             (FCE3)
sum_(n<N) r_n <= C.                                    (FCE4)
```

Here the four source copies are the grandchildren of two binary recurrence
steps, the three context failure spaces occupy three distinct grandchildren,
and the fourth is the active reserve.  Then

```text
q_(n+1) >= q_n-delta_n-zeta_n,                         (FCE5)
```

and hence

```text
eta N q_0
 <= C
  +eta sum_(j<N)(N-1-j)(delta_j+zeta_j)
  +sum_(n<N) epsilon_n.                                (FCE6)
```

If the errors have polynomial fixed-word bounds times `sqrt(E)`, marked
separation gives `q_0>=q_*>0`, and `N>C/(eta q_*)` is fixed, then `(FCE6)`
forces a dimension-independent positive lower bound on the global normalized
HS energy `E`.

For three endpoint laws of common carrier mass `s_n<=q_n`, each contextual
failure mass is at most `s_n`, so their sum automatically obeys `(FCE2)` with
`zeta_n=0`.  The robust rank-one endpoint floor gives `(FCE3)` once the BCS
gap gives `s_n>=eta q_n` up to local error.  Thus no context has to be chosen
as the unique exit and no nonlinear active complement has to be recognized.

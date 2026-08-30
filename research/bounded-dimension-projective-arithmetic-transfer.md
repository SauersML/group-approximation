---
rg: 2
id: bounded-dimension-projective-arithmetic-transfer
kind: claim
title: Projective arithmetic commutant transfer holds uniformly in every bounded matrix dimension
distinct_from:
  projective-commutant-transfer-for-arithmetic-pair: that requires one modulus uniform over all matrix dimensions; this supplies a modulus after fixing an arbitrary finite dimension cap.
  exact-projective-arithmetic-tuples-obey-transfer: that permits every dimension but assumes scalar relators; this permits genuinely nonscalar relator errors but fixes the dimension cap.
---

Fix one of the arithmetic pairs, presentation, subgroup generating set `S`,
and target word `h` from
`projective-commutant-transfer-for-arithmetic-pair`.  Let `K_0` be the
constant in the established exact-representation transfer theorem.  For
every integer `D>=1` there is a modulus

```text
eta_D(delta) -> 0  as delta -> 0                     (BDP1)
```

such that every presentation tuple `rho` in `U(d)`, `d<=D`, of max-relator
normalized-Hilbert--Schmidt defect at most `delta`, and every `U in U(d)`,
satisfy

```text
e(U,rho(h))
 <= K_0 sum_(c in S)e(U,rho(c)) + eta_D(delta).        (BDP2)
```

In particular every counterexample sequence to dimension-free projective
commutant transfer has matrix dimensions tending to infinity after passage
to a subsequence.

## Proof

For each `d<=D`, the space consisting of one unitary for every presentation
generator together with the witness `U` is compact.  Define `eta_D(delta)`
as the maximum, over the finite union of these compact spaces and over
tuples with relator defect at most `delta`, of

```text
( e(U,rho(h))-K_0 sum_(c in S)e(U,rho(c)) )_+.         (BDP3)
```

The maximum exists.  If `(BDP1)` failed, there would be
`delta_j->0`, one fixed `d<=D` after taking a subsequence, and convergent
tuples whose values in `(BDP3)` stay bounded below.  Their limit has every
defining relator equal to the identity, hence is an honest
`d`-dimensional representation of the presented group.  Continuity of word
evaluation and normalized trace would give the same positive violation at
the limit, contradicting the exact transfer theorem.  Therefore
`eta_D(delta)->0`, proving `(BDP2)`.

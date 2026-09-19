---
rg: 2
id: orthogonal-checksum-controls-only-mass-weighted-syndromes
kind: claim
title: One orthogonal checksum controls only mass-weighted first-hit syndromes
distinct_from:
  self-similar-square-function-checksum-compiler: that asks in addition for a contractive carrier-return recurrence; this isolates what Pythagoras alone proves and why that recurrence is load-bearing.
  branching-plus-first-hit-exits-forces-hs-floor: that assumes the required branching ledger and derives a floor; this shows orthogonality without the ledger is insufficient.
  dyadic-parity-checksum-has-finite-pauli-gauge: that gives a finite algebraic gauge countermodel to parity returns; this is a general normalized-HS trace-budget limitation on authenticated blocks.
---

ESTABLISHED.

Let `W in U(d)` and let `(P_n)` be pairwise orthogonal projections.  Put

```text
s_n=||(W-I)P_n||_(2,d),
mu_n=tr_d(P_n),
e_n=s_n^2/mu_n  (mu_n>0).                                (OCS1)
```

Then

```text
sum_n s_n^2 <= ||W-I||_(2,d)^2,
sum_n mu_n e_n <= ||W-I||_(2,d)^2.                       (OCS2)
```

This is exactly Pythagoras, because the operators `(W-I)P_n` have
orthogonal initial spaces.  It is the strongest conclusion available from
orthogonal authentication alone.  In particular `(OCS2)` gives no bound on
`sup_n e_n`: a maximal conditional syndrome `e_N=4` on a block of mass
`mu_N=epsilon` costs only `4epsilon` of squared normalized-HS defect.

Spectator amplification makes the obstruction exact.  Direct-sum a fixed
bad block with arbitrarily many blocks on which `W=I`; the conditional error
on the bad block is unchanged while both `mu_N` and its contribution to the
global word defect tend to zero.  The same construction applies when the
`P_n` are perfectly authenticated by a finite diagonal selector packet.

Therefore a one-word first-hit compiler needs more than orthogonal decoded
blocks.  It must tie every syndrome block to a common positive-mass marked
reservoir through a contractive return such as

```text
a_n <= lambda a_(n+1)+C s_n,       lambda<1,              (OCS3)
```

or prove a uniform lower bound on the total mass of the bad blocks.  Without
that same-reservoir statement, a late challenge is still hidden in a tiny
authenticated tail.  This pinpoints why Pythagoras is the energy ledger but
not the actuator in `self-similar-square-function-checksum-compiler`.

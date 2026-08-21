---
rg: 2
id: exact-first-hit-ladder-kills-regular-carrier
kind: claim
title: An exact positive-density first-hit ladder kills its carrier in the regular trace
invalidates:
  - tagged-s3-survivor-via-central-successor-corner
  - tagged-s3-survivor-via-context-atom-bridges
  - fanizza-one-sided-pulse-decoder-proof
distinct_from:
  trace-functorial-bcs-signal-groupification-impossible: that rules out a decoder lower-bound valid in every tracial representation; this identifies the precise trace-functorial step inside the proposed tag ladder.
  finite-packet-cannot-realize-absorbing-contraction: that uses a finite packet's regular summand as a countermodel to finite-table contraction; this uses the canonical trace of the final infinite group and the summable first-hit recurrence itself.
  free-occurrence-hnn-return-does-not-preserve-first-hit-prefix: that invalidates one particular prefix placement; this applies even after the prefix and context incidences have been made exact.
---

Let `Gamma` be a discrete group and work in its finite von Neumann algebra
`L(Gamma)` with faithful canonical trace `tau`.  Suppose exact projections
`q_n,r_n` satisfy, for every `n>=0`,

```text
2 tau(q_n)<=tau(q_(n+1))+tau(r_n),
tau(r_n)<=tau(q_n),
tau(r_n)>=eta tau(q_n),
sum_(n<N)tau(r_n)<=1                                  (RFL1)
```

for one `eta>0` and every `N`.  The first two inequalities give

```text
tau(q_(n+1))>=tau(q_n).                               (RFL2)
```

Hence

```text
1>=sum_(n<N)tau(r_n)>=eta N tau(q_0)                  (RFL3)
```

for every `N`, so `tau(q_0)=0`.  Faithfulness gives `q_0=0` in `L(Gamma)`.

Every zero-defect ingredient of the proposed S3/tag ladder is valid in
`L(Gamma)`: finite subgroup tables are already exact, endpoint and context
spectral cuts are genuine projections, unitary transport preserves trace,
and the first-hit telescope is an operator identity.  Therefore a proof of
`(RFL1)` using only those ingredients cannot make `q_0` a positive carrier
for a nontrivial group word.  If fixed group relations also made separation
of `w` imply

```text
tau(q_0)>=c tau((w-I)^*(w-I))                         (RFL4)
```

for `c>0`, applying the regular representation to `w!=1` would contradict
`(RFL3)`.

This does not rule out a finite-dimensional first-hit argument.  It shows
that one of its load-bearing inequalities must use a genuinely matrix-only
fact—integer rank, finite multiplicity, or a decoder not defined on arbitrary
finite von Neumann algebras.  Context/tag covariance and trace cyclicity alone
cannot supply that step.

In particular, the two-bit tag and context-atom bridge remain valid local
placement lemmas.  What fails is promoting their exact tracial identities to
the full Fanizza matrix decoder without an additional finite-dimensional-only
multiplicity theorem.

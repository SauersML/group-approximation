---
rg: 2
id: canonical-tight-orthogonal-checksum-collapses-one-mark
kind: claim
title: A canonically tight orthogonal checksum collapses one fixed mark depthwise
distinct_from:
  orthogonal-checksum-controls-only-mass-weighted-syndromes: that permits the authenticated block mass to escape to later indices; this adds canonical tightness and proves that arbitrary depthwise constants then suffice.
  self-similar-square-function-checksum-compiler: that asks for a uniform backward carrier recurrence; this gives a different sufficient condition, namely canonical-trace tight exhaustion of one fixed carrier.
  depthwise-canonical-kleene-needs-no-uniform-runtime-gap: that is the reverse-Kleene quantifier theorem; this supplies its concrete orthogonal-block analytic hypothesis.
---

ESTABLISHED CONDITIONAL CHECKSUM THEOREM.  Let `(U_m)` be a
canonical-profile matrix sequence, let `W_m` be one fixed marked word, and
let `P_m` be one fixed authenticated carrier projection.  For every depth
`N`, suppose a finite decoded window supplies pairwise orthogonal
projections

```text
 P_(m,1),...,P_(m,N)<=P_m,
 T_(m,N)=P_m-sum_(n<=N)P_(m,n),                         (CTO1)
```

with the following properties.

1. For every fixed `n`,

```text
 ||(W_m-I)P_(m,n)||_2^2 ->0.                            (CTO2)
```

The finite proof constant may depend arbitrarily on `n` and its simulated
runtime.
2. There are numbers `b_N->0` such that

```text
 limsup_(m->infinity) tr_m(T_(m,N))<=b_N.               (CTO3)
```

Then

```text
 ||(W_m-I)P_m||_2 ->0.                                  (CTO4)
```

If additionally `liminf tr_m(P_m)>0`, `(CTO4)` collapses the mark on one
positive-density carrier.  No estimate is uniform in depth, detected block
size, or runtime.  The load-bearing uniformity is instead **canonical
tightness** `(CTO3)` and use of the same `W_m,P_m` at every depth.

This is the exact circumstance in which an orthogonal checksum defeats
direct-sum dilution.  A sequence supported entirely on block types
`k_m->infinity` has zero limiting mass in every fixed decoded type, so it
violates `(CTO3)` whenever the root carrier retains positive canonical
mass.  Depthwise Kleene by itself does not exclude that escaping sequence.


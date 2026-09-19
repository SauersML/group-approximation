---
rg: 2
id: stw29-projection-qq-dichotomy-proof
kind: route
title: Spread one defect projection through simplicity and reflect proper infiniteness from a multiple
target: stw29-projection-qq-characterizes-rr0-dichotomy
requires: []
artifacts:
  - research/artifacts/stw29-projection-monoid-dichotomy-audit-2026-08-30.md
---

Suppose first that `V(A)` has `(QQ_V)`.  If `V(A)` has no infinite nonzero
element, then no matrix algebra over `A` contains an infinite projection,
so `A` is stably finite.

Assume instead that `p in V(A)` is infinite.  There is a nonzero `r` with

```text
p+r=p.                                                   (1)
```

Every nonzero projection in a simple algebra is full.  Hence `p<=k r` for
some `k`.  Iterating `(1)` gives `p+k r=p`, and therefore

```text
2p <= p+k r = p.                                        (2)
```

Thus `p` is properly infinite.

Let `q` be any nonzero element of `V(A)`.  Simplicity gives integers
`l,m>=1` with

```text
p <= lq,                    q <= mp.                    (3)
```

A properly infinite element absorbs every finite multiple of itself.  From
`(2)` and `(3)` one gets

```text
2(lq) <= 2lm p <= p <= lq.
```

Thus `lq` is properly infinite.  Property `(QQ_V)` now makes `q` properly
infinite.  We have proved that every nonzero projection in every matrix
algebra over `A` is properly infinite.

Real rank zero gives a nonzero projection in every nonzero hereditary
subalgebra.  The standard simple real-rank-zero pure-infiniteness criterion
therefore applies, and `A` is purely infinite.

Conversely, `(QQ_V)` is automatic in either side of the dichotomy.  In a
stably finite algebra no nonzero multiple is properly infinite.  In a
purely infinite simple algebra every nonzero projection class is properly
infinite.

Finally assume that `A` contains an infinite projection and a finite
projection `q`.  The first half of the proof makes some `p` properly
infinite, and simplicity gives `(3)`.  The same calculation shows that
`lq` is properly infinite.  Hence

```text
(l+1)(2q) <= lq,
```

while `2q not <= q` because `q` is finite.  This is the explicit
almost-unperforation failure `(P)`: proper infiniteness of `lq` makes every
multiple `mq` with `m>=l` at most `lq`, including `m=2(l+1)`.

More generally, if `nx` is properly infinite, then

```text
(n+1)x <= 2nx <= nx.
```

Induction gives `mx<=nx` for every `m>=n`, so
`(n+1)(2x)<=nx`.  Almost unperforation, applied with the pair `2x,x`,
therefore gives `2x<=x`.  Thus almost unperforation implies `(QQ_V)`.

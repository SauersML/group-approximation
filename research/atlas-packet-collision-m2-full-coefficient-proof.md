---
rg: 2
id: atlas-packet-collision-m2-full-coefficient-proof
kind: route
title: Read four matrix units from the stored eight-dimensional escape frame
target: atlas-packet-collision-m2-has-full-coefficient-algebra
requires:
  - atlas-multiplicity-two-packet-collision-hub-escape
  - atlas-morita-coefficient-cyclicity-reduction
---

Decode the stored hexadecimal frame `(PCM1)` row-wise in the interleaved
four-by-two basis and invert it over `F2`.  Its relevant blocks are

```text
T_(1,3)=[1 1;0 0],       T_(1,4)=[0 0;1 1],
S_(3,1)=[0 0;1 0],       S_(1,2)=[1 0;1 1].
```

Their four products are exactly `(PCM2)`, hence generate `M_2(F2)`.
The cited escape theorem supplies exact packet and collision and failure of
q14.  On a `k`-fold direct amplification the algebra acts only on the first
tensor factor.  Each seed vector exposes at most two vectors in the passive
`F2^k` factor, so a generating seed has dimension at least `ceil(k/2)`.
This is the asserted positive-density amplification fence.

---
rg: 2
id: a4-holonomy-gap-from-packet-commutator-collapse
kind: route
title: Packet-central relative chart frames force the two S3 covariance defects to vanish
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-relative-packet-commutator-collapse
  - atlas-packet-energy-controls-s3-covariance
---

Take the normalized exact A4 context sequence in the target and choose any two
regular chart frames.  By `atlas-a4-relative-packet-commutator-collapse`, the
relative chart unitary `U_n` has packet commutator energy

```text
E_packet(U_n) -> 0.
```

The gauge invariance recorded in that claim means this is independent of the
chosen regular chart identifications.  Apply
`atlas-packet-energy-controls-s3-covariance` to the same `U_n`:

```text
a_n^2+b_n^2 <= (28363/1260) E_packet(U_n) -> 0.
```

In particular

```text
limsup_n (a_n^2+b_n^2)=0 < 1/128,
```

which is stronger than `(A4-HOL-GAP)`.

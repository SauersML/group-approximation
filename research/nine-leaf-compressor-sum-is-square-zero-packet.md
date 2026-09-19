---
rg: 2
id: nine-leaf-compressor-sum-is-square-zero-packet
kind: claim
title: Summing the two nine-leaf compressors produces a square-zero packet
distinct_from:
  openai-nine-leaf-leavitt-configuration: that constructs the two compressors and proves the geometric compression and generation properties; this computes their relative involution in the modular group algebra and rules out the symmetric sum as a proper isometry.
  recursive-leavitt-kernel-packets-are-locally-finite: that traps iterated constant S3 packets in finite subgroup algebras; this is a separate exact cancellation for the two Thompson prefix compressors.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

For the compressors `u,v` and elementary subgroup `Gamma` of the nine-leaf
Leavitt configuration, put `c=v^(-1)u` and `n=1+[c]` in the characteristic-two
group algebra.  Then

```text
c^2=1,        [c,Gamma]=1,        n^2=0,
```

and for every `a in F_2[Gamma]`,

```text
([u]+[v]) a ([u^(-1)]+[v^(-1)])=0.
```

Thus the obvious symmetric sum of the two compressors is a square-zero
packet, not a proper isometry or a direct-finiteness witness.

---
rg: 2
id: periodic-higman-spectrum-is-cofinite
kind: claim
title: Every sufficiently large integer belongs to the periodic-Higman spectrum
artifacts:
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
distinct_from:
  periodic-higman-spectrum-contains-three: that is one order-three certificate; this supplies all integers beyond an explicit bound and does not assert membership of three.
---

For the spectrum `Sigma` in `periodic-higman-period-spectrum-criterion`,
every integer

```text
n > B_* = 4000 * 40^12 = 67108864000000000000000
```

belongs to `Sigma`. Moreover, `G_n` has a finite matrix quotient preserving
each of `x_0,x_1,x_2,x_3` as a nonidentity element, with the stable letter
having exact order `n`.

Consequently the missing-period criterion cannot apply at any `m>B_*`.
This does not assert that `G_n` is residually finite. It leaves open the
possibility of missing primes in the finite interval from the fixed
filling threshold `m_0` to `B_*`.

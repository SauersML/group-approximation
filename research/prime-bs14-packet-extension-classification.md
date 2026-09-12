---
rg: 2
id: prime-bs14-packet-extension-classification
kind: claim
title: Exact primitive-prime scalar BS14 packets extend iff they are the full odd Weil orbit
distinct_from:
  iwahori-cycle-packet-determinant-fence: that gives a determinant obstruction; this is the exact primitive-prime classification.
  iwahori-weil-cycle-packets-extend-exactly: that supplies the positive Weil model; this adds necessity.
  bs14-relative-involution-extension-stability: that is approximate and flexible; this is exact and irreducible-packet level.
---

Let `p>=7` be prime, `lambda` primitive of order `p`,
`m=ord_p(4)`, and let the scalar `BS(1,4)` cycle have eigenvalues
`lambda,lambda^4,...,lambda^(4^(m-1))` and wrap scalar `v`.  It extends to
the five exact Iwahori relations exactly when

```text
p == 3 mod 4,  m=(p-1)/2,  v=1.
```

These and only these packets are restrictions of the odd Weil constituent
of `PSL_2(F_p)`.  Thus the prime-packet exact zeros are completely
classified rather than merely excluded by determinant congruences.

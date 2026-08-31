---
rg: 2
id: periodic-higman-prime-spectrum-semisimple-reduction
kind: claim
title: A prime Higman period has an automorphism-simple semisimple certificate
---

**ESTABLISHED.**  Let `Sigma` be the period spectrum in
`periodic-higman-period-spectrum-criterion`, and let `ell` be prime.  If
`ell in Sigma`, then there are

```text
Q = S^m,                 m in {1,ell},
beta in Aut(Q),          ord(beta)=ell,
Q=<q_0,q_1,q_2,q_3>,     beta(q_i)=[q_i,q_(i-1)],
```

where `S` is a nonabelian finite simple group and `beta` acts transitively on
the `m` simple direct factors of `Q`.

Thus exclusion of a prime from `Sigma` needs only exclude two exact finite
semisimple cases:

1. an almost-simple case `Q=S`, with an order-`ell` automorphism of `S`;
2. a cyclic-factor case `Q=S^ell`, with the order-`ell` automorphism acting
   transitively on the factors.

This is a reduction, not a proof that any prime is absent.  In particular it
does not establish `periodic-higman-large-prime-period-gap`.


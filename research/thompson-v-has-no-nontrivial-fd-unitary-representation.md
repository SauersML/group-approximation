---
rg: 2
id: thompson-v-has-no-nontrivial-fd-unitary-representation
kind: claim
title: Every finite-dimensional unitary representation of Thompson's V is trivial
distinct_from:
  thompson-v-not-lef: that excludes local embeddings into finite groups; this excludes every finite-dimensional complex unitary representation.
---

Every homomorphism

```text
rho:V -> U(d)
```

is trivial.

Indeed Thompson's `V` is infinite, finitely generated and simple.  If `rho`
were nontrivial, simplicity would make it injective.  Its image would then be
a finitely generated linear group over `C`, hence residually finite by
Mal'cev's theorem.  This would make `V` residually finite (and therefore LEF),
contradicting `thompson-v-not-lef`.

The conclusion is stronger than absence of finite quotients: it also excludes
infinite compact matrix images.

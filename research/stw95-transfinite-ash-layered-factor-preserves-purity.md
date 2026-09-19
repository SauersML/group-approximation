---
rg: 2
id: stw95-transfinite-ash-layered-factor-preserves-purity
kind: claim
title: Transfinitely ASH-layered separable factors preserve purity under the Seth--Vilalta hypotheses
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
  - research/artifacts/stw95-nonunital-ash-unitization-audit-2026-08-30.md
distinct_from:
  stw95-nuclear-successor-filtrations-need-no-exact-factor: that assumes purity of every successor-layer tensor product; this verifies all those local hypotheses uniformly for ASH layers by the Seth--Vilalta theorem.
  stw95-one-zstable-factor-forces-pure-product: that uses Z-absorption of one factor and allows an arbitrary other factor; this permits a non-Z-stable pure factor but requires its Seth--Vilalta quotient condition and an ASH-layered other factor.
  stw95-nonunital-ash-factor-preserves-purity: that is the local theorem for one possibly nonunital ASH factor; this assembles arbitrarily many such cells through a continuous ordinal filtration.
---

Let `A` be a pure C*-algebra.  Assume that either

1. `A` is simple; or
2. every quotient of `A` is stably finite.

Let `B` be separable and admit a continuous increasing filtration
`(J_alpha)_(alpha<=gamma)` by closed ideals, indexed by an arbitrary ordinal,
such that

```text
J_0=0,                 J_gamma=B,
J_lambda=closure(union_(alpha<lambda) J_alpha)
```

at every limit ordinal.  If every successor quotient
`J_(alpha+1)/J_alpha` is a **separable ASH algebra**, not necessarily unital,
then

```text
A tensor_min B
```

is pure.

Consequently, if `B` is itself pure, then `(A,B)` is a positive class for
the general pure-tensor permanence question in Problem XCV.  The conclusion
does not require `A` to be separable or exact, `B` itself to be ASH, or either
factor to be Z-stable.  When `gamma` is countable, separability of `B` already
follows from separability of the successor quotients by extension and
sequential-limit permanence; thus the arbitrary-ordinal statement contains
the countable-filtration case.

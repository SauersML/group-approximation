---
rg: 2
id: uniform-power-return-abelianization-barrier
kind: claim
title: A bounded-root power-return certificate forces the cursor to have zero free abelianization
distinct_from:
  uniform-power-return-self-hash: that asks for the positive compiler; this is a necessary syntactic condition excluding cursors with growing exponent vector.
---

If each word

```text
q_m=a_m w a_m^-1 w^-m
```

is a product of at most `C` conjugates of one fixed finite relator list, then
free abelianization gives `[q_m]_ab=(1-m)[w]_ab`.  The right-hand certificate
family has uniformly bounded exponent vectors, while the left side grows
linearly unless `[w]_ab=0`. This is a necessary condition only.
`power-return-certificates-have-linear-area` now excludes the
bounded-certificate hypothesis for every nontrivial cursor,
including commutator words with zero exponent vector.

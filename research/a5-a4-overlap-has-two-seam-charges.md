---
rg: 2
id: a5-a4-overlap-has-two-seam-charges
kind: claim
title: An A5 chart has two independent seams invisible on an A4 overlap
distinct_from:
  a5-carmichael-triangle-covers-involution-kernels: that is a positive spectral gap for three involutions inside one fixed A5 representation; this identifies representation types which remain indistinguishable after restriction to the common A4 face.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that gives arbitrarily large private-gauge models for the prefix-clone fragment; this is a two-chart finite-group obstruction already present in A5 amalgamated over A4.
---

Let `R(G)` denote the complex representation ring.  For the standard
inclusion `A4 < A5`, restriction has kernel

```text
ker(Res:R(A5)->R(A4))
  = Z([3]-[3']) directSum Z([4]-[1]-[3]).               (ASC1)
```

Here `1,3,3',4,5` are the irreducible representations of `A5`, and
`1,1',1'',3` are those of `A4`.  Thus an exact common `A4` face does not
determine the adjacent `A5` chart: it misses two independent integral seam
charges.

This ambiguity is realized by exact finite-dimensional unitary charts.  Two
copies of `A5` amalgamated over their standard `A4` admit:

* a three-dimensional representation which is `3` on one copy and `3'` on
  the other; and
* a four-dimensional representation which is `4` on one copy and `1+3` on
  the other.

In each case the two actions can be conjugated so that they agree literally
on the amalgamated `A4`.  Neither representation factors through the natural
`A6` completion formed by two adjacent point-stabilizer copies of `A5`.
Consequently any local-to-global alternating-packet argument based only on
agreement of the `A4` restrictions is false.  An additional collision datum,
such as the Thompson R5 relation across the two nonshared leaves, must remove
both seam directions.


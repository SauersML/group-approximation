---
rg: 2
id: cdi-standard-generator-choice-fails-projective-gate
kind: claim
title: A standard allowed CDI generator choice has a strictly intermediate character coefficient
distinct_from:
  cdi-wreath-extension-preserves-projective-basis-gate: that proves the exact transfer equivalence for every input representation; this exhibits a concrete input permitted by CDI Lemma 5.1 for which the transferred gate fails.
  projective-basis-character-criterion: that gives the abstract intermediate-coefficient test; this produces such a coefficient from the actual Ge-Popa block generator.
---

In the proof of CDI Theorem A, write

```text
M_tilde=P tensor R,
P=M*L(F_2).
```

Choose the generating sequence `(w_i)` of `P` used in CDI Lemma 5.1 so that
`w_1=1` and some `w_2` is non-scalar.  With nonzero orthogonal projections
`(p_i)` summing to one and generators `u,v` of `R`, the three generating
unitaries are

```text
a=1 tensor u,
b=1 tensor v,
c=sum_i w_i tensor p_i.                                (CDI-S1)
```

This completely legitimate source-level choice has a word `r=r(a,b)` such
that

```text
0 < |tau_Mtilde(c r)| < 1.                             (CDI-S2)
```

Hence the input character of `F_3` fails gate `(G1)`, and by
`cdi-wreath-extension-preserves-projective-basis-gate` the final CDI
property-`(T)` character fails `(G1)` as well.

Thus the published proof not only leaves `(G1)` uncontrolled: its standard
generator lemma admits an explicit implementation where `(G1)` is false.
Obtaining the positive twisted-sector compiler requires replacing this
choice by a generating tuple whose entire group character vanishes off its
scalar kernel, which is exactly the projective-group-basis problem and is not
provided by embedding universality.


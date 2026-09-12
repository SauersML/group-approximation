---
rg: 2
id: linear-sofic-implies-weakly-sofic-over-every-field
kind: claim
title: Groups linear sofic over any field are weakly sofic
distinct_from:
  weakly-sofic-not-sofic: that separates weak soficity from soficity through the Kun--Thom wreath; this is the inclusion of every linear sofic class into the weakly sofic class.
  sofic-implies-linear-sofic-over-every-field: that is the lower inclusion of the chain; this is the upper one.
---

ESTABLISHED.  For every field `F`, an `F`-linear sofic countable group is
weakly sofic.  So for each `F`,

```text
sofic  <=  F-linear sofic  <=  weakly sofic.
```

For a finite field this is immediate: `GL_n(F)` is a finite group and the
normalized rank metric is bi-invariant.  For an arbitrary field the finite
entry ring is reduced modulo a maximal ideal, as in Arzhantseva--Paunescu
arXiv:1212.6780, Theorem 8.2 (stated there over `C`).  See
[[linear-sofic-implies-weakly-sofic-over-every-field-proof]].

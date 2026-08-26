---
rg: 2
id: simple-kazhdan-groups-have-full-mf-radical
kind: claim
title: Every infinite simple Kazhdan group has full MF radical
distinct_from:
  map-matricial-stability-non-mf: That needs point-operator-norm stability and minimal almost periodicity; this uses neither, applying the Ozawa--Thom weak-quasidiagonality theorem directly to an infinite simple property-(T) group.
  simple-sofic-total-mf-radical: That constructs one countable simple sofic full-radical group without property (T); this proves full MF radical for every infinite simple Kazhdan group, without asserting soficity.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: That supplies five concrete finitely presented torsion-free inputs; this is the general MF-radical theorem that applies to each of them.
---

Let `K` be a countable infinite simple group with property `(T)`.  Then

```text
K is not MF,                 Rad_MF(K)=K.               (SKM1)
```

Equivalently, every homomorphism from `K` to an MF group is trivial.

The input is Dadarlat, *Obstructions to matricial stability of discrete
groups and almost flat K-theory*, arXiv:2007.12655v2.  The introduction
states explicitly that every MF group is weakly quasidiagonal, and
Proposition 3.19 (Ozawa--Thom) states that every infinite weakly
quasidiagonal property-`(T)` group has an infinite residually finite
quotient.  Simplicity excludes such a quotient.

In particular, each of the five Titz Mite--Witzel simple finite residuals is
unconditionally non-MF and has full MF radical.  Its soficity remains a
separate question: sofic approximation is in normalized Hamming norm and
does not imply MF approximation in operator norm.

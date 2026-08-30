---
rg: 2
id: rips-kernel-equivalence-proof
kind: route
title: Factor finite quotients forward and use Kapovich-Wise plus Belegradek-Osin backward
target: rips-kernel-target-iff-hyperbolic-nonrf
requires: []
---

`(1) -> (2)`. Choose `1 != q in R_f(Q)` and a lift `g in G`. If `G` were
residually finite, some homomorphism `phi:G->F` to a finite group would have
`phi(g)!=1`. But `phi|_N` is a homomorphism from `N` to a finite group, so it
is trivial. Hence `phi` factors through `Q`, where it would detect `q`,
contradicting `q in R_f(Q)`. Thus the hyperbolic group `G` is not residually
finite.

`(2) -> (1)`. Let `Q` be a non-residually-finite word-hyperbolic group; it
is finitely presented. Kapovich--Wise Theorem 1.2 says that universal
residual finiteness of word-hyperbolic groups is equivalent to every
nontrivial word-hyperbolic group having a nontrivial finite quotient. Taking
the contrapositive gives a nontrivial word-hyperbolic group `H` with no
nontrivial finite quotient. Such `H` is non-elementary, since elementary
hyperbolic groups are residually finite.

Apply Belegradek--Osin Corollary 1.2 to this `H` and the finitely presented
`Q`. It gives

```text
1 -> N -> G -> Q -> 1
```

with `G` word-hyperbolic and `N` a quotient of `H`. Every homomorphism from
`N` to a finite group pulls back along the surjection `H->N`, hence is
trivial. Thus `N` has no nontrivial finite quotient, proving (1). `QED`

Primary sources:

- Ilya Kapovich and Daniel T. Wise, *The equivalence of some residual
  properties of word-hyperbolic groups*, J. Algebra **223** (2000),
  562--583, DOI `10.1006/jabr.1999.8104`, Theorem 1.2.
- Igor Belegradek and Denis Osin, *Rips construction and Kazhdan property
  (T)*, Groups Geom. Dyn. **2** (2008), 1--12, DOI `10.4171/GGD/29`,
  Corollary 1.2 and the discussion on p. 4.

Sources checked 2026-08-30.

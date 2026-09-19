---
rg: 2
id: kt-q2-double-gao-relative-embedding-proof
kind: route
title: Verify Gao's Haar-relative-unitary hypothesis using the SLd quotient
target: kt-q2-double-hyperlinear-iff-relative-embeddable
requires: []
artifacts:
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

Gao--Junge--Gao, arXiv:2012.07940v3, Appendix Theorem 7.1, says that for
finite von Neumann algebras `N subset M` and a finite factor `N_1`, relative
embeddability `RE/N_1` is equivalent to tracial embeddability of `M *_N M`
into `(R tensor N_1)^omega`, provided that `M` contains a unitary `u` with

```text
E_N(u^k)=0       for every nonzero integer k.                 (KGR1)
```

Take `N_1=C`, which is a finite factor.  Choose an infinite-order matrix
`A in SL_d(Z)` and put `a=(1,A) in G`, `u=lambda(a) in L(G)`.  The quotient
map `G->SL_d(Z)` is trivial on `Gamma`, while the image of `a^k` is
`A^k!=1` for every `k!=0`.  Hence `a^k` lies outside `Gamma`, and the group
conditional expectation `E_(L(Gamma))` gives `(KGR1)`.

The canonical tracial amalgamated free product satisfies

```text
L(G) *_(L(Gamma)) L(G) = L(G *_Gamma G).
```

Taking `N_1=C` in Gao's theorem therefore proves `2 <=> 3`.  Finally,
Connes embeddability of `L(D)` is equivalent to hyperlinearity of the
countable group `D`, proving `1 <=> 2`.

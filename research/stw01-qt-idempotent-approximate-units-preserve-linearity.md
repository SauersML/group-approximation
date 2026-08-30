---
rg: 2
id: stw01-qt-idempotent-approximate-units-preserve-linearity
kind: claim
title: Quasitracially idempotent approximate units split bounded quasitraces
distinct_from:
  stw01-qt-central-projection-extensions-preserve-linearity: that uses genuine projections whose commutators are universally quasitrace-null; here the approximate-unit elements may be positive nonprojections, and only become central projections in the individual quasitracial quotients.
  stw01-qt-invisible-ideal-extension-principle: that requires every bounded quasitrace to annihilate the whole ideal; here the ideal may have a traced central summand and need not admit any projectional approximate unit.
  stw01-central-projection-ideal-extensions-preserve-qt-linearity: that splits the extension by central projections already inside A; neither projections nor centrality in A are assumed here.
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `A` be a unital C-star algebra and write

```text
J_bQT(A)=intersection_(tau in QT_b(A)) N_tau,
N_tau={x in A:tau(x*x)=0}.
```

Let `I triangleleft A` have an increasing approximate unit `(e_n)` of positive
contractions such that

```text
e_n-e_n^2 in J_bQT(A),        [e_n,A] subset J_bQT(A)       (n>=1).   (QTI)
```

Suppose every bounded `2`-quasitrace on the hereditary algebra
`Her_A(e_n)` is a trace, for every `n`, and every bounded `2`-quasitrace on
`A/I` is a trace.  Then every bounded `2`-quasitrace on `A` is a trace.

The two conditions in `(QTI)` say exactly that the image of `e_n` is a
central projection in every quotient `A/N_tau`.  Thus this theorem strictly
contains `stw01-qt-central-projection-extensions-preserve-linearity`.

The containment is strict even at the level of algebras, not only of chosen
approximate units.  Put

```text
D=C_0((0,1]) tensor K,
A=C direct_sum D~,                 I=C direct_sum D.
```

The stable algebra `D` is bounded-quasitrace-null and has no nonzero
projections.  If `f_n(t)=min(1,nt)`, `k_n` is an increasing finite-rank
projectional approximate unit for `K`, and

```text
h_n=f_n tensor k_n,                e_n=(1,h_n),
```

then `(e_n)` satisfies `(QTI)`.  Its hereditary algebras are a scalar summand
plus a finite-homogeneous algebra, and `A/I=C`, so the theorem applies.  The
ideal `I` carries the nonzero scalar trace but admits no projectional
approximate unit, because every projection in its `D` summand is zero.


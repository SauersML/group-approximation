---
rg: 2
id: right-translation-outer-class-injectivity-proof
kind: route
title: Detect right-translation outer classes with the Cartan full group
target: noncompact-right-holonomy-is-not-compact-profinite
requires: []
---

Let `D=L^infinity(L)`.  The left translation action `A y L` is essentially
free, so `D subset P=D rtimes A` is a Cartan inclusion.  Every `alpha_h`
preserves `D`.

Suppose `alpha_h=Ad(v)` for a unitary `v in P`.  Since `alpha_h(D)=D`, the
unitary `v` normalizes the Cartan algebra.  The normalizer/full-group
dictionary for a free group-measure-space Cartan says that the underlying
measure transformation lies in the full group of the left `A`-orbit
relation.  Thus there is a measurable map `a:L->A` such that, for almost
every `x in L`,

```text
x h = a(x) x.                                             (RTO1)
```

The group `A` is countable.  Hence one fiber `a(x)=a_0` has positive Haar
measure.  On that fiber,

```text
x h x^(-1)=a_0.                                          (RTO2)
```

If `(RTO2)` has one solution `x_0`, its full solution set is a left coset of
the centralizer `C_L(h)`.  A measurable subgroup of a locally compact group
has positive Haar measure only if it is open.  For `L=SL_2(Q_2)`, the
centralizer of a noncentral element has empty interior: equivalently, an open
centralizer would have full Lie algebra `sl_2(Q_2)`, forcing the element to be
central.  The positive-measure fiber therefore implies `h in Z(L)`.

Conversely, if `h=z in Z(L)={+-I}`, then `z in A` and right translation by
`z` equals left translation by `z`; hence `alpha_z=Ad(u_z)` on `P`.  This
proves `(NCH2)`.  Since right translations compose (with order determined by
the convention in `(NCH1)`), applying `(NCH2)` to
`alpha_h alpha_k^(-1)` proves `(NCH3)`.

Finally, discreteness makes `Lambda' cap K` a finite subgroup: it is discrete
and compact.  Torsion-freeness gives `Lambda' cap K={e}`.  If a nontrivial
`lambda in Lambda'` and `k in K` had the same outer class, `(NCH3)` would give
`lambda k^(-1) in Z(L) subset K`, hence `lambda in K`, a contradiction.  This
is `(NCH4)` and finishes the proof.

---
rg: 2
id: stw84-weighted-fourier-cutdown-and-row-gap
kind: claim
title: Weighted augmentation carriers retract Fourier windows; canonical Fourier rows have a fixed order-zero gap
distinct_from:
  stw84-folner-carrier-corners-are-normal-closure-corners: that theorem identifies the support corner and shows that it is Morita-tautological for the alternating shift; the present theorem retains the positive weights, quantifies the resulting Fourier retraction, and isolates a separate order-zero obstruction in the canonical band-matrix return map.
artifacts:
  - research/artifacts/stw84-weighted-fourier-cutdown-audit-2026-08-30.md
---

Let

```text
G=K rtimes_alpha Z,       A=C*(G),       J=I_K rtimes_alpha Z,
```

where `K` is countable and locally finite, and write `U` for the canonical
implementing unitary.  Given a finite set of algebraic augmentation
coefficients and `N>=1`, let `h` be the finite-spectrum positive carrier
from `stw84-augmentation-ideal-has-finite-dimensional-folner-carriers`.
Thus, for every prescribed coefficient `a`,

```text
ha=ah=a,       ||alpha^k(h)-h||<=|k|/N.               (WFC1)
```

Then the c.p.c. cutdown `C_h(x)=h^(1/2)x h^(1/2)` satisfies

```text
||C_h(a U^k)-a U^k|| <= ||a|| sqrt(|k|/N).            (WFC2)
```

Consequently, for a prescribed Fourier polynomial

```text
x=sum_(|k|<=L) a_k U^k,
```

one can choose the carrier to obtain

```text
||C_h(x)-x||
 <=sum_(|k|<=L)||a_k|| sqrt(|k|/N).                   (WFC3)
```

This is a genuine weighted replacement for the non-invariant support
projection: no estimate on `alpha(s(h))-s(h)` is used.

There is, however, a uniform obstruction to combining `(WFC2)` with the
canonical interval-compression return map.  Let `A` be any unital
C-star algebra, let `U in A` be unitary, and let `h in A` be a norm-one
positive contraction.  For `n>=2`, define

```text
Theta_(h,n):M_n -> A,
Theta_(h,n)([c_ij])
 =n^(-1) sum_(i,j=0)^(n-1)
   c_ij h^(1/2) U^i U^(-j) h^(1/2).                  (WFC4)
```

This is c.p.c. and `Theta_(h,n)(1)=h`.  Nevertheless,

```text
inf{||Theta_(h,n)-Psi||:
    Psi:M_n->A c.p.c. order zero}
 >= floor(n/2)ceil(n/2)/(2n^2) >=1/9.                (WFC5)
```

For every unital `D`, the same lower bound holds for any c.p.c. map on
`M_n(D)` whose restriction
to the scalar copy `M_n tensor 1_D` is `(WFC4)`.  Thus slow covariance of
the positive carrier and even exact recovery of a finite Fourier packet do
not make the standard Fourier-row return approximately order zero.  A
finite-nuclear-dimension proof must replace that row map, split it by a
genuinely different multi-colour construction, or exploit additional
coefficient orthogonality; cone-projective repair of the unsplit row is
quantitatively impossible.

---
rg: 2
id: maslov-ce-subgroup-classifies-finite-deligne-covers
kind: claim
title: The CE subgroup of the Maslov circle exactly classifies hyperlinear finite Deligne covers
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that treats the fixed triple cover and its two nontrivial fibres; this simultaneously classifies every finite cyclic quotient of the universal Deligne extension.
  finite-central-hs-sector-decomposition: that decomposes approximate representations along central spectral sectors; this uses the exact von Neumann direct-sum decomposition and the closed-subgroup theorem to obtain an iff classification.
---

**ESTABLISHED.**  Let

```text
1 -> Z -> E_infinity -> Sp_4(Z) -> 1
```

be the integral Deligne extension represented by the Maslov cocycle `b`, and
let

```text
E_q=E_infinity/(qZ),       q>=1.
```

If `E_CE` is the closed subgroup of the Maslov circle from
`maslov-ce-parameter-set-is-a-closed-subgroup`, then

```text
E_q is hyperlinear    iff    1/q belongs to E_CE.        (FDC1)
```

Indeed the central Fourier projections give the finite direct-sum
decomposition

```text
L(E_q) = direct_sum_(j=0)^(q-1)
         L_(c_(j/q))(Sp_4(Z)).                            (FDC2)
```

The group `E_q` is hyperlinear exactly when every summand in `(FDC2)` is
Connes embeddable.  If `1/q in E_CE`, the subgroup property puts every
`j/q` in `E_CE`.  Conversely hyperlinearity makes the `j=1` summand CE.
This proves `(FDC1)`.

Consequently the following are equivalent:

1. nontrivial CE Maslov parameters accumulate at zero;
2. every finite Deligne cover `E_q` is hyperlinear;
3. finite Deligne covers of unbounded orders are hyperlinear.

If these fail, `E_CE` is a finite cyclic group, so any prime `q` not dividing
its order has `1/q notin E_CE`; `(FDC1)` makes the finitely presented finite
central extension `E_q` nonhyperlinear.  Thus failure of the small-twist CE
claim yields a finitely presented nonhyperlinear group, not merely the
countable phase extension attached to an irrational parameter.


# Kun--Thom infinite-degree correspondence audit

**Date:** 2026-08-26

## Corrected question

The literal returned word is not a compressor normalizer.  Its left
saturation sees the infinite-degree marked double coset.  Can divergence of
the resulting left/right correspondence dimensions itself obstruct finite
matrices?

## Exact countermodel

No.  Take the diagonal algebra `D_d subset M_d` for `d=2^r` and the
normalized Walsh matrix

```text
H_(s,t)=d^(-1/2)(-1)^(s dot t).
```

Every entry is nonzero, so diagonal compression on the left and right
recovers every matrix unit:

```text
D_d H_d D_d=M_d.
```

As a right `D_d`-module, `M_d` is `d` copies of `D_d`; the same holds on the
left.  Both dimensions are exactly `d`, while the correspondence occupies
all of `L2(M_d)`.  Thus degree can diverge without either a defect or
vanishing physical density.

At the same time,

```text
||E_(D_d)(H_d)||_2=d^(-1/2).
```

For any nonzero Walsh character `a_d in D_d`, Fourier conjugation sends it to
a nontrivial translation matrix, whose diagonal expectation is zero:

```text
E_(D_d)(H_d^*a_dH_d)=0.
```

So the model also satisfies the precise finite-matrix signatures already
extracted from the literal Kun--Thom word: small return expectation, a fixed
exterior conjugate, and uniform separation from edge normalizers.  Polar
correction changes the Walsh unitary by at most `2/sqrt(d)`.

## Consequence

No obstruction can depend only on:

- divergence or imbalance tests for left/right module dimensions;
- full left/right support;
- positive physical carrier density;
- vanishing return expectation;
- one fixed exterior-conjugate conditional-expectation test;
- the standard conditional-expectation/polar correction.

The calibration does not model the full Kun--Thom actor.  That is exactly the
remaining information: a positive proof must use simultaneous compatibility
of the expanding correspondence with the strict compressor and Kazhdan actor,
not correspondence degree alone.

## Cairn duplication check

Searches for `double coset correspondence dimension finite matrix degree`,
`infinite degree correspondence finite quotient`, and nearby text found the
group-theoretic infinite-degree theorem and aggregate leakage calibrations,
but no exact full-density bi-dimension countermodel.

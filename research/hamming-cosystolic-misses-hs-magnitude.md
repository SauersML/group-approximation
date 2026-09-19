---
rg: 2
id: hamming-cosystolic-misses-hs-magnitude
kind: claim
title: Nonabelian Hamming cosystolic expansion does not supply operator Hilbert--Schmidt rounding
distinct_from:
  operator-unique-neighbor-cosystolic-rounding: that asks for a normalized-HS magnitude estimate for matrix-valued local PVM data; this records why the available group-independent cosystolic theorem does not provide it.
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that proves an exact support-density theorem for noncommuting reflections; this separates support density from small operator magnitude.
---

The group-independent cosystolic theorem of Dikstein--Dinur, as imported in
Kaufman--Oppenheim--Weinberger, arXiv:2411.02819, Theorem 2.11, gives bounded-
degree complexes with uniform `1`-cosystolic expansion over every abstract
coefficient group `Lambda`.  Its cochain metric is the normalized support
metric:

```text
dist_Ham(alpha,beta)=Pr_e[alpha(e) != beta(e)].          (NHC1)
```

Consequently this theorem cannot be inserted as the missing estimate in
`operator-unique-neighbor-cosystolic-rounding`.  For unitary coefficients,
normalized Hilbert--Schmidt smallness permits

```text
alpha_e=exp(i epsilon H_e),
```

with every `alpha_e` nonidentity while all bounded face defects are
`O(epsilon)` in normalized HS norm.  Such a cochain has full Hamming support
for every `epsilon>0`, so it never enters the small-support hypothesis even
as its HS defect tends to zero.

This is a metric mismatch, not a counterexample to operator rounding.  It
shows exactly that nonabelian cover/cocycle stability controls the location
of discrete errors but supplies no estimate for continuously smeared matrix
errors.  A successful LDPC argument still needs an operator-valued magnitude
inequality or a preliminary quantization theorem converting HS energy into
sparse discrete defects.

---
rg: 2
id: culf-mastel-rstar-reduction-is-support-blind
kind: claim
title: Culf--Mastel applies to R-star but supplies no Fano-cap support theorem
distinct_from:
  culf-mastel-oracular-2csp-perfect-gap-family: that records the perfect-gap machine family and its RE orientation; this audits the fixed-language reduction at the level of local perfect-strategy supports.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for one cap-supported completeness model; this proves the cited reduction does not itself establish that extra property.
---

ESTABLISHED CITATION AUDIT.
The one-ghost relation `R_*` is non-TVF in the sense of Culf--Mastel.  For
every pair of coordinates and every assignment to that pair, the parity row
leaves two completions on the other coordinates, and deleting the single
ghost removes at most one.  Together with its non-Schaefer NP-completeness,
Culf--Mastel Theorem 6.8 therefore applies directly to the fixed language
`{R_*}` and supplies perfect completeness and constant soundness.

However, their completeness proof does not imply Fano-cap local supports.
In arXiv:2410.21223v2, Corollary 6.7 assumes only the classical extension
property

```text
phi in C_i  iff  there exists psi in D_i with psi|_(V_i)=phi.    (CMS1)
```

Theorem 6.8 then invokes NP-completeness to choose a transformed BCS with
that property, applies subdivision, and replaces empty constraints by the
non-TVF gadget of Proposition 6.2.  Neither `(CMS1)`, subdivision, nor
Proposition 6.2 bounds the set of `R_*` assignments receiving positive
spectral mass in a perfect lifted trace.  In particular, none excludes three
positive assignments on a Fano line.

Thus the published theorem rigorously supplies the fixed-language
Culf--Mastel family, but not
`culf-mastel-rstar-halt-model-has-fano-cap-support`.  Closing that node needs
a new cap-range witness selection for the classical reduction, or a global
support-minimality argument for the actual lifted perfect trace.

References: Culf--Mastel, arXiv:2410.21223v2, Proposition 6.2, Corollary 6.7,
and Theorem 6.8 (especially the invocation of NP-completeness in its proof).

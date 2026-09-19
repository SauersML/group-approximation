---
rg: 2
id: canonical-marked-corner-nonamenable-density-vanishes
kind: claim
title: A canonical central-sign corner has zero low-energy commutant density for every nonamenable subgroup
distinct_from:
  canonical-marked-corner-kazhdan-density-vanishes: that assumes property T and a Kazhdan gap; this uses only nonamenability and the regular spectral gap from Kesten's criterion.
  property-t-hs-positive-density-commutant-no-growth: that treats arbitrary characters and transports low spectra; this is specific to canonical microstates and proves absolute vanishing on one marked corner.
---

**ESTABLISHED PROPERTY-`(T)`-FREE TERMINAL.**  Let `G` contain a finitely
generated nonamenable subgroup `Lambda` and a central involution `J` with

```text
<J> intersect Lambda=1.
```

Let `phi_n` be canonical-trace normalized-Hilbert--Schmidt microstates of
`G`.  Exactify the central involution, put `e_n=(1-phi_n(J))/2`, and use the
normalized adjoint trace on `End(e_n H_n)`.  For a finite inverse-closed
generating multiset `S` of `Lambda`, set

```text
M_n=(1/|S|)sum_(s in S)Ad(phi_n(s))|_(e_n H_n),
A_n=I-M_n.
```

If

```text
kappa=1-||(1/|S|)sum_(s in S)lambda_Lambda(s)||>0,
```

then for every `0<b<kappa`,

```text
tr_ad(1_[0,b](A_n))->0.                                (CMN1)
```

Equivalently, if adjoint-space projections `R_n` have density bounded below,
their average old-group commutator energy cannot tend to zero:

```text
tr_ad(R_n A_n)
 >=b(tr_ad(R_n)-tr_ad(1_[0,b](A_n))).                  (CMN2)
```

This is a canonical-trace conclusion only.  It does not authenticate an
arbitrary norm-corona trace and therefore does not itself prove non-MF.

DERIVATION
canonical-marked-corner-kesten-proof


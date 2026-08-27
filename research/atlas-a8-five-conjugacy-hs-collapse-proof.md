---
rg: 2
id: atlas-a8-five-conjugacy-hs-collapse-proof
kind: route
title: Apply the normal-certificate theorem with collision multiplicity one
target: atlas-a8-five-conjugacy-hs-collapse
requires:
  - finite-normal-certificate-hs-collapse
  - atlas-a8-six-transvection-normal-certificates
---

Use the six standard transvection letters as the alphabet `S` and set

```text
beta=t23.
```

`atlas-a8-six-transvection-normal-certificates` supplies, for every generator,
a certificate

```text
s=a_s beta a_s^-1.
```

Hence every certificate contains exactly one occurrence of the distinguished
word `beta`: the constant `M` in `finite-normal-certificate-hs-collapse` is
exactly `1`.  The `t23` certificate is tautological and has zero defect, so the
maximum certificate defect is the maximum over the five displayed nontrivial
relations.

The generic estimate `(NG-CERT)` therefore specializes immediately to

```text
max_(s in S)||T_s-1||_2 <= eta+delta,
```

which is `(A8-5CHECK)`.

---
rg: 2
id: two-tier-matricial-invisibility
kind: claim
title: One finitely presented non-MF group has two strict levels of matricial invisibility
distinct_from:
  bare-self-copy-mf-calibration: That MF group supplies the exact-versus-asymptotic witness; this theorem places its lift beside a second word generating the MF radical of a non-MF camouflage group.
  compression-wreath-five-radicals-coincide: That theorem proves equality of several residuals in a telescope family; this construction forces the MF radical to be strictly smaller than the exact linear, finite, and Bohr residuals.
artifacts:
  - research/two-tier-matricial-invisibility-proof.md
  - experiments/verify_bs12_calibration.py
---

There is a finitely presented non-MF group `W` with explicit elements `d,z`
such that

```text
d belongs to Rad_MF(W),
z belongs to Rad_fd(W) and Rad_linear(W),
z does not belong to Rad_MF(W).                      (T1)
```

Here `Rad_linear` is the intersection of the kernels of all
finite-dimensional linear representations over all fields.  The same `z` is
killed by every finite quotient and every compact representation, but is
detected by one norm-corona representation.

Moreover

```text
Rad_MF(W)=normalClosure(d),
W/Rad_MF(W) ~= C,

Rad_MF(W) subsetneq Rad_fd(W),
Rad_MF(W) subsetneq Rad_linear(W).
```

where `C` is the torsion-free MF calibration group.  Thus one group exhibits
three distinct levels: a word invisible even asymptotically, a word visible
asymptotically but invisible to every exact finite-dimensional model, and
elements visible by exact models.

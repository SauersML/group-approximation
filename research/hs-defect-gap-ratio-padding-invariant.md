---
rg: 2
id: hs-defect-gap-ratio-padding-invariant
kind: claim
title: The intrinsic defect-gap ratio is exactly invariant under padding
distinct_from:
  weak-mf-embedding-not-reusable: That theorem shows that padding can destroy normalized Hilbert--Schmidt visibility of a fixed weak-MF embedding; this theorem identifies the defect-to-visibility quotient which padding leaves exactly unchanged.
  corner-renormalization-cost: That theorem quantifies compression by a projection; this theorem is an exact finite-matrix identity for direct sum with an identity block.
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

Let `phi:F->U(d)` be a unitary table, fix `g in F`, and let `m>=0`.  Put

```text
phi'(x)=phi(x) directSum 1_m in U(d+m),
rho=d/(d+m).
```

For every tested product `(a,b)` and the marked trace gap one has

```text
||phi'(a)phi'(b)-phi'(ab)||_(2,d+m)^2
  = rho ||phi(a)phi(b)-phi(ab)||_(2,d)^2,              (PI1)

1-Re tr_(d+m)(phi'(g))
  = rho (1-Re tr_d(phi(g))).                           (PI2)
```

Hence, whenever the denominator is positive,

```text
  ||phi'(a)phi'(b)-phi'(ab)||_(2,d+m)^2
  ---------------------------------------------------
       1-Re tr_(d+m)(phi'(g))

= ||phi(a)phi(b)-phi(ab)||_(2,d)^2
  ----------------------------------------------- .   (PI3)
       1-Re tr_d(phi(g))
```

Taking maxima over any fixed finite family of multiplication tests preserves
the identity.  Thus identity-block padding can make both normalized
Hilbert--Schmidt defects and a marked trace gap arbitrarily small, but it
cannot change their ratio.

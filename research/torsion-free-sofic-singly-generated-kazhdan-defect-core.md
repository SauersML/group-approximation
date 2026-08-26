---
rg: 2
id: torsion-free-sofic-singly-generated-kazhdan-defect-core
kind: claim
title: Construct a torsion-free finitely presented sofic Kazhdan group saturated by one compression defect
distinct_from:
  defect-saturation-full-mf-radical: That already constructs a torsion-free finitely presented Kazhdan full-radical group at the audited paper level, but does not prove the positive approximation property of soficity.
  simple-sofic-total-mf-radical: That supplies soficity and full MF radical, but not torsion-freeness, finite presentation, property (T), or a compression-defect description.
  arithmetic-single-defect-saturation: That proves the algebraic saturation implication after a routing quotient is supplied; this asks that the saturated quotient also be sofic.
artifacts:
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

Construct a finitely presented, torsion-free, sofic group `K` with property
`(T)`, a finitely generated Kazhdan subgroup `L<=K` carrying a one-sided
compression configuration, and an element `k in K` such that

```text
D_K(L) = K = <<k>>^K.                                  (TFC1)
```

Then `normal-kazhdan-defect-non-mf` gives `Rad_MF(K)=K`.  This is the exact
kernel needed by the split-cyclic target, including its preferred finite
presentation and one-element normal-generation strengthening.

The known arithmetic Hull--Osin candidate satisfies every clause of `(TFC1)`
except soficity.

## Attempts

1. **Arithmetic saturation.**  This is the live route
   `arithmetic-defect-core-via-sofic-saturation`.  The existing quotient has
   the correct presentation, torsion, Kazhdan, defect and normal-generation
   properties.  It stops only at
   `arithmetic-defect-saturated-kazhdan-group-is-sofic`.
2. **Simple sofic envelope.**  `simple-sofic-total-mf-radical` gives a
   countable simple sofic full-radical group, but the envelope theorem does
   not preserve torsion-freeness, finite presentation, or property `(T)` and
   supplies no compression pair.  It cannot currently feed `(TFC1)`.
3. **Residual-finiteness repair.**  Impossible for a nontrivial output:
   `(TFC1)` and the normal-Kazhdan theorem force full MF radical, while every
   residually finite group is MF.

This is a sufficient but stronger-than-necessary construction target.  The
direct route `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` only asks
that the cyclic extension create a defect saturating `K`; it does not require
`K` to have full MF radical on its own.

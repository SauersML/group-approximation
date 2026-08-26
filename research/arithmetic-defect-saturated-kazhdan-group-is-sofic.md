---
rg: 2
id: arithmetic-defect-saturated-kazhdan-group-is-sofic
kind: claim
title: Make the arithmetic single-defect saturated Kazhdan quotient sofic
distinct_from:
  defect-saturation-full-mf-radical: That constructs the torsion-free finitely presented property-(T) quotient and proves its full MF radical, but does not prove it sofic.
  fournier-facio-group-is-nonsofic: That concerns the separate published Fournier--Facio quotient, whose nonsoficity is part of its construction; this asks for a sofic choice of the arithmetic single-defect routing quotient.
  concrete-compression-source: That source is linear and residually finite before routing; soficity is not inherited by arbitrary quotients, so source soficity does not settle this claim.
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
---

In the arithmetic route `defect-saturation-from-arithmetic-source`, choose
the routed quotient `q:R->>Q` so that `Q` is sofic while retaining

```text
Q is two-generated, finitely presented, torsion-free and property (T),
q(sigma) != 1,
Q = <<q(sigma)>>^Q = D_Q(q(P)).                         (ADS1)
```

The existing Hull--Osin router supplies every clause except soficity.  The
fact that the source `R` is residually finite does not help formally:
quotients of sofic groups are not known to be sofic in general.

## Attempts

1. **Inherit soficity from the source.**  This dies because `Q` is a quotient
   of the residually finite group `R`, and quotient closure of soficity would
   imply that every countable group is sofic.
2. **Ask the router for residual finiteness.**  This is inconsistent with the
   rest of `(ADS1)`: the defect saturation and normal-Kazhdan theorem force
   `Rad_MF(Q)=Q`, whereas a nontrivial residually finite group is MF.
3. **Sofic-preserving marked routing.**  The remaining live approach is
   `arithmetic-defect-saturated-sofic-via-sofic-router`: construct finite
   permutation models during the marked small-cancellation routing rather
   than trying to inherit them from the quotient map afterward.

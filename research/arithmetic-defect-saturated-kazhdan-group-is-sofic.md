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
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
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
4. **Amenable-extension permanence.**  Property `(T)` makes every amenable
   quotient finite, while full MF radical kills every finite quotient.  Thus
   every amenable quotient of `Q` is trivial, and the kernel in a proposed
   sofic-by-amenable decomposition is again all of `Q`.
5. **Bass--Serre permanence.**  Property `(T)` gives property `FA`, excluding
   any nontrivial reduced amalgam or HNN decomposition.  Hull's quotient
   presentation supplies no amenable-edge splitting in any case.
6. **Exact local models.**  Since `Q` has no nontrivial finite quotient and is
   finitely presented, it cannot be LEF.  A positive proof must therefore use
   genuinely approximate, unstable permutations rather than congruence
   quotients or exact finite charts.
7. **Hull finite-ball protection.**  Hull's Theorem 7.1 makes each chosen
   quotient injective on one prescribed finite ball, but increasing that ball
   changes the quotient.  It does not produce increasingly accurate models
   of one fixed `Q`, and the theorem contains no soficity-permanence clause.

Proving this claim would answer Alekseev--Thom Open Problem 6.1 and more: the
output would be two-generated, finitely presented, torsion-free,
acylindrically hyperbolic, Kazhdan, finite-residual-full and full-MF-radical.

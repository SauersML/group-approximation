---
rg: 2
id: rf-perfect-pair-transfer-equals-regular-rcc
kind: claim
title: For residually finite perfect pairs, regular RCC is exactly full projective transfer
artifacts:
  - research/artifacts/rf-perfect-projective-rcc-audit-2026-08-30.md
distinct_from:
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that equates a full finite-matrix linear bound with exclusion of unrestricted projective ultraproduct leaks but leaves a purported trace-profile gap; this uses residual-finite tensor camouflage and perfectness to remove that gap and identify the result with regular-trace RCC.
  canonical-trace-does-not-weaken-thin-commutant-transfer: that treats ordinary qualitative commutators; this includes projective source phases, the target phase, and the dimension-free linear finite-matrix inequality.
  projective-transfer-equals-rcc-for-perfect-pairs: that compares the two qualitative statements inside one fixed trace class; this proves that the unrestricted and regular trace classes are equivalent and then recovers the finite-level modulus.
---

Let `A=<X|R>` be finitely presented and residually finite, let
`C=<S><=A`, fix `h in A` with `A=<C,h>`, and suppose that both `C` and
`A` are perfect.  For an assignment `rho:X->U(d)` and `U in U(d)` put

```text
delta(rho)=max_(r in R)||rho(r)-I||_2,
q(rho,U)=sum_(s in S)(1-|tr([U,rho(s)])|^2),
e_h(rho,U)=1-|tr([U,rho(h)])|^2.
```

The following are equivalent.

1. There is `L<infinity`, independent of `d`, such that every assignment
   and every `U` satisfy

   ```text
   e_h(rho,U) <= L(q(rho,U)+delta(rho)).                 (RPT1)
   ```

2. For every tracial matrix ultraproduct `M` and every regular-trace
   representation `pi:A->U(M)`,

   ```text
   pi(C)' cap M = pi(A)' cap M.                          (RPT2)
   ```

Thus, for a residually finite perfect pair, neither an arbitrary modulus nor
an unrestricted trace profile is stronger than regular RCC.  In particular
the theorem applies to
`SL_n(Z)<=SL_n(Z[1/p])`, `n>=3`, with the standard denominator generator.
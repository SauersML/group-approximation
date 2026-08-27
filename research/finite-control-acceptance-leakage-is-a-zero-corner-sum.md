---
rg: 2
id: finite-control-acceptance-leakage-is-a-zero-corner-sum
kind: claim
title: Strict finite-control acceptance is exactly a finite sum of selected zero-corner leakages
distinct_from:
  positive-density-hs-power-overlaps-force-finite-depth: that consumes many small returns of one positive-density head; this converts one strict head compression into finitely many off-head zero-corner coefficients.
  central-marked-two-cycle-zero-compression-cell: that groupifies one ordinary-word zero compression; this is the analytic decomposition which would feed such cells after superoperator coefficients are wordized.
  controlled-swap-wordizes-matrix-corner-without-adjoint-dilution: that converts an already ordinary matrix-corner residual to a commutator word; this identity applies first to the finite control register and does not solve the verifier's vector-to-matrix wordization.
---

Let the fixed control space have orthogonal coordinate atoms

```text
I=sum_(a in F_2^m)P_a
```

and translation unitaries `X^a` with `X^a P_0 X^a=P_a`.  For every unitary
`W` on the control space tensored with an arbitrary finite-dimensional
payload space,

```text
sum_(a!=0)||P_0 X^a W P_0||_2^2
 =tau(P_0)-||P_0 W P_0||_2^2.                          (FCL1)
```

Consequently, if the head compression has operator norm at most `rho<1`,

```text
sum_(a!=0)||P_0 X^a W P_0||_2^2
 >=(1-rho^2)tau(P_0).                                  (FCL2)
```

If an exact perfect model satisfies `WP_0=P_0`, every off-head coefficient
in `(FCL1)` is zero.  Thus a strict one-cycle acceptance gap can in principle
be consumed by finitely many selected zero-compression cells, without power
amplification or a no-return tail.

The statement is purely analytic.  In the Culf--Mastel application
`W_game` is a left--right superoperator and the distinguished input is one
tracial Gram vector.  Turning the terms in `(FCL1)` into ordinary group-word
matrix corners on a common positive-density source remains the
payload-sensitive wordization gate.


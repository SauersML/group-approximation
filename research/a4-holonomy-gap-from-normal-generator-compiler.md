---
rg: 2
id: a4-holonomy-gap-from-normal-generator-compiler
kind: route
title: Full-chart holonomy compilation plus 19243 normal generation collapses the relative frame
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-full-packet-normal-generator-holonomy-compiler
  - atlas-a8-19243-normal-generator-hs-stability
---

Let `pi_n,Q_n` be the compiler output.  The normalized-network hypotheses give

```text
eta_n -> 0,
||sigma_n(q_19243)-1||_2 -> 0.
```

By `(A4-NG-COMP-2)`,

```text
||pi_n(b)-1||_2 -> 0.
```

The established A8 normal-generator stability theorem therefore gives

```text
tr_(M_n)(1-Q_n) -> 0.
```

Substitute this and `eta_n->0` into `(A4-NG-COMP-1)`:

```text
dist_2(U_n,lambda_(k_n)(A8)') -> 0.                    (1)
```

Choose `Y_n` in the chart commutant with `||U_n-Y_n||_2->0`.  For either fixed
raw-S3 covariance generator `h` used in the holonomy target,

```text
||U_n lambda(h)-lambda(h)U_n||_2
 <= 2 ||U_n-Y_n||_2 -> 0,
```

because `Y_n` commutes with all of `A8`.  Hence both covariance coordinates
satisfy

```text
a_n^2+b_n^2 -> 0,
```

which is stronger than the required `limsup < 1/128`.  This proves the
holonomy coherence gap.

Conceptually, this route uses the full packet only to compile a finite
`A8`-valued residual state machine.  Collision `19243` then kills one normal
generator, and finite normal-generation turns that one local verifier readout
into global holonomy collapse.  No classical alignment rounding is needed.

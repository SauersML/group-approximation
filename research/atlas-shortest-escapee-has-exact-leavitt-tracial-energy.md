---
rg: 2
id: atlas-shortest-escapee-has-exact-leavitt-tracial-energy
kind: claim
title: The shortest Atlas escapee has energy eighteen in an exact full-relator Leavitt factor model
distinct_from:
  atlas-shortest-escapee-has-no-relator-telescope: that proves the two dangerous words survive the Leavitt quotient and hence have no normal-closure certificate; this evaluates their normalized Hilbert--Schmidt energies in the canonical finite factor and installs the relative chart unitary.
  atlas-six-relator-leavitt-tracial-countermodel: that gives a positive five-row additive circulation behind six phase cycles; this uses the full 4,636-word rank-five presentation and computes the inversion energy of the actual escapee st3_135_11.
  atlas-true-criterion-baseline: that computes the finite-dimensional tensor-flip start, where every control vanishes but the inversion energy is zero; this gives an infinite finite-factor endpoint where every relator vanishes but the inversion energy is eighteen.
---

**ESTABLISHED EXACT FINITE-FACTOR COUNTERMODEL.**  Let `Q` be the binary
Leavitt Atlas quotient, let `M=L(Q)` with its canonical trace, and let

```text
rho(h)=lambda_Q(i_1(h))                    (h in A8).
```

There is a unitary `W in M` such that

```text
W rho(h) W^*=lambda_Q(i_2(h))              (h in A8). (LTE1)
```

Evaluate the two-chart presentation using `rho` and this single relative
unitary `W`.  Every one of the `4,636` analytic Atlas relators is exactly the
identity, but for `w=st3_135_11` one has

```text
||[A_a,B_b]||_2^2=2,
||[A_a,B_c]||_2^2=2,
||[A_a,B_a]||_2^2=0,                                 (LTE2)
```

and therefore, using the exact multiplicities `6,3,1`,

```text
E_w(W)=6*2+3*2+1*0=18.                               (LTE3)
```

Thus the proposed control coercivity fails not merely for a freed phase
model but in an exact common-relative-unitary representation with regular
`A8` chart traces:

```text
E_w(W)=18,
sum_(s in controls)||pi_W(s)-1||_2^2=0.              (LTE4)
```

It even fails after the right side is enlarged to all `4,636` relators.

**FINITE DIMENSION IS THE ENTIRE REMAINING ISSUE.**  `(LTE4)` is a
countermodel in a finite von Neumann factor, not in a matrix algebra.  Hence
it does not by itself refute an inequality asserted only for
`U(20160 k)`.  It does prove that no argument valid in all finite tracial von
Neumann algebras -- in particular no universal tracial sum-of-squares or
`C*`-positivity certificate -- can establish that matrix inequality.

Moreover, if `Q` is hyperlinear, trace-faithful matrix microstates for the
finite set in `(LTE2)` have all relator defects tending to zero while

```text
E_w -> 18.                                            (LTE5)
```

Consequently any dimension-independent finite-matrix coercivity inequality
for this escapee would prove that `Q` is nonhyperlinear.  The analytic
endpoint is therefore already branch-selecting: it cannot be a neutral
consequence of the abstract presentation or its canonical trace.

DERIVATION
atlas-shortest-escapee-leavitt-tracial-energy-proof

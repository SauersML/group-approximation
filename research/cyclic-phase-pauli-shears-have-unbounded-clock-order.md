---
rg: 2
id: cyclic-phase-pauli-shears-have-unbounded-clock-order
kind: claim
title: Phase-corrected polynomial Pauli shears have unbounded finite clock order
artifacts:
  - experiments/cyclic_phase_pauli_clock.py
distinct_from:
  phase-inverting-fourth-root-lifts-opposite-pauli-shears: that proves the atomic two-dimensional phase correction; this proves that the same correction survives arbitrarily large cyclic Frobenius packets and does not collapse the polynomial clock to finite order.
  triangular-e5-pulses-admit-persistent-tail-character: that constructs characters negative on every E5 pulse; this constructs exact polynomial shear clocks but does not yet impose a first-hit prefix.
---

For `m>=1`, put `R_m=F_2[x]/(x^m-1)` and let

```text
ell_m(f)=[x^0]f,
B((a,b),(c,d))=ell_m(ad+bc)              on V_m=R_m^2.          (CPC1)
```

The form is nondegenerate.  Let `P_m` be the phase-Pauli group with normal
forms `(r,a,b) in Z/4 x V_m` and product

```text
(r,a,b)(s,c,d)=(r+s+2 ell_m(bc),a+c,b+d).                      (CPC2)
```

It has order `4*2^(2m)`, central fourth root `R=(1,0,0)`, and its `R=i`
spin representation has dimension `2^m`.

The opposite polynomial shears

```text
U(a,b)=(a+xb,b),                 L(a,b)=(a,b+xa)               (CPC3)
```

are symplectic involutions.  Correct every image of a Pauli basis generator
by `R` exactly when its Weyl normal form has nonzero quadratic refinement,
and send `R` to `R^-1`.  This gives involutive automorphism lifts
`U_hat,L_hat` of `P_m`.

The orders of `U_hat L_hat` are unbounded as `m` varies.  Indeed the quotient
matrix over `F_2[x]` is

```text
M=[[1+x^2,x],[x,1]].                                             (CPC4)
```

The upper-left entry of `M^n` is monic of degree `2n`, while the lower-left
entry has degree `2n-1`.  Thus `M^n!=I`.  If `m>2n`, reduction modulo
`x^m-1` cannot wrap the leading term, so the order of the quotient of
`U_hat L_hat`, and hence the order of the lift itself, is greater than `n`.

The artifact audits the complete generator presentation of both lifts.  For
`m=1,...,12` the quotient and lifted orders agree and are

```text
3, 3, 15, 6, 51, 15, 63, 12, 315, 51, 3075, 30.                (CPC5)
```

This supplies arbitrarily long exact finite phase-Clifford clocks.  The
remaining global issue is to realize their compatible universal module and
prefix-preserving packet transports inside one finitely presented group.

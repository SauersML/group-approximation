---
rg: 2
id: separate-pauli-branch-transports-do-not-carry-s4
kind: claim
title: Two exact Pauli branch transports do not transport their joint standard polynomial
distinct_from:
  first-leavitt-weyl-cell-has-exact-rectangular-model: that constructs the full first-cell rectangular model and its conditional PI floor; this isolates the precise failure of using its two separately bounded branch transports as the PI bridge.
  s4-common-holonomy-charger-is-morita-blind: that appends commuting powers of one holonomy to four packet paths; this permits two different branch conjugators and shows that entry-dependent conjugation does not carry an alternating polynomial.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that proves the analytic gap once all four returned words lie near one degree-two factor; this shows why pairwise transport does not provide that common confinement.
---

In the exact qubit rectangular model, duplicate the source Weyl pair into the
four source occurrences

```text
Xtuple=(X_src,Z_src,X_src,Z_src).
```

Transport the first pair by `U_0=1` and the second by `U_1=SWAP`.  Every
occurrence has an exact bounded branch transport to

```text
Ytuple=(X tensor 1,Z tensor 1,1 tensor X,1 tensor Z).
```

Nevertheless

```text
s4(Xtuple)=0,                    ||s4(Ytuple)||_2=8.     (SPT1)
```

The source value vanishes already by alternation because its arguments
repeat.  The target value is `8ABCD`, since the two target pairs anticommute
internally and commute across pairs.  Hence separate exact transport of the
two child packets, even on one carrier and with a fixed nonzero PI tuple,
does not transport the joint polynomial evaluation.

Standard polynomials are covariant under one common conjugation, not under
an entry-dependent family of conjugations.  The smallest surviving bridge
must therefore synchronize the four fixed occurrences through one common
almost-unitary intertwiner (or directly control the signed sum of all
transported monomials).  No mutual-bicommutant or scalar-spectator conclusion
is needed for that narrower bridge.

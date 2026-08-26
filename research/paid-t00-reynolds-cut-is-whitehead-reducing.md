---
rg: 2
id: paid-t00-reynolds-cut-is-whitehead-reducing
kind: claim
title: A 48-word paid t00 menu hits a positive cut reducing both Whiteheads
artifacts:
  - research/paid-t00-whitehead-reynolds-cut-proof.md
distinct_from:
  paid-t00-pauli-menu-hits-whitehead-constant-atom: that places one of eight Pauli conjugates on the Whitehead-fixed constant atom but its spectral high cut need not reduce the Whitehead action; this Reynolds-averages that compression and returns a positive reducing spectral cut at the cost of the six-element native S3 menu.
  native-actor-normal-closure-does-not-localize-paid-t00-support: that proves conjugating only by J1,J2 and the order-seven heads can leave the paid discrepancy pointwise trivial on the constant atom; this first uses a dual-Pauli conjugate that hits the atom and only then averages its six Whitehead translates.
  paid-t00-carrier-has-signed-hecke-reynolds-dichotomy: that gives operator-norm incidence with the actual signed Hecke source or a detector-word payment; this gives positive trace mass on a representation-dependent subcut of the equal-scale Whitehead atom and does not identify it with the signed source.
---

**ESTABLISHED WHITEHEAD-REDUCING LOCALIZATION.**  Let

```text
P=(1-z)/2,
e=P product_(m=1)^3(1+X_m)/2,
S_3=<J_1,J_2>.                                      (PWR1)
```

Thus `tau(e)=tau(P)/8`, and both literal prefix Whiteheads preserve `e`.
For the paid discrepancy `D=x_78(t_00+s_0t_00)`, let

```text
D_epsilon=u_epsilon^(-1)Du_epsilon,
C_epsilon=P(1-D_epsilon)/2                           (PWR2)
```

be the fixed eight-word Pauli menu.  By
`paid-t00-pauli-menu-hits-whitehead-constant-atom`, one `epsilon` satisfies

```text
tau(A)>=tau(P)/128,          A=eC_epsilon e.          (PWR3)
```

Reynolds-average this positive contraction over the exact native `S_3`:

```text
B=(1/6) sum_(w in S_3) wAw^(-1).                     (PWR4)
```

Then `0<=B<=e`, `tau(B)=tau(A)`, and `B` commutes with `J_1,J_2`.  Its
spectral high cut

```text
E=1_([1/32,1])(B)                                    (PWR5)
```

therefore satisfies

```text
0!=E<=e,       [E,J_1]=[E,J_2]=0,
tau(E)>=tau(P)/248.                                  (PWR6)
```

Moreover, for at least one `w in S_3`,

```text
tau(E wC_epsilon w^(-1) E)>=tau(P)/7936.             (PWR7)
```

Equivalently, one member of the fixed menu of at most `8*6=48` ordinary
conjugates

```text
D_(epsilon,w)=w u_epsilon^(-1)D u_epsilon w^(-1)     (PWR8)
```

has positive paid compression on one common reducing cut for the two actual
Whiteheads.  The finite choice may be frozen on a subsequence, and every
constant is independent of the active trace profile.

This closes the source-localization question for the equal-scale
`J_1/J_2` constant atom.  It does not type `E` as the signed Hecke source,
does not make `D_(epsilon,w)` normalize `E`, and does not identify the
quarter/eighth selector targets.  Those are separate occurrence seams.
No Property T, canonical trace, literature theorem, or local computation is
used.

DERIVATION
paid-t00-whitehead-reynolds-cut-proof

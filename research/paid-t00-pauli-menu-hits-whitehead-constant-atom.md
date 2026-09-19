---
rg: 2
id: paid-t00-pauli-menu-hits-whitehead-constant-atom
kind: claim
title: Eight native Pauli flips place one paid t00 discrepancy on the Whitehead constant atom
artifacts:
  - research/paid-t00-pauli-menu-constant-atom-proof.md
distinct_from:
  native-t00-y1-collision-pays-marked-opnorm: that puts the discrepancy on a positive part of the marked carrier without locating it in a native finite packet; this locates one of eight literal conjugates on the actual middle-index constant atom.
  middle-index-marked-heisenberg-packet-is-whitehead-equivariant: that gives the equal-mass atom decomposition and Whitehead action but no coefficient-sensitive paid operator; this inserts the paid t00 discrepancy by a finite profile-independent menu.
  binary-leavitt-arbitrary-profile-native-cross-gram: that requires the two unequal selector occurrences and their mixed gauge; this gives a paid compression on the equal-scale Whitehead atom and deliberately does not identify the quarter/eighth row.
---

**ESTABLISHED FINITE-MENU LOCALIZATION.**  On the marked carrier

```text
P=(1-z)/2
```

use the three literal middle-index Pauli pairs `(X_m,Y_m)` and their eight
`X`-character atoms

```text
e_epsilon=P product_(m=1)^3 (1+epsilon_m X_m)/2.
                                                               (PAM1)
```

Let

```text
D=x_78(t_00+s_0t_00),          C=P(1-D)/2.             (PAM2)
```

be the paid discrepancy carrier.  Then

```text
tau(C)>=tau(P)/16.                                      (PAM3)
```

For each sign vector choose the literal Pauli flip

```text
u_epsilon in <Y_1,Y_2,Y_3>
```

which carries the constant atom `e_+=e_(+,+,+)` to `e_epsilon`, and put

```text
D_epsilon=u_epsilon^(-1) D u_epsilon,
C_epsilon=P(1-D_epsilon)/2.                            (PAM4)
```

At least one member of this fixed eight-word menu satisfies

```text
tau(e_+ C_epsilon e_+)>=tau(P)/128.                    (PAM5)
```

More quantitatively, for that member the spectral projection

```text
E=1_([1/32,1])(e_+ C_epsilon e_+)                      (PAM6)
```

has

```text
tau(E)>=tau(P)/256.                                    (PAM7)
```

Both literal prefix Whiteheads preserve `e_+`.  Thus every arbitrary active
trace profile contains a positive Whitehead-fixed atom on which one literal
conjugate of the fully paid coefficient discrepancy has nonvanishing
cross-Gram mass.  The choice is among eight fixed group words and may be
made after seeing the matrix coordinate; a subsequence freezes it.

This does **not** prove the unequal native selector cross-Gram.  The two
Whiteheads have the same quarter-scale label action on `e_+`, and no relation
here says that `D_epsilon` normalizes the atom or is the controlled
quarter/eighth selector output.  The lemma removes the possibility that all
paid conjugates avoid the Whitehead constant atom; occurrence typing of the
unequal row remains open.  No Property T, canonical trace, literature input,
local computation, or Lean compilation is used.

DERIVATION
paid-t00-pauli-menu-constant-atom-proof

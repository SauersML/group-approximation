---
rg: 2
id: full-q-quarter-adjacent-profiles-have-half-cross
kind: claim
title: Both adjacent-character profiles retain one-quarter native cross-Gram energy
artifacts:
  - research/full-q-quarter-adjacent-cross-proof.md
  - experiments/full_q_quarter_native_target_audit.py
distinct_from:
  full-q-native-quarter-source-has-distinct-literal-ranges: that records the rank-one pairing-zero profile and fences equality of the two literal ranges; this includes both adjacent-character orbits and computes their full cross operators.
  full-hecke-whitehead-zero-cross-gram: that constructs a synthetic finite interface with orthogonal target sheets; this uses the actual full-parabolic quotient and its literal native Whitehead occurrences.
  binary-leavitt-arbitrary-profile-native-cross-gram: that quantifies over every finite packet multiplicity profile arising from an arbitrary norm-corona representation; this proves positivity only on the two trivial-stabilizer adjacent-character monomial profiles.
---

**ESTABLISHED SCOPED POSITIVE PROFILE.**  In each of the two exact
adjacent-character monomial representations of the complete eight-summand
parabolic packet, retain

```text
Q=e_(L_0,lambda_0),
F=Q(1+r)(1+l)/4,
r=x_58(a_2),                 l=x_69(a_3),
T_1=J_1F,                    T_2=J_2F.                 (QAC1)
```

The two character orbits are indexed by the invariant pairing
`epsilon in {0,1}`.  Their exact ranks and cross operators are

```text
epsilon     rank(Q)     rank(F)     T_1^*T_2 on F
   0            4           1            (1/2) I_F
   1           12           3            (1/2) I_F.   (QAC2)
```

Consequently both profiles satisfy

```text
tr(T_1^*T_2T_2^*T_1)=(1/4)tr(F).                      (QAC3)
```

In both profiles the two literal range projections have zero projection
meet even though `(QAC3)` is positive.  Thus the positive moment comes from
the angle between distinct native ranges, not from a common literal range.

This result does **not** prove
`binary-leavitt-arbitrary-profile-native-cross-gram`.  The two monomial
models use the trivial representation of each adjacent-character
stabilizer.  An arbitrary exact finite packet representation can carry a
nontrivial stabilizer multiplicity type, and the present calculation does
not show that its finite Hecke path sum remains bounded below.  In
particular `(QAC2)` cannot be promoted to an arbitrary norm-corona profile
by inserting regular or canonical multiplicities.

No Property `(T)`, canonical-trace replacement, local computation, or
literature theorem is used.  The finite calculation was run only through
the MSI wrapper.

DERIVATION
full-q-quarter-adjacent-cross-proof

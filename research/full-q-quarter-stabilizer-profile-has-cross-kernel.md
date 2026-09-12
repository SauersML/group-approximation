---
rg: 2
id: full-q-quarter-stabilizer-profile-has-cross-kernel
kind: claim
title: A nontrivial adjacent-character stabilizer profile retains a native cross kernel
artifacts:
  - research/full-q-quarter-stabilizer-cross-kernel-proof.md
  - experiments/full_q_quarter_stabilizer_permutation_audit.py
distinct_from:
  full-q-quarter-adjacent-profiles-have-half-cross: that computes scalar fiber profiles where the native cross operator is one half of a unitary; this adds a nontrivial stabilizer fiber and obtains a genuine kernel.
  binary-leavitt-arbitrary-profile-native-cross-gram: that asks only for a positive normalized-HS cross-Gram mass floor; the present profile still has relative energy seven fortieths and therefore does not refute that claim.
---

**ESTABLISHED FULL-SOURCE DESCENT FENCE.**  Use the pairing-one
vector/covector character orbit of the exact five-node Levi packet.  Its
stabilizer is `GL_4(F_2)`.  Its permutation representation on the `15`
nonzero vectors of the natural four-space is two-transitive, hence splits
as the trivial representation plus an irreducible `14`-dimensional
zero-sum constituent.  Induce this nontrivial constituent.

Compute first in the exact `496*15=7440` dimensional permutation-fiber
representation and then restrict to its invariant
`496*14=6944` dimensional zero-sum summand.  Retain the literal full source
and native quarter cut

```text
Q=e_(L_0,lambda_0),
F=Q(1+r)(1+l)/4,
T_1=J_1F,                    T_2=J_2F.                 (QSK1)
```

The exact ranks on this irreducible stabilizer profile are

```text
rank(Q)=120,                 rank(F)=30,
rank(T_1^*T_2)=24.                                      (QSK2)
```

Thus the literal native cross operator has a six-dimensional kernel on
`F`.  In particular, the complete full-parabolic packet does not imply
that `T_1^*T_2` is bounded below on all of `F`, and it does not justify a
full-source polar inverse.

The normalized-Hilbert--Schmidt moment is nevertheless positive:

```text
Tr_F(T_1^*T_2T_2^*T_1)=21/4,
(1/rank(F))Tr_F(T_1^*T_2T_2^*T_1)=7/40.               (QSK3)
```

Therefore this profile is **not** a counterexample to `(APG1)` of
`binary-leavitt-arbitrary-profile-native-cross-gram`.  It rules out only
the stronger shortcut which asks the quarter-source cross operator to be
injective or uniformly bounded below on its full source.  A valid APG1
proof may still spectral-cut the positive part, but must prove a
profile-uniform lower bound for its mass.

No Property `(T)`, canonical-trace substitution, local computation, or
literature theorem is used.  The finite audit was run only through the MSI
wrapper.

DERIVATION
full-q-quarter-stabilizer-cross-kernel-proof

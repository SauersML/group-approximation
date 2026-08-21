---
rg: 2
id: mixed-cnot-allowed-active-return
kind: claim
title: Return the complement of the joint mixed-CNOT exit as one approximately reducing active carrier
distinct_from:
  projected-hard-sign-bridge-selects-joint-exit: that sends the analytically compressed joint exit to a first-hit layer; this must retain its complement for the next corner-localized BCS application.
  mixed-central-cnot-completes-relative-rank-one-router: that routes the two flag halves on `K=-1`; this must also retain the allowed `K=+1,b=-1` sector without a scalar controlled word.
---

For the six-generator `S_3` replacement of the mixed router on the marked
carrier, let

```text
X=QF(I-b)/2,             A=Q-X.                        (MAR1)
```

Put a complete gauge-doubled Fanizza occurrence at every site of the free
Thompson occurrence amalgam.  In each occurrence use the endpoint packet of
`s3-active-complement-is-three-equal-scale-affine-atoms`, so

```text
A=P_(+,+)+P_(+,-)+P_(-,+),       X=P_(-,-).            (MAR2)
```

Adjoin an HNN edge carrying the three endpoint generators `(J,K,b)` of one
occurrence to those of the next.  By
`s3-affine-hnn-transports-the-active-vector`, it carries `A` to the next
analytic active carrier `A'` with fixed normalized-HS loss.  The atom
`P_(+,-)` is included, so every allowed `K=+1,b=-1` character returns exactly.

By `packet-central-active-complement-reduces-shared-words`, `A'`
approximately reduces the next occurrence's original shared BCS words.  The
free occurrence amalgam imposes no commutation between the old and fresh
logical tuples, and Britton embedding preserves the marked base.

The exit component `X` no longer belongs to this target:
`projected-hard-sign-bridge-selects-joint-exit` transports it directly to the
correct E5 first-hit layer using `b` as the hard word and `X` only as an
analytic right compression.

The HNN edge also carries `X` to the fresh inactive atom `X'`.  This does not
invalidate the branching/first-hit ledger: the next active mass is defined by
`A'`, while the independently transported copy of `X` has already entered the
orthogonal Thompson first-hit reservoir.  The ledger requires

```text
2q_n<=q_(n+1)+r_n+error,
```

not that every other image of the exit vanish algebraically.  Ordinary HNN
transport supplies no contraction and is not credited with one; persistence
comes from the one-active-plus-one-exit balance in
`branching-plus-first-hit-exits-forces-hs-floor`.

## Fences retained

- The internal mixed-packet automorphism group has order four and supplies
  only identity and shear on `span{b,d}`.  There is no third internal endpoint
  chart to finish this return.
- Sending every `b=-1` sector to the E5 boundary proves the exit lower bound
  after compression by `X`, but it cannot define the next active carrier:
  allowed `K=+1,b=-1` mass has no first-detection character and may recur.
- The direct commutator bound for the analytic complement is supplied by
  `packet-central-active-complement-reduces-shared-words`.
- A finite graph of HNN charts still has a stationary regular flow and cannot
  prove the separate Schur contraction theorem.  The present route instead
  uses the already established branching-plus-first-hit ledger; it must not be
  cited for `schur-violation-density-gives-contraction`.
- The four-child context batch gives a different escape from this target:
  send all three contextual failures to three grandchildren and reserve the
  fourth as active.  This bypass is tracked by
  `mixed-cnot-joint-exit-via-four-child-context-batch`; it does not assert the
  stronger complement-return statement here.

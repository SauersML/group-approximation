---
rg: 2
id: mixed-cnot-allowed-active-return
kind: claim
title: Return the complement of the joint mixed-CNOT exit as one approximately reducing active carrier
distinct_from:
  projected-hard-sign-bridge-selects-joint-exit: that sends the analytically compressed joint exit to a first-hit layer; this must retain its complement for the next corner-localized BCS application.
  mixed-central-cnot-completes-relative-rank-one-router: that routes the two flag halves on `K=-1`; this must also retain the allowed `K=+1,b=-1` sector without a scalar controlled word.
---

For the mixed router on the marked carrier, let

```text
X=QF(I-b)/2,             A=Q-X.                        (MAR1)
```

Construct a finite group-word return, compatible with the next Fanizza clock
level, whose active carrier differs from `A` by at most polynomial
normalized-HS loss, approximately reduces the original shared BCS words, and
preserves the two-child trace balance.  The construction must admit an exact
extension of every allowed `K=+1` packet character, including `b=-1`.

The exit component `X` no longer belongs to this target:
`projected-hard-sign-bridge-selects-joint-exit` transports it directly to the
correct E5 first-hit layer using `b` as the hard word and `X` only as an
analytic right compression.

The remaining difficulty is therefore one-sided.  It is not necessary to
make a group word recognize `X`; it is necessary to show that deleting the
already-accounted-for projection `X` leaves a coherent next-level carrier.
A direct spectral complement is insufficient unless its commutators with all
shared BCS words are controlled.  A relation forcing `b=+1` on `K=+1` is
also invalid, because it deletes an allowed radical character.

## Attempts

- The internal mixed-packet automorphism group has order four and supplies
  only identity and shear on `span{b,d}`.  There is no third internal endpoint
  chart to finish this return.
- Sending every `b=-1` sector to the E5 boundary proves the exit lower bound
  after compression by `X`, but it cannot define the next active carrier:
  allowed `K=+1,b=-1` mass has no first-detection character and may recur.
- The live options are an E5-provided third chart or a direct commutator bound
  for the analytic complement `A` against the original shared Fanizza words.
- `six-generator-one-jump-router-has-s3-radical-atlas` now supplies a third
  finite-packet option: its marked rank jumps by one and its `S_3` symmetry is
  transitive on all three nonzero allowed radical endpoint signs.  The exact
  remaining estimate is
  `s3-radical-atlas-returns-allowed-active-carrier`.
- The four-child context batch gives a different escape from this target:
  send all three contextual failures to three grandchildren and reserve the
  fourth as active.  This bypass is tracked by
  `mixed-cnot-joint-exit-via-four-child-context-batch`; it does not assert the
  stronger complement-return statement here.

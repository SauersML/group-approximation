---
rg: 2
id: projective-atlas-cannot-orient-transverse-branch-phase
kind: claim
title: A projective Atlas frame cannot orient the transverse branch phase
distinct_from:
  transverse-companion-defects-pay-one-kill-completeness: that proves aggregate payment and the abstract selector split; this shows collision 19243 in the current Schur interface is exactly blind to that selector.
  branch-flip-pauli-extraction-cancels-schur-surplus: that analyzes promotion of the branch flip into the returned finite packet; this identifies why the projective Atlas alternative cannot orient it either.
  kazhdan-and-transverse-packets-cannot-orient-clifford-twist: that gives a general spectator-sign countermodel for covariance packets; this computes the exact i-phase symmetry of the D8 ledger and PGL Atlas route.
---

# A projective Atlas frame cannot orient the transverse branch phase

ESTABLISHED. In the binary Schur head, the only relative datum between the
two faithful child embeddings is

```text
[W] in PGL(M),                                            (PAT1)
```

as proved by `binary-schur-head-embeddings-are-relative-inner-holonomies`.
The current `binary-schur-branch-payment-via-19243-holonomy` route installs
the Atlas packet and collision in this relative **inner** frame. Every chart
generator is read through `Ad(W)`, so for every scalar phase `lambda`,

```text
Ad(lambda W)=Ad(W).                                       (PAT2)
```

In particular all thirty A4 packet defects, the four rectangle holonomies
after projective gauge fixing, and collision `q_19243` are unchanged by

```text
W -> iW.                                                  (PAT3)
```

The transverse D8 ledger has the opposite symmetry. For

```text
S(W)=(W+W^*)/2,       T(W)=(W-W^*)/2,
```

one has

```text
S(iW)=iT(W),          T(iW)=iS(W),                        (PAT4)
D_T(iW)=D_S(W),       D_S(iW)=D_T(W).                     (PAT5)
```

Thus any estimate derived only from the projective Atlas frame and collision
19243 is invariant under an operation which swaps the proposed paid and
retained branches. It may give a symmetric total-energy obstruction, but it
cannot imply an oriented one-exit inequality selecting one fixed child.

The direct-sum selector is invisible for the same reason. Amplify any Atlas
frame by two identical multiplicity copies and use `W` on one, `iW` on the
other. All Atlas/collision data are blockwise identical by `(PAT2)`, while the
two D8 ledgers are complementary by `(PAT5)`. At the scalar endpoints,
`W=I` makes the S return exact and `W=iI` makes the T return exact, giving the
zero-selected-defect split whenever the remaining relations add no odd phase
readout.

There are only two ways for the existing lanes to see this phase.

1. Add an occurrence of the raw return implementer with odd total exponent,
   or another phase-sensitive word tied to the payload. This is not present
   in a PGL/inner-frame Atlas compiler.
2. Promote the branch flip into the returned Pauli packet. But
   `branch-flip-pauli-extraction-cancels-schur-surplus` proves that this
   recombines the child lines into one `M_2` spin and leaves one stationary
   multiplicity ray; the surplus needed for an exit is consumed.

Therefore collision 19243 does not prohibit the `M_T direct_sum M_S`
selector split in its currently stated projective-frame route. To exploit
`D_T+D_S=I`, the compiler must expose a phase-sensitive lift of the
projective frame **without** adjoining the full branch-flip Pauli algebra,
and couple that lift to the same payload carrier. This is strictly stronger
than the present four-holonomy Atlas gap.

The minimal required lift is now explicit:
`central-square-orients-transverse-ledger` proves that a
named representative with the ordinary relation `W^2=J` pins the branch to
the payload central sign, with sharp dimension-free HS constants, and does
not generate the branch-flip `M_2`.  Thus the remaining Atlas issue is exactly
to expose one raw holonomy representative on the payload carrier rather than
only its projective inner action.

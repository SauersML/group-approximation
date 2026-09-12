---
rg: 2
id: fanizza-signal-involution-is-native-mark
kind: claim
title: The Fanizza signal involution is a correctly oriented native mark for a group-level triviality diagonal
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
distinct_from:
  fanizza-nonmember-signal-is-not-a-separated-mark: that correctly rules out using positive nonmember signal mass in the older Boone orientation; this uses nonmember vanishing as soundness and membership positivity as mark survival in the reverse Kleene diagonal.
  self-referential-bcs-nonzero-signal-collapse: that first diagonalizes inside the star-algebra to prove its projection algebraically nonzero; this retains the whole computable family and postpones the diagonal until after groupification.
---

Take the Fanizza `L`-family for `L=HALT`, and write

```text
D_m=(1-x_(D,m))/2.
```

The same named involution has the two alternatives required by
`kleene-halting-mark-collapse-diagonal`, provided a groupification retains
the original BCS representation and its approximate Bob observable:

```text
m halts
  => some BCS GNS representation has pi(x_(D,m))!=I;              (NSM1)

m does not halt
  => every epsilon-perfect strategy satisfies
     ||X_(D,m)-I||_(2,phi)^2 <= 4 C_m epsilon.                    (NSM2)
```

Thus no separate Boone word has to feed positive mass into `D_m`.  The
nonmember identity `phi(D_m)=0` is exactly the desired word-collapse side,
not an obstruction, once the fixed point enumerates a proof that
`x_(D,m)=1` rather than searching for a separated microstate.

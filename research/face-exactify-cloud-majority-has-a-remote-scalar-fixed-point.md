---
rg: 2
id: face-exactify-cloud-majority-has-a-remote-scalar-fixed-point
kind: claim
title: Face exactification followed by cloud majority has a remote scalar fixed point
distinct_from:
  balanced-overlay-local-alternating-projections-contract: that proves contraction inside a fixed operator tube; this gives an explicit fixed point outside the tube even for the balanced original-plus-pair-sum overlay.
  parity-charge-or-green-divergence-has-strict-descent: that permits a parity-aware choice of update or a cross-term Lyapunov; this rules out deriving its sparse branch merely from local nearest-face exactification followed by coordinatewise equality projection.
  sparse-clifford-cycles-refute-average-commutator-rounding: that is a noncommutative growing-length obstruction; this is a three-coordinate scalar obstruction caused only by incoherent nearest-face tie choices.
---

ESTABLISHED SHARP ALGORITHM FENCE.  Consider the length-three repetition
code with original parity rows

```text
 h_12=(1,1,0),       h_23=(0,1,1),
```

and redundant pair-sum row `h_13=(1,0,1)`.  Balance the overlay by taking
two indexed copies of each original row and one pair-sum row.  There is a
legitimate nearest-face metric projection `Pi_A` and the usual
coordinatewise equality-cloud majority/sign projection `Pi_B` for which

```text
 Pi_B Pi_A(w)=w,       w=(1,0,0),                       (FCM1)
```

although `w` is not a codeword and has relative Hamming distance `1/3`
from the exact shared code variety.

Thus even the balanced pair-sum geometry does not make **every** sweep of
nearest fixed-face exactification and equality sign rounding a global
contraction.  The Loewner correction bound controls the price of a selected
local repair but does not coordinate its degenerate nearest-point choices
across clouds.  Any proof of
`parity-charge-or-green-divergence-has-strict-descent` must prescribe a
coherent parity-aware repair, use a strict Lyapunov cross term, or first
enter the established local operator tube.

This is an algorithmic no-go, not a counterexample to the desired group
stability theorem: another choice of nearest face corrections sends `w`
directly toward `000`, and the displayed fixed point has constant scalar
syndrome energy, so the common outlier mechanism can quarantine it.

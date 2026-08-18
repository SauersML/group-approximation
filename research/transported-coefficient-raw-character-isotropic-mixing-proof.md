---
rg: 2
id: transported-coefficient-raw-character-isotropic-mixing-proof
kind: route
title: Thirty-two exact rational Leavitt-prefix contractions give the two isotropic block tables
target: transported-coefficient-raw-character-isotropic-mixing
requires: []
artifacts:
  - experiments/atlas_transported_coefficient_raw_character_mixing.py
  - experiments/atlas-transported-coefficient-raw-character-mixing.json
---

The experiment reconstructs the exact raw two-sheet coefficient packet used by
`atlas_double_pauli_comb_blocks.py`: the two commuting coefficient involutions
`B_0,B_1`, their four joint character cuts `F_epsilon`, and the comb
transport.  All group elements remain exact binary Leavitt-prefix matrices and
all group-algebra coefficients are rational.

For each `i in {0,1}` and each of the sixteen ordered character pairs, it
reduces

```text
F_epsilon (comb^* B_i comb) F_delta (comb^* B_i comb)
```

exactly in the rational group algebra and takes the canonical group trace.
The 32 independently evaluated contractions are checked against the closed
forms

```text
(20 I + J)/256,   (4 I + J)/128.
```

The checked JSON freezes every entry.  The script parallelizes the independent
normal-form contractions only for runtime; there is no floating-point or
sampling step.  Finally, the row sums and centered eigenvalues are rational
arithmetic: multiplying by `8=1/tau(F_epsilon)` gives survival masses `3/4`
and `1/2`, and subtracting one normalized off-diagonal entry from the diagonal
entry gives centered factors `5/8` and `1/4`.

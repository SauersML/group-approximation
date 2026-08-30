---
rg: 2
id: atlas-three-mode-balanced-area-collector-proof
kind: route
title: Partition the exact expansion by its first rank-one reset
target: atlas-three-mode-balanced-area-sparse-collector
requires:
  - atlas-rank-five-complete-packet-exporter
  - atlas-three-label-mode-two-unitary-moment-reduction
artifacts:
  - experiments/atlas_three_mode_balanced_area.py
  - experiments/atlas-rank5-balanced-area.json
  - experiments/verify_atlas_rank5_balanced_area.py
---

Expand every controlled occurrence using

```text
U = E tensor 1 + ((I+W)/2-E) tensor S + ((I-W)/2) tensor D.
```

The six summands are represented exactly, including their dyadic scalar.  A
term with no `E` is a single affine permutation `L_g W^epsilon`.  Its
normalized trace is exact: for `epsilon=0` it is nonzero only at `g=1`; for
`epsilon=1` the script exhausts all `2^16` binary matrices, retains precisely
the 20,160 invertible ones, and counts the fixed points of the twisted affine
permutation.

For a term containing `E`, choose its first `E` in the original cyclic word
order and rotate the trace to that occurrence.  This partitions the expansion
terms: the slots before the distinguished occurrence are required to be
non-`E`, while later slots may reset again.  Between consecutive resets the
product is one affine permutation.  Since `E` projects onto the identity
label and `W` fixes that label, the segment survives exactly when its
translation part is the identity; each surviving reset contributes the exact
factor `1/20160`.  Hence no expansion term is omitted or counted twice.

In parallel, multiplication in the relation `S D=t D S` gives

```text
(t^A S^a D^b)(t^C S^c D^d)
  = t^(A+C-bc) S^(a+c) D^(b+d).
```

The collector stores this integer triple and exact rational coefficient.
Exponent pruning is sound because the remaining left and right controlled
slots bound all possible positive and negative corrections to `a` and `b`.
Only terminal states with `a=b=0` contribute to the Laurent row.  The state
cap is also sound: crossing it aborts before allocating or emitting anything;
it never discards a state.

The five exact controls cover the empty word, a nonidentity word in either
chart, the second-chart identity, and second-chart cancellation.  Finally,
ordinary polynomial Euclid over `Q` computes the incremental gcd of the
shifted `f_s(t)-1` rows and verifies the exported Bezout combination before
emission.  `verify_atlas_rank5_balanced_area.py` independently binds an
artifact to the reconstructed packet and replays that rational certificate;
with `--recompute-row` it also reconstructs the archived sparse row from its
literal source word.  This proves the claimed capped exact collector and
certificate format.

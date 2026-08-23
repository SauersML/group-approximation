---
rg: 2
id: weighted-code-character-hash
kind: claim
title: A logarithmic random coordinate hash separates all but a prescribed weighted character boundary
distinct_from:
  sequential-character-recentering-has-decision-tree-loss: that lower-bounds exact identification of every character by an adaptive binary tree; this keeps only a weighted unresolved-pair tail and has no dependence on the number of characters
  code-distance-upgrades-pair-energy-to-full-pinching: that uses all coordinates of an already commuting code PVM; this selects a short coordinate hash before global PVM alignment
---

Let `D` be any finite multiset of binary codewords of relative distance at
least `delta`.  Give every ordered pair of distinct labels `(a,b)` an
arbitrary weight `w_(a,b)>=0`, and give every coordinate `k` an arbitrary
cost `r_k>=0`.  Put

```text
W=sum_(a!=b)w_(a,b),          r_bar=(1/L)sum_k r_k.
```

For every integer `t>=1`, there is a sequence of coordinates
`K=(k_1,...,k_t)` such that

```text
sum_(a!=b : c_a|K=c_b|K) w_(a,b)
 <=2(1-delta)^t W,                                      (RCH1)

sum_(s=1)^t r_(k_s)<=2t r_bar.                          (RCH2)
```

In particular, `t=O_delta(log(1/eta))` leaves at most `eta W` unresolved
weighted boundary while spending only `O_delta(log(1/eta))` times the
average coordinate cost.  The bounds are independent of `|D|`, character
multiplicities, and matrix dimension.

For a terminal character PVM `(f_a)`, one may take

```text
w_(a,b)=(1/L)sum_i||f_aQ_if_b||_2^2,
r_k=(1/L)sum_i||[Q_k,Q_i]||_2^2.                        (RCH3)
```

Then `(RCH1)` is exactly the off-diagonal generator mass left between
distinct character atoms which the sampled coordinate signs fail to
separate, while `(RCH2)` is the complete-pair row budget needed to align the
sampled spectral cuts.

## Attempts

Exact character identification incurs logarithmic decision-tree depth.
The weighted HS objective does not require exact identification: distinct
labels which carry negligible off-diagonal generator mass may remain merged.
Random hashing exploits precisely this relaxation.  What remains is to turn
the sampled, only approximately commuting raw reflections into a joint PVM
which realizes this terminal character hash modulo simultaneous conjugacy.

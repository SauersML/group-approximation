---
rg: 2
id: outside-prefix-contractions-reduce-exterior-kernels
kind: route
title: Use two outside-prefix contractions to eliminate nonperiodic support
target: two-sided-exterior-kernels-must-be-periodic-and-asymmetric
requires:
  - two-sided-deletion-corrections-pass-natural-kernel-test
artifacts:
  - research/artifacts/kaplansky-exterior-kernels-reduce-to-pure-periodic-tails-2026-09-08.md
---

Choose a tail xi of maximum aperiodic height or maximum positive
preperiod depth in the union of both tensor supports. Both 0xi
and 1xi are outside that union. Contracting the full target at
0xi gives an invertible weighted b-character matrix applied to
the xi columns, so those columns vanish. Contracting at 1xi
then gives an injective weighted H_z-character matrix applied
to the xi rows, so those rows vanish too. The diagonal exterior
terms are checked explicitly. This contradicts xi's presence
and leaves only purely periodic tails.

On periodic cores, the wrong-prefix 0 contraction kills columns
with preceding bit one. The wrong-prefix 1 contraction gives
M_H times the row plus M_b(z) times the column equal to zero
at every remaining tail. If X and Y are individually symmetric,
rows equal columns and the sum of these matrices is a weighted
copy of the invertible natural matrix a. All rows therefore
vanish. General asymmetric periodic tensors are not eliminated
by this argument.

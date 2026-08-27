---
rg: 2
id: dimension-kleene-threshold-envelope-proof
kind: route
title: Compare the self-search window with the tensor-amplified defect profile
target: dimension-kleene-threshold-needs-amplification-envelope
requires: []
---

For a `d`-dimensional tuple `U`, the tuple `U tensor I_k` has dimension `kd`
and exactly the same normalized-HS value on every relator and on the marked
word.  Hence a search allowed to amplify `U` enters a soundness window at some
multiple precisely when its defect is below `Delta(d)` in `(DKE1)`.  This
proves the necessary crossing condition `(DKE2)`.

Assume `(DKE3)` and write its positive infimum as `rho`.  A hyperlinear
canonical microstate sequence eventually has defect below `rho/2` and marked
distance above the fixed cutoff.  For its dimension `d`, the definition of
the supremum gives a `k` with `delta(kd)>rho/2`.  The dovetailed effective
search over tuples and `k` therefore finds the amplified witness and outputs
`kd`.  The usual halting-soundness contradiction applies.

For the failure statement, `exp(-kd)<=exp(-d)<=1/d` for all positive integers
`d,k`.  Therefore the profile `(DKE4)` approaches zero but never satisfies a
single amplified strict window.  Since the ordinary hyperlinearity premise
used in the Kleene proof supplies no rate relating defect to dimension, it
cannot rule out this numerical behavior.  Pointwise positivity of the
reported threshold therefore cannot replace a positive amplification
envelope.

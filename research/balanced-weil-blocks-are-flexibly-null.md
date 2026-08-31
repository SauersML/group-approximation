---
rg: 2
id: balanced-weil-blocks-are-flexibly-null
kind: claim
title: Every balanced Weil block amplification is flexibly null
distinct_from:
  regular-iwahori-strict-congruence-exactification-is-false: that proves a fixed positive distance from every same-dimensional endpoint for one balanced block; this proves that arbitrary orthogonal amplifications of those blocks are always repaired by asymptotically negligible padding when their defect vanishes.
  direct-sum-weil-compressions-have-quadratic-padding: that treats the positive-central compressed even packets; this adds the exact negative-central odd packets needed for the regular SL2 trace and tracks the resulting flexible endpoint.
  weil-reservoir-mixing-has-energy-paid-completion: that proves the energy-paid completion after an arbitrary mixed positive even-Weil reservoir has been authenticated; this adds the negative-central balance and proves regular SL2 trace for the post-torsion strict-counterpacket amplification.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for energy-paid completion of arbitrary cross-packet mixtures; this closes only the block-diagonal balanced Weil family.
---

For every finite multiset of primes `p_j=5 mod 8`, put
`d_j=(p_j-1)/2`.  Let `C_(p_j)` be the torsion-normalized compressed
even-Weil vertex pair on dimension `d_j`, and let `O_(p_j)` be the exact
odd-Weil endpoint on dimension `d_j`.  Form the balanced pair

```text
Phi = direct_sum_j (C_(p_j) direct_sum O_(p_j)),
N = 2 sum_j d_j,                 K = number of blocks.    (BWF1)
```

In the exact `C_2*C_3*C_3` torsion frame, let `u,v` be the two remaining
structural words and use unnormalized Frobenius norm.  Set

```text
E(Phi) = sum_j (
  ||C_(p_j)(u)-1||_F^2 + ||C_(p_j)(v)-1||_F^2
),
epsilon(Phi)^2 = E(Phi)/N.                              (BWF2)
```

The fixed square-free/Tietze coordinate changes compare `epsilon(Phi)` with
the original Iwahori local defect by universal constants, independent of all
primes and multiplicities.  Then

```text
K/N <= (23/2) epsilon(Phi)^2.                           (BWF3)
```

Adding exactly one positive-central line to each block produces the genuine
endpoint

```text
Pi = direct_sum_j (E_(p_j) direct_sum O_(p_j))
```

on dimension `N+K`, where `E_p` is the full even-Weil representation.
There is a universal constant `C`, for the fixed presentation generators,
such that

```text
(N+K)/N - 1 <= (23/2) epsilon(Phi)^2,
d_2^gen(Phi,Pi) <= C epsilon(Phi).                      (BWF4)
```

Consequently no orthogonal direct sum, repeated-block amplification, or
tensor multiplicity amplification of the balanced strict counterpacket can
refute Dogon--Vigdorovich's flexible question.  If its normalized defect
tends to zero, the displayed completion uses `o(N)` added dimensions and is
at generalized Hilbert--Schmidt distance `o(1)`.

The central-sector balance does not change this conclusion.  Before
completion the positive and negative sectors both have dimension
`sum_j d_j`, so the normalized trace of `-I` is exactly zero.  After
completion it is `K/(N+K)`, which tends to zero by `(BWF3)`.  If the
least occupied prime tends to infinity, the usual Weil character estimate
also makes every fixed noncentral trace tend to zero.  Thus these are
regular-character microstates and their explicit flexible completions remain
regular-character asymptotically.

This theorem does not control a common involution which genuinely mixes
different Weil levels before the block labels are authenticated.  Such
cross-level boundary recycling is exactly the surviving enemy in
`bs14-flexible-cross-packet-boundary-reconciliation`.

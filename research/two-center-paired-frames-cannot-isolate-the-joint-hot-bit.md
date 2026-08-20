---
rg: 2
id: two-center-paired-frames-cannot-isolate-the-joint-hot-bit
kind: claim
title: Two commutator coordinates cannot isolate one Pauli bit at the joint-hot atom
artifacts:
  - experiments/rank_one_context_frame_search.py
distinct_from:
  two-by-two-support-compiler-has-unique-fixed-pivot: that constrains affine rank matrices with fixed pivots; this constrains isomorphic paired-frame presentations after a relative Pauli pair has already been named.
  rank-one-no-signaling-pairing-floor: that gives a probabilistic floor after one shared bit has been exposed; this proves why two symbolic commutator coordinates cannot build the required exposing frame.
---

Let `F,B,B'` be alternating forms on one binary vector space, with `F` fixed,
and consider the two symbolic commutator maps

```text
Phi_B (omega)=(F(omega),B(omega)),
Phi_B'(omega)=(F(omega),B'(omega)).                    (TCF1)
```

Suppose the two paired frames have the same relation kernel,

```text
ker Phi_B=ker Phi_B',                                  (TCF2)
```

and their singleton coefficient ranks agree:

```text
rank B=rank B'.                                        (TCF3)
```

Then their joint-hot ranks also agree:

```text
rank(F+B)=rank(F+B').                                  (TCF4)
```

Hence an isomorphic-edge construction with only two symbolic commutator
coordinates cannot agree at endpoint labels `00,10,01` and gain exactly one
Pauli factor at `11`.  At least a third central commutator coordinate is
necessary.

The exhaustive four-generator audit checked every one of the `2^16`
coefficient word matrices.  It found 26 relation-kernel classes and no pair
with the forbidden profile, in agreement with `(TCF4)`.  This explains why a
named Schur pair alone is insufficient and why the successful paired frame
must retain one baseline Pauli pair as well.

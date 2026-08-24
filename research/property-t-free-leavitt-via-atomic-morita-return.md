---
rg: 2
id: property-t-free-leavitt-via-atomic-morita-return
kind: route
title: Return one coefficient cell to the root atom, apply the one-third gap, and saturate
target: property-t-free-leavitt-full-mf-radical
requires:
  - binary-leavitt-atomic-morita-return
  - atomic-morita-return-kills-finite-order-mf-mark
  - full-leavitt-idempotent-defect-saturation
---

Let a norm-matrix-corona representation of
`St_20(L_(F_2)(1,2))` retain the distinguished root
`z=x_13(s_1t_1)`.  Its rounded nontrivial spectral projection is nonzero on
an infinite coordinate subsequence.  Binary Atomic Morita Return produces
the two diagonal inverse rows and completeness row on that very projection.

The atomic corner gap gives a lower bound `1` on the sum of the three
defects, whereas AMR makes the sum tend to zero.  Hence every corona
representation kills `z`.  The established root commutator saturation puts
every root subgroup in `<<z>>`, so `z` normally generates the rank-twenty
Steinberg group and its MF radical is the whole group.

This route uses neither the positive-density torsion reblocking of the
corona-module/HS routes nor the common `M_2`/`M_4` packet identity and return
row of the selector route.  Its one unresolved input is the prescribed-atom
coefficient return itself.


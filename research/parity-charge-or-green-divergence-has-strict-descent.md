---
rg: 2
id: parity-charge-or-green-divergence-has-strict-descent
kind: claim
title: Parity charge or Green divergence gives one strict joint descent step
distinct_from:
  parity-charged-green-edge-curl-coercivity: that proves the one-sided charge inequality E_edge at most C times divergence plus sparse syndrome; this must turn the charged alternative into actual descent.
  sparse-face-row-square-survives-intrinsic-green-step: that bounds the second-order sparse damage after a dense step and the cost of re-exactification; this requires a fixed first-order gain in either the dense or sparse branch.
  balanced-overlay-local-alternating-projections-contract: that contracts inside a previously identified operator-norm tube; this must work in the retained row-square basin before such a base point is known.
---

OPEN.  On the retained pointwise low-odd-square block, construct one
dimension-independent update, or a two-branch choice of updates, satisfying

```text
 E_dense,new+lambda E_sparse,new
 <=(1-c)(E_dense+lambda E_sparse)
   +C E^(3/2)+C epsilon_inv,                            (PCD1)
```

for fixed `c,lambda>0`.  Here `E_sparse` is the balanced parity/equality
charge in `(PCG1)` and `E_dense` is complete-pair energy.

Equivalently, it is enough to prove a quantitative dichotomy:

1. if `E_sparse<=theta E_edge`, then `(PCG1)` forces
   `E_div>=c_0 E_edge`, so the damped Green step decreases the dense layer;
2. otherwise, a face/equality synchronization step decreases
   `E_sparse` by a fixed fraction while increasing `E_dense` by less than
   that decrease.

## Attempts

`parity-charged-green-edge-curl-coercivity` proves the needed implication
in branch 1 after choosing `theta` small.  It does not prove branch 2:
`E_edge<=C E_sparse` is compatible with zero divergence and comparable
positive edge and sparse energies.  Likewise,
`fixed-parity-faces-exactify-with-loewner-row-square-control` gives an
operator-order **cost** bound for making each local face exact, but not a
strict decrease of equality-cloud disagreement; separately exact faces can
move their shared marginals apart again.  Invoking local alternating
projections is circular outside its operator-norm tube.

A valid proof must exploit the normalized equality channel gap to obtain a
strict sparse decrease, or exhibit a Lyapunov cross term whose decrease
pays the equality movement.  Merely adding the nonnegative divergence term
to `(PCG2)` cannot establish `(PCD1)`.

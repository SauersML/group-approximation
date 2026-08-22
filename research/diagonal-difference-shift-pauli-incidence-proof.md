---
rg: 2
id: diagonal-difference-shift-pauli-incidence-proof
kind: route
target: diagonal-difference-shift-propagates-pauli-incidence
uses:
  - diagonal-covariance-has-quadratic-hs-word-cost
  - toeplitz-coordinate-paulis-localize-cells-and-grams
---

Use the finite relations `(DPI1)`.  Since `t=cU` and `c,U` commute, move
the `U^i` part of `t^i` across a base Pauli seed and cancel it, giving
`a_i=c^i a c^(-i)`.  Move a shifted selector `z_j` past `c^i` using the
conjugates of `[c,z]`, and past `a` using `[z,a]` together with `[U,a]`.
This proves all shifted cross-commutators.  Standard commutator collection
and the quadratic diagonal-covariance estimate give polynomial filling area.

Finally evaluate the presentation on `(DPI5)`.  The difference shift and
Toeplitz Paulis occupy the first tensor factor, while the C18/reset menu and
Fanizza shift occupy the second.  Hence the new relations are compatible
with an exact nontrivial marked model.  Apply the Pauli Gram localization
estimate after fixed-packet exactification of the selectors.

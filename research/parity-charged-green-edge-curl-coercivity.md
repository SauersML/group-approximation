---
rg: 2
id: parity-charged-green-edge-curl-coercivity
kind: claim
title: Charge finite-Green edge curl by the balanced sparse syndrome
distinct_from:
  ordinary-green-triangle-curl-has-a-linear-code-tangent: that refutes a pair-only quadratic curl estimate; this asks to pay its linear tangent by the parity/equality layer that detects it.
  sparse-face-row-square-survives-intrinsic-green-step: that proves sparse exactification has only second-order cost once a descent direction is known; this must use the sparse residual itself to establish first-order dense coercivity.
  off-base-row-gradient-coercivity: that is the full descent theorem; this is its sole remaining first-order inequality.
---

OPEN.  On the retained pointwise low-odd-square block, prove a
dimension-free Hodge/SOS inequality of the form

```text
 E_edge(omega)
 <=C E_div(omega)+C E_parity+ C E_equality,             (PCG1)
```

where `omega_ij` is the intrinsic skew edge signal, `E_div` is the
normalized correction-row energy, and the last two terms are the balanced
operator row-square residuals of the all-local-dual faces and equality
clouds.  Any remainder which is quadratic in the low odd-square radius is
acceptable and can be absorbed.

## Attempts

The ordinary complete-graph Hodge identity alone writes edge energy as
divergence plus ordinary triangle curl.  The latter is not quadratic:
`ordinary-green-triangle-curl-has-a-linear-code-tangent` gives an exact
low-`R` counterexample.  Its linear part is, however, precisely a violation
of the local-dual tangent equations.  A proof of `(PCG1)` should therefore
apply the established face-Hamiltonian/code gap to the linearized curl and
use `fixed-parity-faces-exactify-with-loewner-row-square-control` to bound
the off-base difference; a pair-only word factorization cannot work.

Planar phase cancellation is not an additional obstruction.
`short-arc-planar-pauli-edges-have-uniform-divergence-gap` writes the edge
field through the complex order parameter and proves
`E_edge<=4 sec^2(r)E_div` whenever the doubled Pauli axes lie in one arc of
length `r<pi/2`, including arbitrary central mixtures with the same bound.
Thus a countermodel to `(PCG1)` must use genuinely nonplanar/noncentral
operator geometry or incompatible projective branches.  The parity charge
is needed to choose/coordinate those branches, not to repair ordinary
short-arc Kuramoto cancellation.

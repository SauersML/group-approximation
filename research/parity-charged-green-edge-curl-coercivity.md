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

ESTABLISHED.  On the retained pointwise low-odd-square block, there is a
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

In fact the pair-sum overlay gives the stronger estimate

```text
 E_edge(omega)<=C(E_parity+E_equality).                 (PCG2)
```

Here `E_parity` includes the normalized involution, within-face
commutator, and parity-word squares of the balanced augmented faces.
`pair-sum-local-exactification-pays-green-edge-proof` first exactifies each
fixed-width occurrence face with Loewner row-square control.  Equality
variance then bounds the incidence distance from shared representatives to
these exact local copies.  Pair-sum congestion converts that incidence
distance into complete-pair commutator energy.  Finally
`omega_ij^*omega_ij=R_ij(I-R_ij)<=R_ij`, where
`R_ij=[Q_i,Q_j]^*[Q_i,Q_j]/4`.  Normalized summation proves `(PCG2)`, and
`(PCG1)` follows because `E_div` is nonnegative.

## Attempts

The ordinary complete-graph Hodge identity alone writes edge energy as
divergence plus ordinary triangle curl.  The latter is not quadratic:
`ordinary-green-triangle-curl-has-a-linear-code-tangent` gives an exact
low-`R` counterexample.  Its linear part is, however, precisely a violation
of the local-dual tangent equations.  The proof above pays that tangent
directly through exact local faces and incidence congestion; it neither
needs nor asserts a pair-only quadratic word factorization.

Planar phase cancellation is not an additional obstruction.
`short-arc-planar-pauli-edges-have-uniform-divergence-gap` writes the edge
field through the complex order parameter and proves
`E_edge<=4 sec^2(r)E_div` whenever the doubled Pauli axes lie in one arc of
length `r<pi/2`, including arbitrary central mixtures with the same bound.
Thus a countermodel to `(PCG1)` must use genuinely nonplanar/noncentral
operator geometry or incompatible projective branches.  The parity charge
is needed to choose/coordinate those branches, not to repair ordinary
short-arc Kuramoto cancellation.

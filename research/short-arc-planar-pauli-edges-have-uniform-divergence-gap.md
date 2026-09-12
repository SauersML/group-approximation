---
rg: 2
id: short-arc-planar-pauli-edges-have-uniform-divergence-gap
kind: claim
title: Short-arc planar Pauli edges have a uniform intrinsic divergence gap
distinct_from:
  ordinary-green-triangle-curl-has-a-linear-code-tangent: that refutes an ordinary quadratic curl estimate using an inactive vertex; this proves that the actual normalized divergence nevertheless controls all edge energy in one coherent planar branch.
  parity-charged-green-edge-curl-coercivity: that asks for arbitrary operator-valued sectors and uses parity/equality to pay curl; this needs no sparse charge but assumes a common planar short-arc representation.
  low-odd-square-removes-pairwise-green-stationarity: that proves edgewise signal from functional calculus; this prevents cancellation of those edge signals after divergence averaging in the planar sector.
---

ESTABLISHED RESTRICTED COERCIVITY.  Let

```text
 Q_i=cos(alpha_i)Z+sin(alpha_i)X
```

be planar Pauli reflections on one qubit (and allow arbitrary central direct
sums of such blocks).  Suppose the doubled angles `x_i=2alpha_i` admit
lifts contained in an interval of length `r<pi/2`.  Write the intrinsic skew
edge and its normalized divergence as

```text
 omega_ij=-(i/2)sin(x_j-x_i)Y,
 d_i=(1/L)sum_j omega_ij.                               (SAP1)
```

Then

```text
 E_edge=(1/L^2)sum_(i,j)||omega_ij||_2^2,
 E_div =(1/L)sum_i||d_i||_2^2,

 E_edge<=4 sec^2(r) E_div.                             (SAP2)
```

Thus no stationary or asymptotically cancelling intrinsic edge field exists
inside a coherent short planar arc.  No parity or equality term is needed.
The estimate is stable under central mixtures because it holds blockwise
with the same constant.

Pointwise low odd square alone does not choose a coherent lift: projective
angles may use different near-`pi` branches on different noncentral blocks.
Accordingly this does not prove
`parity-charged-green-edge-curl-coercivity`.  It shows that any obstruction
to that claim must use genuinely nonplanar/noncentral geometry or failure of
the parity layer to select compatible projective branches; ordinary planar
phase cancellation is excluded.

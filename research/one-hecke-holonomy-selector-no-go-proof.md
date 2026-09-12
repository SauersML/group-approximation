---
rg: 2
id: one-hecke-holonomy-selector-no-go-proof
kind: route
title: Close the last multiplicity gauge while retaining the rank mismatch
target: one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum
requires:
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - cyclic-coarse-fine-selector-rows-spread-carrier-error
---

Use the positive regular stationary packet modules supplied by the first
prerequisite.  On any matched isotypic block, after the packet intertwiners
have been fixed, each edge intertwiner still has a free external
multiplicity gauge

```text
T_i = T_i^0 tensor V_i.
```

If the sole attached two-cell prescribes the closed holonomy
`V_(k-1)...V_0=W`, choose `V_0,...,V_(k-2)` arbitrarily and set

```text
V_(k-1) = W (V_(k-2)...V_0)^(-1).
```

Every packet edge and the holonomy cell is then represented exactly, so its
ordinary word energy is zero.  The same assignment works after replacing
the intertwiners by partial-swap involutions: that construction is functorial
in the free multiplicity gauges.

The selector ranks are unaffected by those gauges.  With the half and
quarter cuts in `(HHC1)`, the cyclic coarse--fine inequality from the second
prerequisite gives

```text
sum_i ||U_i e_i U_i^* - f_(i+1)||_2^2
  >= (1/4) sum_i tr(P_i) > 0.                         (HNP1)
```

Thus the proposed selector sum is positive in an exact finite-dimensional
model whose edge-plus-two-cell energy is zero.  No inequality of the form
`(HHC6)` with `eta(0)=0` can hold.  A single uncompressed closed holonomy
therefore cannot pay the cyclic selector sum; any successful actuator must
read additional compressed intermediate selector data, exactly as claimed.

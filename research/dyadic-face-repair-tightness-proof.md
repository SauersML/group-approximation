---
rg: 2
id: dyadic-face-repair-tightness-proof
kind: route
title: Split authenticated faces by repair cost and local energy density
target: dyadic-face-repair-needs-cost-tail-tightness
requires:
  - fixed-finite-core-face-has-energy-paid-completion
  - regular-trace-allows-diffuse-dyadic-flow
---

For `C_lambda<=L`, `(DFR1)` gives total normalized cost at most
`L epsilon`.  For `C_lambda>L`, use `r_lambda<=d_lambda`; this proves
`(DFR3)`.  Choose `L` using `(DFR4)` and then let `n->infinity`.

For `(DFR5)`, split the types in `F` according as
`e_lambda/d_lambda<=theta` or `>theta`.  The low-density part costs at most
`omega_F(theta)`.  The total physical mass of the high-density part is at
most `epsilon/theta`.  Repairing everything outside `F` by the trivial
dimension bound proves `(DFR5)`.

The one-type array in the claim satisfies every fixed-type conclusion, yet
has energy density `1/C_n` and permitted repair fraction one.  Finally,
`regular-trace-allows-diffuse-dyadic-flow` proves that canonical trace makes
the mass of every fixed conductor window vanish, so finite-window
compactness supplies no tail term tending to zero.


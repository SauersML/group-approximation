---
rg: 2
id: iwahori-weil-cycle-packet-proof
kind: route
title: Restrict the finite-field Weil representation to the arithmetic BS(1,4) matrices
target: iwahori-weil-cycle-packets-extend-exactly
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Use the standard `(p-1)/2`-dimensional Weil constituent of `PSL_2(F_p)` for
`p=3 mod 4`.  In its unipotent eigenbasis, the half-parabolic `s` has one
eigenline for every nonzero quadratic square (up to the fixed square scaling
from `1/2`).  If `ord_p(4)=(p-1)/2`, these eigenlines form one fourth-power
cycle.  The diagonal matrix `r` carries each line to its predecessor in that
cycle, and `r^m=1` in `PSL_2(F_p)`, so the packet normal form has scalar
monodromy `+1`.  The finite-field reductions of `x,r,s` obey all five
relations of the corrected presentation, hence the Weil images give the
required exact involution and cubics.

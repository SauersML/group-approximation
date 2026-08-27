---
rg: 2
id: movable-weyl-gauge-counterpacket-proof
kind: route
title: Reverse a small base-commutant correction on an exact congruence packet
target: movable-weyl-gauge-refutes-iwahori-cubic-low-mode-gain
requires: []
---

For each `L`, use the regular representation of the reduction modulo
`N=4^L-1` and the length-`L` character orbit described in `(MWG2)--(MWG4)`.
The correction identity `(MWG5)` identifies the residual of the tuple with
Weyl swap moved by `c_alpha^(-1)` as `exp(i alpha b)`.  The band derivative
calculation gives `(MWG7)`, while fixed-word telescoping gives `(MWG8)` for
every presentation row.  Substitution into the proposed positive-exponent
estimate and cancellation leaves `1<=C' g_L^epsilon`, contrary to
`g_L -> 0`.  This proves the target claim.

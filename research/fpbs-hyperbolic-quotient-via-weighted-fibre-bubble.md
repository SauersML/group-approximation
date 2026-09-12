---
rg: 2
id: fpbs-hyperbolic-quotient-via-weighted-fibre-bubble
kind: route
title: Apply the rapid-decay weighted bubble criterion to every Cayley graph of the hyperbolic-quotient class
target: fpbs-hyperbolic-quotient-every-generating-set
requires:
  - fpbs-rd-quotient-weighted-bubble-gives-critical-l2
  - hyperbolic-groups-have-property-rd
  - fpbs-rd-quotient-weighted-critical-fibre-bubble
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

Fix `Gamma` in the class, a finite symmetric generating set `S`, and a rapid
decay exponent `D` of the hyperbolic quotient `Q`.

1. The weighted critical fibre bubble is finite; this is the open premise.
2. The implication claim bounds `||T_(p_c)||` on `Cay(Gamma,S)`, which gives
   `p_c < p_{2->2} <= p_u`.
3. `S` was arbitrary, so the target follows.

This is a one-premise alternative to `fpbs-hyperbolic-quotient-via-fibre-estimates`.
It has no far-halfspace premise. Its single premise is stronger than the
unweighted fibre bubble by a polynomial weight.

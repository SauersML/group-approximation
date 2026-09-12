---
rg: 2
id: fpbs-hyperbolic-quotient-via-fibre-estimates
kind: route
title: Apply the two-estimate L2 gap to every Cayley graph of the hyperbolic-quotient class
target: fpbs-hyperbolic-quotient-every-generating-set
requires:
  - fpbs-hyperbolic-quotient-fibre-estimates-l2-gap
  - fpbs-hyperbolic-quotient-uniform-fibre-bubble
  - fpbs-hyperbolic-quotient-far-halfspace-share
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Fix `Gamma` in the class and a finite symmetric generating set `S`. Both
premises hold for `Cay(Gamma,S)`: the uniform fibre bubble and the vanishing
far-halfspace share. The implication claim then gives
`p_c < p_{2->2} <= p_u` on `Cay(Gamma,S)`. Since `S` was arbitrary, the target
follows. This is a genuine two-premise decomposition, not a restatement. Each
premise is a statement about the fibre-summed profile on `Q`. Neither is
equivalent to the target, and neither follows from the other, as far as the
artifact shows.

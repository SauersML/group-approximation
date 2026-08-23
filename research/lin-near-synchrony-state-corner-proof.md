---
rg: 2
id: lin-near-synchrony-state-corner-proof
kind: route
title: Average Lin's spectral-layer row estimate relative to layer mass
target: lin-near-synchrony-selects-one-state-corner
requires: []
---

The spectral-corner decomposition and integrated row bound are Theorem 4.1
of Junqiao Lin, arXiv:2304.01940v3.  If every positive-mass layer had
`e_lambda>E tau(P_lambda)`, integration would contradict the two displayed
integrals, proving the selected-layer estimate.

No uniform lower bound follows.  For
`sigma=alpha^(-1/2)p`, `tau(p)=alpha`, positivity of
`integral P_lambda d lambda=alpha^(-1)p` forces almost every layer under
`p`, hence every such layer has mass at most `alpha`.  Since `alpha` is
arbitrary, the selection is state-dependent and quantitatively insufficient
for a marked-mass floor.

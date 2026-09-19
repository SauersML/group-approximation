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

For the relative marked-sector version `(L4.2)`, use `sigma=sqrt(N)q`.
The positive operator integral of the layers is `sigma^2=Nq`.  Compressing
that identity by `1-q` shows
`integral (1-q)P_lambda(1-q) d lambda=0`; positivity makes the integrand
zero almost everywhere, and hence `P_lambda<=q` for almost every layer.
Therefore `tau(P_lambda)<=1/N`, whereas
`tau(p)=floor(N/2)/N`.

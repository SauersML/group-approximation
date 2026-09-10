---
rg: 2
id: fpbs-measurable-matroid-approximate-exchange
kind: claim
title: Measurable matroid bases admit approximate simultaneous exchanges
artifacts:
  - research/artifacts/fpbs/docs/sparse-base-surgery.md
  - research/artifacts/fpbs/docs/cost-rank-duality.md
---

For bases B1,B2 of a measurable matroid and a finite measurable
partition B1=X1 union ... union Xq, every epsilon>0 permits a
partition B2=Y0 union Y1 union ... union Yq with mu(Y0)<=epsilon
and (B1 minus Xi) union Yi independent for each i. Each such set
can be extended to a basis after adding measure at most epsilon.
This is Theorem 7.20 of arXiv:2608.16464v1.

For a graphing cycle matroid, the bases are hyperfinite essential
forests. The theorem does not assert connected orbit-spanning outputs
or identify matroid rank with optimized action cost.

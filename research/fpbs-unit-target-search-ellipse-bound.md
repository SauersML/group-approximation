---
rg: 2
id: fpbs-unit-target-search-ellipse-bound
kind: claim
title: Unit target weighting confines connection queries to the open-path metric ellipse
artifacts:
  - research/artifacts/fpbs/search-geometry.md
---

For the balanced exhaustive search with priority depth(u)+1+d_G(v,y),
if the endpoint open distance is L, every queried edge lies in the induced
metric ellipse {v:d_G(x,v)+d_G(v,y)<=L}. Thus the fresh-query count is at
most the number of its induced edges. On T_4 x Z the ellipse has exact
volume (a+2)(b+2)3^m-(a+b+2m+3), for m=floor((L-a-b)/2).
Section 2 proves these deterministic statements; no moment bound on L
or expected-query upper bound is asserted.

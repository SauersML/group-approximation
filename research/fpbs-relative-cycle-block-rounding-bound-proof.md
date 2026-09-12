---
rg: 2
id: fpbs-relative-cycle-block-rounding-bound-proof
kind: route
title: Apply retraction rounding and bound the retained tree chains by crossing-edge energy
target: fpbs-relative-cycle-block-rounding-bound
requires:
  - fpbs-relative-cycle-retraction-rounding
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Sections 6 and 7. Replace internal edges by their block-tree paths and
fix crossing edges. The bounded retraction R preserves boundary. For
a cycle chain v, Rv has external part P_out v and an internal tree
chain whose boundary is its negative. The block-tree Laplacian bound
1/M^2 and the full boundary norm bound sqrt(2d) yield
||Rv||^2<=(1+2d M^2)||P_out v||^2. Apply this to K^(1/2) and take
traces, then use the required retraction-rounding inequality. This
proves both the general and the relative estimates. Section 6 retains
the direct proof by internal cycle projection as well.

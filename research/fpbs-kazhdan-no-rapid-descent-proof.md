---
rg: 2
id: fpbs-kazhdan-no-rapid-descent-proof
kind: route
title: Pull the series back to a finitely presented Kazhdan cover and apply Lackenby's rapid-descent theorem
target: fpbs-kazhdan-no-rapid-descent
requires:
  - fpbs-shalom-property-t-is-open
  - fpbs-lackenby-rapid-descent-p-large
  - fpbs-lackenby-cocycle-support-toolkit
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

Written deduction, lane `sw-007`, 2026-09-17. The full argument is Section
"Theorem A" of the artifact.

1. Shalom gives a finitely presented Kazhdan `G` onto `Gamma`.
2. The preimages `P_i` form an abelian `p`-series of `G` with the same
   quotients and indices, so it has rapid descent.
3. Lackenby's Theorem 1.15 makes `G` `p`-large, so some finite index subgroup
   maps onto `Z`. This contradicts (T).
4. If `RG_p(L) = c > 0`, the derived `p`-series of `L` has
   `d_p(D_i/D_(i+1)) = d_p(D_i) >= 1 + c[L:D_i]`, which is rapid descent.
5. A pro-`p`-cofinal family with linear growth pushes linear growth onto the
   derived `p`-series by Lemma 3.3 (`fpbs-lackenby-cocycle-support-toolkit`).

---
rg: 2
id: quotient-gap-gives-uniform-relative-projection-repair
kind: claim
title: "Quotient spectral gap repairs every small-energy projection in a common large corner"
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 3.2. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

In the setting of quotient-gap-expectations-have-coordinate-lifts, let 0<a<1 and L=36/a^2. There are projections e_n and eta_n>0, with tr(1-e_n)->_omega 0 and eta_n->_omega 0, chosen BEFORE any test projection. For every n and every p<=e_n with E_n(p)<=tr(p)/(4L), there is a projection f in the original M_(d_n) with
```
||f-p||_2^2 <= L E_n(p),
tr(p)/4 <= tr(f) <= 9 tr(p)/4,
E_n(f) <= eta_n tr(f).
```
There is no lower bound on rank(p)/d_n. This is Liu Theorem 3.2, not merely additive-error repair for a prescribed sequence. Removing maximal-rank bad projections and their bounded word neighborhoods is the proposed uniformity mechanism.

## Attempts

2026-09-20: equation-level inspection is recorded in the cited audit. No concrete gap was found in the inspected steps, but this import remains OPEN pending completion of its independent review. No empty-premise citation route is supplied.

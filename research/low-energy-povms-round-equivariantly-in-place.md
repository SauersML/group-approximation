---
rg: 2
id: low-energy-povms-round-equivariantly-in-place
kind: claim
title: "Low-energy positive partitions round equivariantly in the original dimension"
distinct_from:
  low-energy-povms-yield-flexible-projection-cuts: "That supplies overlapping cuts and auxiliary repairs; this produces an orthogonal original-dimensional partition with independently vanishing energy."
  outcome-count-free-subpovm-completion: "That controls ordinary rounding error; this requires vanishing summed equivariance error even at fixed positive purity deficit."
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 4.3 (using the credited Houdayer–Vaes and Ioana projection results). This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

For every h>=1 and epsilon>0 there is delta>0, independent of dimension d and outcome count m, with the following property. Let u_1,...,u_h be unitaries in M_d and positive a_i sum to I. If sum_i E_u(a_i)<=delta, where E_u(x)=(4h)^(-1)sum_j ||[u_j,x]||_2^2, there is a projection-valued partition q_i in the SAME M_d such that
```
sum_i E_u(q_i) <= epsilon,
sum_i ||q_i-a_i||_2^2 <= 5000 sum_i tr(a_i-a_i^2) + epsilon.
```
No group relations or spectral gap are assumed. The purity deficit need not vanish for the OUTPUT ENERGY to vanish. Liu Theorem 4.3 uses an auxiliary algebra only during construction, then returns the partition to the physical dimension.

## Attempts

2026-09-20, initial pass: the partial audit left this claim open. Superseded by the full reconstruction in the acceptance supplement and the direct route `low-energy-povms-round-equivariantly-in-place-proof`. The exact assertion is now established by a checked written proof of Jihao Liu's argument, including its quantified error estimates and named background imports. This is not a Lean certificate or external human-referee verdict; authorship remains Liu's.

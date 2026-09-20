---
rg: 2
id: quotient-gap-gives-large-scalar-expanding-blocks
kind: claim
title: "Quotient gap yields arbitrarily large physical scalar-expanding block decompositions"
distinct_from:
  hs-one-level-expander-block-decomposition: "That asks for a stronger fixed-gap decomposition for compressed original generators as discarded trace vanishes; this allows a tolerance-dependent gap and doubled perturbed generators."
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 5.1. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

In the fixed ultrafilter setting with h generator lifts and quotient gap a>0, for EVERY FIXED epsilon>0 there are c=c(a,h,epsilon)>0, partitions R_(0,n),...,R_(m_n,n) of I in the ORIGINAL M_(d_n), and two unitaries z_(j,n)^+,z_(j,n)^- for each original generator, such that:
- every z reduces every R_(i,n);
- sum_(j,+/-)||z_(j,n)^+/- - u_(j,n)||_2^2 ->_omega 0;
- lim_omega tr(R_(0,n)) <= epsilon;
- on every nonzero i>=1 block, the doubled list has scalar gap c in the normalized block trace.

Ranks and outcome counts are unrestricted. Epsilon is fixed BEFORE the ultrafilter limit. No positive gap uniform as epsilon->0, and no gap for the unperturbed compressed generators, is asserted. Source: Liu Theorem 5.1.

## Attempts

2026-09-20: equation-level inspection is recorded in the cited audit. No concrete gap was found in the inspected steps, but this import remains OPEN pending completion of its independent review. No empty-premise citation route is supplied.

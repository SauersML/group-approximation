---
rg: 2
id: defective-block-expansion-prunes-to-doubled-gaps
kind: claim
title: "Summable expansion defects can be pruned into scalar gaps for doubled nearby generators"
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Lemma 5.4. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

Let P_0,...,P_m partition I in M_d, and let h unitaries w_j reduce every P_i. Fix 0<theta<=1. For each i>=1 suppose every projection q<=P_i with rank(q)<=rank(P_i)/2 satisfies E_w(q)>=theta tr(q)-xi_i, where xi_i>=0 and xi=sum_(i>=1)xi_i.

There are R_i<=P_i for i>=1 and two unitary copies z_j^+,z_j^- reducing R_0=I-sum_(i>=1)R_i and every R_i, with
```
tr(R_0)-tr(P_0) <= 8 xi/theta,
sum_(i>=1) E_w(R_i) <= xi/7,
sum_(j,+/-) ||z_j^+/- - w_j||_2^2 <= 16 h xi/7.
```
Every nonzero retained block has scalar gap theta^2/64 for the DOUBLED list, in its own normalized trace. This is Liu Lemma 5.4. It charges each defect once and imposes no minimum block trace.

## Attempts

2026-09-20, initial pass: the partial audit left this claim open. Superseded by the full reconstruction in the acceptance supplement and the direct route `defective-block-expansion-prunes-to-doubled-gaps-proof`. The exact assertion is now established by a checked written proof of Jihao Liu's argument, including its quantified error estimates and named background imports. This is not a Lean certificate or external human-referee verdict; authorship remains Liu's.

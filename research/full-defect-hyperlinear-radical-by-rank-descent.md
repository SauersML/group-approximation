---
rg: 2
id: full-defect-hyperlinear-radical-by-rank-descent
kind: route
title: "Transfer the universal Cohn hyperlinear radical through the rank-two normal generator"
target: full-defect-rings-have-full-hyperlinear-radical
requires:
  - cohn-rank-four-has-full-hyperlinear-radical
  - full-idempotent-ring-has-properly-infinite-unit
  - elementary-rank-descent-to-two
artifacts:
  - research/artifacts/full-defect-ring-hyperlinear-radical-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorems 1.2/6.7 and 1.3/7.4, with Andreas Thom's
conditional normalization theorem, supplies the analytic contribution
through the universal Cohn prerequisite. The present descent is earlier
Cairn/OpenAI algebra in `non_mf_groups_exist.tex`, now applied to
hyperlinear targets. It is not an analytic argument of Liu's paper.

## Why sufficient

Fullness supplies v_0,v_1,w_0,w_1 with w_i v_j=delta_ij, and thus a
unital map from the integral two-copy Cohn ring C to R. The algebraic
rank-descent premise supplies Psi:EL_4(R)->EL_2(R), with
Psi(x_12(1)) normally generating EL_2(R). For any homomorphism rho
from EL_2(R) to a hyperlinear target, the composite

```
EL_4(C) -> EL_4(R) --Psi--> EL_2(R) --rho--> K
```

is trivial by the Cohn prerequisite. Hence rho kills the normal
generator Psi(x_12(1)), so rho is trivial. Neither the ring map nor
its elementary-group map needs to be injective. Every elementary root
in rank n>=3 lies in a two-coordinate copy of EL_2(R), proving the
remaining ranks. The same corner formula j embeds EL_4(R) into R^x;
it is nontrivial since R is nonzero, so R^x cannot be hyperlinear.

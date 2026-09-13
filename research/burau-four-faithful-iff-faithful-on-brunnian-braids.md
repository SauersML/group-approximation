---
rg: 2
id: burau-four-faithful-iff-faithful-on-brunnian-braids
kind: claim
title: "The 4-strand Burau representation is faithful iff no nontrivial Brunnian 4-braid lies in its kernel"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

`ρ_4` is faithful on `B_4` if and only if `ker ρ_4 ∩ Brun_4 = 1`.

This is Proposition 1.2 of arXiv:2607.05283v1 (Bharathram–Birman–Brendle), which they deduce
from Long's theorem. Here it is derived from two independently proved claims:

- `burau-faithful-iff-faithful-on-noncentral-normal-subgroup` (Long's theorem for `n ≥ 4`);
- part 1 of `brunnian-four-braids-are-pseudo-anosov` (`Brun_4` is a nontrivial normal subgroup
  meeting the center trivially, so it is not contained in the center).

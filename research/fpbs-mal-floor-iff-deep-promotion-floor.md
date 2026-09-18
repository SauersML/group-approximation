---
rg: 2
id: fpbs-mal-floor-iff-deep-promotion-floor
kind: claim
title: The Gamma_mal Bernoulli floor holds iff promoting E_{phi^{j+1}(F_2)} to E_{phi^j(F_2)} inside the Bernoulli shift of F_2 costs at least a fixed c > 0 at every depth j
distinct_from:
  fpbs-mal-bernoulli-single-stage-floor: that is the open target; this is an exact reformulation of it as a uniform one-step promotion floor for one finitely generated group, and it decides nothing.
  fpbs-shifted-stage-relative-cost-zero-or-infinite: that says relC over a stage is 0 or infinity; this replaces relC over a stage by the one-step promotion cost from stage 1 to stage 2 with arbitrary labels.
  fpbs-mal-graphing-b-length-weighted-floor: that bounds depth-0 graphings (labels in H_2) in b-length; this shows that the depth-j promotion costs Q_j are the only remaining quantity.
artifacts:
  - research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md
  - experiments/fpbs-deep-promotion-2026-09-17/core_size.py
  - experiments/fpbs-deep-promotion-2026-09-17/core_size_out.txt
---

**ESTABLISHED** through `fpbs-mal-floor-iff-deep-promotion-floor-proof`.

Let `L = F(a, b)`, `phi(a) = a`, `phi(b) = b a b^{-2}`,
`L_j = phi^j(L)`, and let `rho` be the Bernoulli shift of `L`, with
`S_j = E_{rho|L_j}`. Put

```text
Q_j = inf { C(Psi) : Psi a graphing inside E_rho,  S_{j+1} v Psi ⊇ S_j }.
```

Then `Q_0 = relC(E_rho; S_1)`, `Q_j` is nonincreasing, and

```text
relC(E_beta; E_{beta|H_1}) > 0   iff   inf_j Q_j > 0,
```

where `beta` is the Bernoulli shift of `Gamma_mal`. More precisely, with
`q_m` the cost of promoting `E_{H_1}` to `E_{H_2}` by graphings inside
`E_{H_m}` (and `m = infinity` meaning inside `E_beta`):
- `q_infinity = lim_m q_m`;
- `relC(E_beta; E_{H_1}) = 0` iff `q_infinity = 0`;
- `q_{j+2} = Q_j`.

**Reading.** The target, about a group that is not finitely generated, is
exactly a uniform one-step promotion floor for the Bernoulli shift of `F_2`.
Its refutation needs no telescoping scheme, only cheap one-step promotions at
growing depth. With `Q_{j+1} = (1 - eps_j) Q_j`, the target is equivalent to
`Q_0 > 0` together with `prod (1 - eps_j) > 0`, where `eps_j` is the saving
from one extra level of labels.

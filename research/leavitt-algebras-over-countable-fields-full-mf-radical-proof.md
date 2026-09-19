---
rg: 2
id: leavitt-algebras-over-countable-fields-full-mf-radical-proof
kind: route
title: The second branch inverts the first complementary idempotent
target: leavitt-algebras-over-countable-fields-full-mf-radical
requires:
  - full-complementary-idempotent-elementary-full-mf-radical
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
  - non_mf_groups_exist.tex
---

## Why sufficient

Take `s = s_1`, `t = t_1`.  Then `1 - s_1 t_1 = Σ_{i ≥ 2} s_i t_i` and

```text
t_2 (1 - s_1 t_1) s_2 = Σ_{i≥2} (t_2 s_i)(t_i s_2) = 1,
```

so `R (1 - st) R = R` with a single pair `a = t_2`, `b = s_2`.  `L_k(1,m)` is
countable for countable `k`.  Apply
[[full-complementary-idempotent-elementary-full-mf-radical]].

---
rg: 2
id: residual-finiteness-two-generator-recursive-is-pi3-complete
kind: claim
title: Residual finiteness is Pi-zero-three complete for two-generator recursive presentations, which is optimal
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  residual-finiteness-three-generator-recursive-is-pi3-complete: that uses the three-generator centralizing family; this reaches two generators, the minimum possible, with the shift right-angled Artin family and a sparser dyadic row placement that survives symmetrization.
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that is the countably generated theorem; this is its optimal finitely generated form.
  amenability-two-generator-recursive-is-pi2-complete: that classifies amenability of the same two-generator family at the second level; this classifies its residual finiteness at the third, so one family witnesses that residual finiteness is strictly harder than amenability, LEF, soficity, hyperlinearity and MF on recursive presentations.
---

ESTABLISHED.  For recursive presentations on two generators,

```text
RF_rec2     is Pi^0_3-complete,
NONRF_rec2  is Sigma^0_3-complete.                                    (R2)
```

One generator is impossible (cyclic groups are residually finite), so
two is optimal.  The family is

```text
G_e = < a, t | [a, t^i a t^-i] = 1  for  i in J_e >,
J_e = U_x { 2^x (4j + 1) : j < |W_g(e,x)| },
```

residually finite iff every `W_g(e,x)` is finite.

This completes the third-level classification begun in
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]]:
on recursive presentations residual finiteness sits one full level above
every approximation property and above amenability, and one
two-generator family exhibits the gap.  The finite-presentation question
(`Pi^0_2`-completeness of `RF_fp`) remains the residually finite Higman
problem.

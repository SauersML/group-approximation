---
rg: 2
id: inverse-packet-conjugator-must-mix-s-and-t-charts
kind: claim
title: An inverse-pair packet conjugator must genuinely mix the s and t charts
distinct_from:
  conjugated-s3-packets-live-on-n-double-cosets: that excludes the C3 normalizer and scalar coordinate copies; this additionally excludes both full pure coefficient chart groups.
  two-packet-solution-requires-relative-double-coset-folding: that requires a relation over the base subgroup; this identifies which explicit coefficient subgroups still cannot supply that relation.
  both-rank-three-factors-must-be-packet-corrected: that requires two packet parameters in general; this specializes to the natural inverse-pair ansatz and gives its exact remaining domain.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

In the ansatz `y=x^-1`, the correction equation is

```text
e(t~+[x]k[x^-1])e(s~+[x^-1]k[x])e=e.
```

It has no solution with

```text
x in N_G(H) union GL_2(F_2<t_0,t_1>) union GL_2(F_2<s_0,s_1>).
```

The normalizer packet is zero.  In the `t`-chart, the corrected left factor
is supported in a residually finite group, so an ambient right inverse would
make its image `t_0` a unit.  In the `s`-chart, the corrected right factor has
the symmetric obstruction with image `s_0`.  Thus every constant,
permutation, scalar self-similar, pure `t`-root, and pure `s`-root candidate
is excluded.  A viable inverse-pair conjugator must contain both coefficient
halves and satisfy the relative double-coset folding condition.


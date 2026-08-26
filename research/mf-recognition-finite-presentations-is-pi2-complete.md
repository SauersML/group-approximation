---
rg: 2
id: mf-recognition-finite-presentations-is-pi2-complete
kind: claim
title: MF and non-MF recognition are second-level complete on finite presentation codes
root: true
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that proves the membership upper bound and properness over the first level; this asks for the missing FIN-hardness.
  mf-recognition-recursive-presentations-is-second-level-complete: that proves exact completeness before finite-presentation compilation.
---

**ESTABLISHED.**  For finite presentation codes,

```text
NONMF_fp is Sigma^0_2-complete,
MF_fp    is Pi^0_2-complete.
```

The upper bounds are established by
[[mf-recognition-has-a-pi2-upper-bound]].  The matching hardness reduction is

```text
FIN <=_m NONMF_fp.
```

It uses the exact recursive FIN/INF switch, the residually finite
three-generator bridge, a Mikhailova fiber-product benign witness whose
ambient group is a direct product of free groups, the effective finite-CEP
embedding `B3(1)<=F_2 times F_2`, and tensor synchronization of the final
asymmetric rope edge.  The output is MF on `INF` and contains the fixed non-MF
group `E` on `FIN`.

## Attempts

The finitely presented Higman host itself need not be MF.  The completed
compiler uses only its relators and marked embedding words to build a
Mikhailova subgroup in a residually finite product of free groups.  This
regular-MF witness supplies the faithful model, while the graph witness
supplies finite edge models.
Tensoring them makes the final edge compatible in operator norm.

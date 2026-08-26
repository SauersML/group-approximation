---
rg: 2
id: torsion-freeness-of-finite-presentations-is-pi2-complete
kind: claim
title: Torsion-freeness of finitely presented groups is Pi-zero-two complete
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  torsion-freeness-recognition-is-pi2-complete: that is the theorem for recursive and enumerated presentations, where the switch alone suffices; this crosses to finite presentations through the compiler and its torsion-free positive rope, and is the first property other than MF whose finite-presentation cell is closed at the second level.
  mf-recognition-finite-presentations-is-pi2-complete: that is the MF cell; this is the torsion-free cell, obtained from the same compiler with a different seed and a different property of the positive branch.
---

ESTABLISHED.  For the recursive coding of finite group presentations,

```text
TORSIONFREE_fp   is Pi^0_2-complete,
HASTORSION_fp    is Sigma^0_2-complete.                            (TFP1)
```

Membership is the `Pi^0_2` normal form of
[[torsion-freeness-recognition-is-pi2-complete]] specialized to finite
relator lists.  Hardness is
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] with
`P` = torsion-freeness (hereditary), (C1) supplied by
[[mf-compiler-positive-branch-is-torsion-free]] and (C2) by the seed
`Z/2`.

This closes one of the open cells of
[[arithmetical-complexity-table-of-group-properties]] and shows that
`Pi^0_2`-completeness on finite presentations is not special to MF: the
obstacle in the remaining cells is exactly whether the fixed rope has the
property in question.

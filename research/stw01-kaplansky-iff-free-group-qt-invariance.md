---
rg: 2
id: stw01-kaplansky-iff-free-group-qt-invariance
kind: claim
title: Kaplansky's quasitrace conjecture is equivalent to universal free-group tensor invariance
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `QT_1(C)` denote the normalized bounded 2-quasitraces on a unital
C*-algebra `C`.  The following are equivalent:

1. every bounded 2-quasitrace on every C*-algebra is a trace;
2. for every unital C*-algebra `A`, restriction along the first-factor
   embedding induces an affine homeomorphism

```text
QT_1(A tensor_min C*_r(F_2)) ~= QT_1(A).                (FG1)
```

This is the exact tensor test recorded in footnote 54 of
Schafhauser--Tikuisis--White, arXiv:2506.10902v2.  It does not assert either
equivalent condition.

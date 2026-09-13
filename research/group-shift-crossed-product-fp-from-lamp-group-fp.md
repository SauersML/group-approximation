---
rg: 2
id: group-shift-crossed-product-fp-from-lamp-group-fp
kind: claim
title: The crossed-product algebra of a group shift is the group algebra of its lamp group, so a finitely presented lamp group makes the shift quantum rigid
distinct_from:
  ledrappier-crossed-product-is-finitely-presented: that proves rigidity of one permutive shift by a commutator computation; this identifies every group shift's crossed product with a group algebra, reducing quantum rigidity of algebraic shifts to finite presentation of metabelian groups.
  antipodal-one-sided-group-shift-configurations-are-walls: that is the obstruction side for group shifts; this is the positive side, through presentations of the lamp group.
artifacts:
  - research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `X ⊆ (F_p^m)^(Z^2)` be a group shift with Pontryagin dual `M`, a finitely
generated `F_p[Z^2]`-module. Let `k` be a field with `char k != p` containing a primitive `p`-th root of unity.
1. `LC(X, k) ⋊ Z^2 ≅ k[M ⋊ Z^2]`, by Fourier transform on the compact group `X`, whose characters form `M`.
2. If the lamp group `M ⋊ Z^2` is finitely presented, then `k[M ⋊ Z^2]` is finitely presented. So `X` is
   `D`-quantum rigid for some `D` (`sft-crossed-product-fp-iff-quantum-rigid`).

**Conditional equivalence.** Two facts are recalled and not re-read:
- Bieri–Strebel: `M ⋊ Z^2` is finitely presented iff `Σ^c_M` has no antipodal pair.
- `Σ^c_M` is the set of one-sided directions.

Given them, together with `antipodal-one-sided-group-shift-configurations-are-walls`, a group shift is
quantum rigid iff it is wall-rigid. So for algebraic shifts, `wall-rigid-z2-sft-is-quantum-rigid` is the
Bieri–Strebel theorem.

**Calibration.** For `f = 1 + x + y` (Ledrappier), `M ⋊ Z^2` is Baumslag's lamp group over
`F_p[t^(±1), (1+t)^(-1)]`, recalled as finitely presented. That matches
`ledrappier-crossed-product-is-finitely-presented`.

Route: `group-shift-crossed-product-fp-from-lamp-group-fp-proof`.

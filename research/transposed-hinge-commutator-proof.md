---
rg: 2
id: transposed-hinge-commutator-proof
kind: route
title: Substitute the two expressions of the common product into the conjugated commutator
target: transposed-hinges-are-conjugated-commutators
requires: []
artifacts:
  - research/artifacts/hinge-closure-window-folding-2026-09-12.md
---

Section 2 of the artifact.

Expand `s'^(-1) [m'^(-1) m, c] s'` as `s'^(-1) m'^(-1) m c m^(-1) m' c^(-1) s'`. Since
`c = s' m'`, the tail `m' c^(-1) s'` equals `m' m'^(-1) = 1`. Since `c = s m`, the
middle `m c m^(-1)` becomes `m s`. What remains is `s'^(-1) m'^(-1) m s`, which is
`(m' s')^(-1)(m s)`.

The hinge is trivial iff the commutator is, that is, iff `m'^(-1) m` commutes with `c`.
A conjugate of a commutator lies in the commutator subgroup. For `s' = 1` we have
`c = m'`, and `[m'^(-1) m, m'] = m'^(-1) m m' m^(-1) = [m'^(-1), m]`. For the defect,
`m'^(-1) = u c u^(-1)` and `m = l`, so the hinge is `[u c u^(-1), l]`, and
`s l = u c^(-1) u^(-1) = m'` confirms the rooted identification.

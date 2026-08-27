---
rg: 2
id: torsion-free-non-mf-from-normal-kazhdan-defect
kind: route
title: Apply the normal-Kazhdan obstruction to the Fournier-Facio torsion-free group
target: torsion-free-finitely-presented-non-mf
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
---

## Why sufficient

Let `G` be the Fournier-Facio group: finitely presented, torsion-free, with
property (T), compression core `(Gamma, t_1, c in J)`, and a copy `S'` of
the finitely presented simple torsion-free group `S` inside its compression
defect (`fournier-facio-torsion-free-skeleton`).

Put `K = <<S'>>^G`.  It is normal in `G` by construction, nontrivial because
`S' != 1`, and contained in `defectNormal` because that subgroup is normal
and contains `S'`.  By
`defect-normally-generates-torsion-free-quotient`, `K` has property (T).

`normal-kazhdan-defect-non-mf` now applies verbatim: every homomorphism from
`G` into the unitary group of a norm matrix corona kills `K` elementwise.
Since `K != 1`, no such homomorphism is injective, so `G` is not MF — while
being torsion-free and finitely presented.

This is the primary route into the root.  Its two established prerequisites
are of different kinds and neither is new mathematics owed by this project:
the analytic half is machine-checked in this repository and needs no torsion
at any step, and the group-theoretic half is published.  The whole remaining
content of the root is the third prerequisite, which is combinatorial group
theory about a small-cancellation quotient — no operator algebra appears in
it.

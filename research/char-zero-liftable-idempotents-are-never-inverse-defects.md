---
rg: 2
id: char-zero-liftable-idempotents-are-never-inverse-defects
kind: claim
title: An idempotent of a modular group algebra with a finite-support characteristic-zero idempotent lift has nonzero class and is never an inverse defect
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that computes the lifted trace on projectives induced from finite subgroups; this evaluates it on any finite-support characteristic-zero idempotent lift, whose support may generate an infinite subgroup, and uses Kaplansky positivity to make it nonzero.
  ternary-anti-central-kernel-unitization-not-directly-finite: that is the open request for an invisible pair on the ternary anti-central summand; this is an established exclusion of every defect that lifts to characteristic zero, for every group and every prime.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Let `G` be any group, `p` a prime, and `d` a nonzero idempotent of `M_n(F_p[G])` that is the
reduction of an idempotent `D` of `M_n(Z_p[G])` with finite support. Then:

1. The lifted trace `t_p([d])` equals `T(D)`, the sum of the diagonal identity coefficients of `D`,
   and it is nonzero. So `[d] != 0` in `K_0(F_p[G])`.
2. For every `m >= 0`, `d (+) 0_m` is not the defect `1 - ac` of any pair `ca = 1` in
   `M_(n+m)(F_p[G])`. Nor is `d` of the form `e - f` for an infinite idempotent `e ~ f < e`.

*Why.* Any pair makes `T` vanish on an idempotent lift of its defect, and lifts are conjugate. Over
a finitely generated subfield of `Q_p`, embedded in `C`, Kaplansky positivity on `C*_r(G)` makes
`T(D) > 0` unless `D = 0`.

**Consequences.**
* **Linear characters.** For linear-character idempotents `e = E_(psi1)`, `f = E_(psi2)` of finite
  subgroups of order prime to `p`, `f e = f` iff `H1 <= H2` and `psi2|H1 = psi1`. So mixed pairs of
  linear characters collapse into one finite subgroup, where `[e] - [f]` has positive lifted trace.
* **Surviving defects are genuinely modular.** No finite-support idempotent lift exists. For a
  difference of finite-subgroup idempotents, the order relation must hold only modulo `p`, which
  needs cancellation from non-linear characters or from `p`-singular subgroups.

Proof: Sections 8.1 and 8.3 of the artifact.

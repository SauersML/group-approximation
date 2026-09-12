---
rg: 2
id: kazhdan-projection-is-norm-limit-of-finite-averages
kind: claim
title: The Kazhdan projection is a norm limit of finitely supported probability averages
distinct_from:
  kazhdan-projection-not-in-l1: that says the Kazhdan projection is not in the image of l^1 and that the averages are not l^1-Cauchy, which closes averaging on Banach targets; this says the same averages do converge in the C*_max norm, and the two statements are compatible.
  kazhdan-projection-finite-target-calculus: that is the exact projection calculus in a finite C*-target, obtained from the universal property; this is the approximation statement that lets one estimate the projection by a finite sum of unitaries in any target.
  kazhdan-projection-rounding: that rounds an almost-invariant projection into a relative commutant inside one finite tracial algebra; this approximates the Kazhdan projection itself in the maximal group algebra.
artifacts:
  - research/artifacts/shorter-proofs-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `L` have property (T) with finite Kazhdan generating set `S`.  For every
`epsilon > 0` there are a finite `F subset L` and weights `mu(l) >= 0` with
`sum_l mu(l) = 1` such that

```text
a = sum_(l in F) mu(l) u_l  in  C*_max(L),
||a - e_L|| < epsilon.
```

The weights are probabilities, so no trivial-character correction is needed
when `a` is used in place of `e_L`: for any homomorphism `pi : L -> U(B)` and
any bounded sequence, the substitution costs `epsilon` and nothing else.

This is the one averaging fact behind both analytic steps of the manuscript:
the transport theorem and the normal-Kazhdan theorem.

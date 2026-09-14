---
rg: 2
id: leavitt-kaplansky-failures-have-invisible-witnesses
kind: claim
title: Every direct-finiteness failure of the Leavitt unit group algebra yields an invisible one
distinct_from:
  leavitt-inverse-defects-are-visible-or-invisible: that normalizes one pair by translating with a single group element into exactly one of two forms; this converts every pair, visible ones included, into an invisible pair, so the two forms are nested rather than independent.
  leavitt-evaluation-kernel-unitization-not-directly-finite: that is the open invisible lifting problem; this is the established implication from any failure of the whole group algebra to that problem, and asserts no failure.
artifacts:
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Let `S = F_2[L_(F_2)(1,2)^x]`, `pi : S ->> R` the evaluation, `K = ker pi` and
`K^+ = F_2 1 + K`. If `b a = 1 != a b` in `S`, then `alpha = Phi(a)` and
`beta = Phi(b)`, with `Phi(x) = delta(x) z + e` of
`leavitt-unit-group-algebra-embeds-in-kernel-corner`, satisfy

    beta alpha = 1,     alpha beta != 1,     pi(alpha) = pi(beta) = 1,

and the defect `1 - alpha beta = delta(1 - ab) z` lies in `K`.

Consequences (Corollary 4 of the artifact):

1. `S` is directly finite if and only if `K^+` is directly finite.
2. A left-invertible lift of `s_0` (the visible problem) yields a failure of `K^+`
   (the invisible problem). The invisible problem is therefore the whole Kaplansky
   question for `R^x`, and the visible problem is a strictly more specific sufficient form.
3. `leavitt-evaluation-kernel-unitization-directly-finite` alone settles direct
   finiteness of `S` and excludes every left-invertible lift of `s_0`.

The converse conversion, from an invisible pair to a visible one, is not known.

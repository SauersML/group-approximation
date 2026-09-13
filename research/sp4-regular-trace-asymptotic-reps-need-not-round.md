---
rg: 2
id: sp4-regular-trace-asymptotic-reps-need-not-round
kind: claim
title: Sp_4(Z) has asymptotic representations with regular limit trace that no genuine representation of the same dimension approximates
distinct_from:
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that gives some non-roundable asymptotic representation of an infinite hyperlinear Kazhdan group, with no control of its trace; this pins the limit trace to the regular character delta_e for Sp_4(Z), so even the single-character strict rounding statement fails.
  sp2g-z-flexibly-hs-stable: that is flexible HS-stability of Sp_2g(Z), the input of the conditional route non-hyperlinear-from-sp2g-flexible-hs-stability; the witnesses here are corners of genuine representations, so they say nothing about flexible or corner rounding.
artifacts:
  - research/artifacts/ideas-2026-09-13/nh/nh-approx-lifting.md
---

**Statement.** Let `Gamma = Sp_4(Z)` with a finite symmetric generating set `S`
that contains a finite Kazhdan set. Write `||x||_2 = tr_k(x^* x)^(1/2)` with
`tr_k` the normalized trace. Then there are `k_n -> infinity` and maps
`phi_n : Gamma -> U(k_n)` with three properties.

1. **Asymptotic.** `||phi_n(g) phi_n(h) - phi_n(gh)||_2 -> 0` for all `g, h`.
2. **Regular trace.** `tr_(k_n)(phi_n(g)) -> delta_e(g)` for all `g`.
3. **No same-dimension rounding.** There is `c > 0` such that for all large `n`
   and every homomorphism `rho : Gamma -> U(k_n)`,
   `max_(s in S) ||phi_n(s) - rho(s)||_2 >= c`.

## What this kills and what it leaves

- **Killed.** Approach 6 of `research/artifacts/ideas-2026-09-13/nh/nh-approx-lifting.md`
  isolated the regular-character rounding statement `(RCR)`: asymptotic
  representations of `Sp_4(Z)` whose traces tend to `delta_e` are HS-close to
  genuine representations. In its strict, same-dimension form `(RCR)` is false.
- **Left untouched.** Each witness `phi_n` is a codimension-one corner of the
  genuine representation it compresses, so flexible or corner rounding is
  untouched. Dogon–Vigdorovich's rigidity theorem for corners
  (arXiv:2506.20843, TeX label `thm:NPS_analog`) consumes a corner
  `q_n rho_n q_n` of positive normalized size. The regular-character input
  therefore survives only in that corner form, which is the existing open
  conditional `sp2g-z-flexibly-hs-stable` through
  `non-hyperlinear-from-sp2g-flexible-hs-stability`.

The proof is in `sp4-regular-trace-asymptotic-reps-need-not-round-proof`. This
claim stays OPEN until the import `sp4-fp-regular-principal-series-irreducible`
is checked at source.

---
rg: 2
id: thompson-f-ore-window-kernel-profiles-monotone-binomial-floor
kind: claim
title: The window kernel dimensions of a pair in Guba's problems for Thompson's F are nondecreasing, vanish identically for a non-Ore pair, and once positive grow at least like a binomial coefficient
distinct_from:
  thompson-f-p22-over-f2-exhaustive-degree-seven-census: that records which P_(2,2) pairs have a common right multiple of degree at most seven; this describes how the solution-space dimension on the letter windows behaves degree by degree, for every field and every pair.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term and division-ring invariants as certificates of a non-Ore pair; this shows the kernel-dimension profile carries no information about a never-settled pair.
artifacts:
  - research/artifacts/hl-f-kernel-profiles-2026-09-14.md
---

**ESTABLISHED** through `thompson-f-ore-window-kernel-profiles-proof` (elementary; not independently
reviewed; no priority claimed).

**Setting.** Let `K` be a field, `M` the positive monoid of Thompson's group `F` with normal forms
`x_(i_1) ... x_(i_D)`, `i_1 <= ... <= i_D`, and let `a, b ∈ K[S_(3,5)]` be nonzero, where `S_(3,5)` is the
set of nine monomials of Guba's Problem `P_(2,2)`. This covers every pair of `P_(2,2)`, and every pair of
`P_(2,1)` since `S_(2,4) ⊂ S_(3,5)`. For
`D >= 0` let `W_D = M_(D, D+3)` be the normal forms of degree `D` with letters `<= D+3`, and

`k_D(a, b) = dim_K { (u, v) ∈ K[W_D]^2 : a u = b v }`.

By Step 2 of `thompson-f-p22-over-f2-census-exhaustive-proof`, the least `D` with `k_D > 0` is the
minimal degree `δ(a, b)` of a nonzero common right multiple, and `δ = ∞` iff `k_D = 0` for all `D`.

1. **Monotone.** `k_D <= k_(D+1)` for every `D`.
2. **Binomial floor.** If `δ = δ(a, b) < ∞`, then for every `D >= δ`
   `k_D(a, b) >= C(2D + 3 − δ, D − δ)`,
   the number of normal forms of degree `D − δ` with letters `<= D + 3`.
3. **No profile data for never-settled pairs.** If `δ(a, b) = ∞` the profile `(k_D)` is identically zero.
   So a kernel-dimension profile computed through any finite degree only restates whether `δ` is at most
   that degree. No recurrence or growth pattern read off profiles can certify `δ = ∞`, i.e. a non-Ore
   pair.

**Calibration (exact, `K = F_2`, in the artifact).** The floor in item 2 is attained exactly on several
settled pairs through degree 7, e.g. the `S_(2,4)` pair `(1, 2)` with `δ = 1` has
`k_D = C(2D + 2, D − 1)` for `D = 1..7`. Other pairs exceed it, which records further independent
generators of the right module `{(u, v) : a u = b v}`.

**Relation to the root.** Item 3 kills the kernel-profile route as a way to certify
`thompson-f-is-not-amenable` (idea 3 of `research/artifacts/ideas-f-hyperbolic-2026-09-13.md`). It says
nothing about `thompson-f-is-amenable`.

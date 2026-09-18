---
rg: 2
id: co-sofic-free-group-irs-counting-proof
kind: route
title: Count image configurations on a finite Schreier graph using rank-m ball bounds, exclude reverse-bad patterns at separated sites, and pass to weak-* limits
target: co-sofic-free-group-irs-carry-no-strict-design
requires: []
artifacts:
  - research/artifacts/co-sofic-irs-rank-corrected-counting-2026-09-17.md
---

Complete direct proof: artifact Sections 1-3. Notation: `F_m` is the group, `rho = R_tau + R_sigma`, and
`b_k` is the ball size in the `2m`-regular tree, so `|B_k(v)| <= b_k` in every Schreier graph of `F_m`.
Take a finite `F_m`-set `X` with `|X| = N`, non-forward-good fraction `eps`, reverse-bad fraction
`delta`, and forward-good set `Good`. Assume `|A| >= 2`; for `|A| = 1` no vertex is reverse-bad.

1. **Lower bound.** `y -> (sigma y)|Good` maps `tau(A^X)` onto `A^Good`, so
   `|tau(A^X)| >= |A|^((1-eps)N)`.
2. **Excluded patterns.** Let `v` be reverse-bad with witness `p_v` on `B_rho(v)`, and suppose
   `B_(R_tau)(v) ⊆ Good`. For `y = tau x`, `sigma y = x` on `B_(R_tau)(v)`, so `tau sigma y(v) = y(v)`,
   and therefore `y|B_rho(v) != p_v`.
3. **Exceptions.** The reverse-bad vertices failing that hypothesis lie within distance `R_tau` of
   `X \ Good`. There are at most `eps N b_(R_tau)` of them.
4. **Separation.** A greedy `2 rho`-separated subset `D'` of the remaining reverse-bad vertices has
   `|D'| >= (delta - eps b_(R_tau)) N / b_(2 rho)`, and its `rho`-balls are disjoint. Hence
   `|tau(A^X)| <= |A|^N (1 - |A|^(-b_rho))^|D'|`.
5. **Combine.** Using `ln(1-u) <= -u`, `|D'| <= eps N |A|^(b_rho) ln|A|`. So
   `delta <= (b_(R_tau) + b_(2 rho) |A|^(b_rho) ln|A|) eps`.
6. **Limit.** Both events depend on the labelled `rho`-ball of the root, which is determined by which
   words of length `<= 2 rho + 1` lie in the stabilizer. So they are clopen in `Sub(F_m)`. `eps_D` and
   `delta_D` are then weak-* continuous. On `mu_X` they equal `eps` and `delta`, because the orbit of `o`
   rooted at `o` is isomorphic to `Stab(o)\F_m`. The inequality defines a closed set containing every
   `mu_X`, hence every co-sofic IRS.

Separating the rank `m` from `rho` answers both referee refutations of `co-sofic-irs-carry-no-strict-design`.
Their counterexamples satisfy the corrected bound (artifact Section 4).

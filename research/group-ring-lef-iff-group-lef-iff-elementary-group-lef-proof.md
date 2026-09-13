---
rg: 2
id: group-ring-lef-iff-group-lef-iff-elementary-group-lef-proof
kind: route
title: LEF data of the group extend linearly through regular representations, units recover the group, the Whitehead identity embeds it in EL_2, and Følner truncation gives the rank function
target: group-ring-lef-iff-group-lef-iff-elementary-group-lef
requires: []
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part1.md
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

The full argument is Lemma L5 of `research/artifacts/un-calibration-table-2026-09-13-part1.md`, and rows 14–15 of part 2.

1. **(ii) ⇒ (i).** Take LEF data `σ_i: F_i → Q_i` with `F_i ↑ Γ`, and put `ρ_i(Σ a_g g) = Σ_(g∈F_i) a_g λ_(Q_i)(σ_i(g))`.
   - If `supp x`, `supp y` and `supp x · supp y` lie in `F_i`, then `ρ_i(xy) = ρ_i(x) ρ_i(y)`.
   - The matrices `λ(q)` are linearly independent, since `λ(q) δ_e = δ_q`.
   
   So `[ρ_i]` is a unital injective ring homomorphism into `∏_ω M_(|Q_i|)(F_q)`.
2. **(i) ⇒ (ii), (iii).** `GL_n` of a LEF ring embeds in an ultraproduct of finite groups (L4). This contains `Γ ⊆ F_q[Γ]^×` and
   `EL_n(F_q[Γ])`, so both are LEF.
3. **(iii) ⇒ (ii).** With `w(u) = e_12(u) e_21(−u^(−1)) e_12(u) = [[0, u], [−u^(−1), 0]]`, we get `w(u) w(−1) = diag(u, u^(−1))`. So
   `g ↦ diag(g, g^(−1), 1, …)` embeds `Γ` in `EL_n(F_q[Γ])`, and LEF passes to subgroups.
4. **Amenable `Γ`.**
   - Truncate left multiplication to Følner sets `B_n`. This is multiplicative up to `o(|B_n|)` rank, which gives a Sylvester rank
     function.
   - For `0 != x` with support `S`, the interior points `h` with pairwise disjoint `Sh` number at least `|B_n| / |S|^2 − o(|B_n|)`, and
     the vectors `x δ_h` for these `h` are linearly independent. So `rk(x) >= 1/|S|^2`, and the rank function is faithful.
   - L2 then gives stable finiteness.
   - Units inject into the rank-metric ultraproduct with `rk(g − h) > 0` (a nonzero entry has positive rank), so `EL_n(F_q[Γ])` is
     `F_q`-linear sofic.
5. **Item 3.** `F_q[Γ]` is finitely generated when `Γ` is, so EJZ gives (T) for `n >= 3`, as quoted in L7 of part 1. Not LEF follows
   from item 1, since `Γ` is not LEF.

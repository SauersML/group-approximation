---
rg: 2
id: subshift-elementary-group-conjugacy-degree-is-jump
kind: claim
title: For every Turing degree d there is an infinite minimal subshift X such that G_X has word problem of degree d and conjugacy problem of degree d′; some G_X has solvable word problem and unsolvable conjugacy problem
distinct_from:
  subshift-elementary-group-word-problem-degree: that computes the word-problem degree L(X) for every X; this separates the conjugacy problem from the word problem by a jump, for one explicit S-adic family.
  subshift-el-transvection-conjugacy-full-group-equivalence: that identifies transvection conjugacy with full-group equivalence for every X; this builds subshifts where that equivalence is Σ^0_1-complete relative to the language.
artifacts:
  - research/artifacts/sk-free-3-conjugacy-problem-2026-09-13-part1.md
  - research/artifacts/sk-free-3-conjugacy-problem-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** For every set `S ⊆ N` there is an infinite minimal subshift `X ⊆ {s,t,w}^Z` with `WP(G_X) ≡_T S` and `CP(G_X) ≡_T S′`, where `G_X = EL_3(LC(X,F_2)⋊Z)`.

With `S` computable, `G_X` is an infinite, finitely generated, simple Kazhdan LEF group whose word problem is solvable and whose conjugacy problem has degree `0′`.

**Upper bound, for every X.** `CP(G_X) ≤_T L(X)′`, by searching for a conjugator with the `L(X)`-decidable word problem.

**Construction.** Directive sequence `τ_m(c) = s^{k_m}·π_m(c)·W_m·t` over growing alphabets `Σ_m = {s,t,w} ∪ {x_e,y_e : e ∈ E_m}`. Here:
- `E_m` is the set of oracle machines `e < m` not yet halted after `m−1` steps;
- `W_m` lists every letter of `Σ_m` once;
- `k_m = 2 + S(m)`;
- payloads carry `x_e`, `y_e` while `e` runs and drop them once `e` halts.

**Properties.**
- Markers make every level recognizable.
- `W_m` gives minimality.
- Constant block lengths give aperiodicity.
- `L(X) ≡_T S`.

**The dichotomy.** For the clopen pairs `A_e`, `B_e` (the starts of level-`(e+1)` blocks of `x_e`, respectively `y_e`):
- if `M_e^S` halts, all later blocks balance, so `1_{A_e} − 1_{B_e}` is a coboundary;
- if not, propriety makes any transfer function constant at block boundaries, while a block of `x_e` has sum 1, so it is not a coboundary.

With `subshift-el-transvection-conjugacy-full-group-equivalence`, `e ↦ (e_13(1_{A_e}), e_13(1_{B_e}))` reduces `S′` to `CP(G_X)`.

**Firewall.** This does NOT say that `CP(G_X) ≡_T L(X)′` for every `X`. Sturmian subshifts with computable slope have a decidable coboundary problem on cylinders (`K^0 = Z + αZ`).

---
rg: 2
id: kl-p-square-system-individual-solvability-proof
kind: route
title: Conjugate each rewritten relator into Klyachko's multivariable form, then amalgamate over the torsion-free subgroup
target: kl-p-square-system-equations-are-individually-solvable
requires: [klyachko-multivariable-equation-with-nonpower-content-solvable, kl-p-power-index-reduces-to-p-nonsingular-square-systems]
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
---

Notation of the target. Write `w = s_1 ... s_k` with letters in
`G ∪ {t, t^(-1)}`.

**Shape of `rho_q`.** By route `kl-p-power-index-p-nonsingular-proof`, step 3,
`rho_q = tau_w(q) = prod_j tau_(s_j)(q phi(s_1 ... s_(j-1)))`:
- a letter `s_j in G` contributes an element of `H`;
- `s_j = t` contributes the single letter `y_(q phi(s_1...s_(j-1)))`;
- `s_j = t^(-1)` contributes the single letter `y_(q phi(s_1...s_j))^(-1)`.

Multiply consecutive `H`-contributions. Then

    rho_q = h_0 y_(x_1)^(eps_1) h_1 y_(x_2)^(eps_2) h_2 ... y_(x_r)^(eps_r) h_r,
    h_i in H,  eps_i in {1, -1},

with exactly one unknown letter for each occurrence of `t^(±1)` in `w`. The
content is `v_q = prod_i y_(x_i)^(eps_i)`, and its exponent sum is
`sum_i eps_i = m`.

**1. Single equations.** Conjugating by `h_r` gives

    h_r rho_q h_r^(-1) = (h_r h_0) y_(x_1)^(eps_1) h_1 y_(x_2)^(eps_2) ... h_(r-1) y_(x_r)^(eps_r),

which has the normal closure of `rho_q` and is exactly Klyachko's form (**) over
the torsion-free group `H`, with coefficients `g_1 = h_r h_0` and
`g_(i+1) = h_i`, variables `y_(x_i)` and the same content `v_q`. By
`klyachko-multivariable-equation-with-nonpower-content-solvable`, it is solvable
over `H` when `v_q` is not a proper power in `F(Y)`.

At `m = ±1`, `v_q` has exponent sum `±1` under `F(Y) -> Z`, `y_x -> 1`. A
proper power `u^k`, `k >= 2`, has exponent sum `k` times that of `u`, which is
never `±1`, and `v_q != 1`. So the hypothesis holds for every `q`.

**2. Variable-disjoint subsystems.** For each `q in S`, part 1 gives a group
`L_q` containing `H` as a subgroup and elements `ybar_x in L_q`, `y_x in U_q`,
with `rho_q(ybar) = 1` in `L_q`. Let `L` be the amalgamated free product of the
groups `L_q`, `q in S`, over their common subgroup `H` (identity on `H` in every
factor).
- By the normal form theorem for amalgamated free products, `H` and every `L_q`
  embed in `L`.
- Since the `U_q` are pairwise disjoint, the assignment `y_x -> ybar_x` (using
  the unique `q in S` with `y_x in U_q`, and `y_x -> 1` for unknowns in no `U_q`)
  is well defined.
- Each `rho_q`, `q in S`, involves only unknowns from `U_q`, and holds in
  `L_q ⊆ L`.

So `L ⊇ H` contains a solution of `{rho_q = 1 : q in S}`, i.e. that subsystem is
solvable over `H`.

**3. Where a violation must sit.** Suppose `m = ±1`. By
`kl-p-power-index-reduces-to-p-nonsingular-square-systems`, non-injectivity of
`G -> G_w` is the same as non-solvability of the whole square system over `H`.
Parts 1 and 2 solve every single equation and every variable-disjoint subsystem.

After the gauge `t -> t g` and the localization of
`kl-p-square-systems-are-connected-after-localization`, `U_q` is
`{y_x : x in q Lambda}` (its item 3). Two such sets meet iff `q^(-1) q'` lies in
`Lambda Lambda^(-1)`. Neither the gauge nor the localization changes
injectivity, so the obstruction is carried by pairs of equations adjacent in the
Cayley graph of `Q` with respect to `Lambda Lambda^(-1) \ {1}`.

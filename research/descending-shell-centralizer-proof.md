---
rg: 2
id: descending-shell-centralizer-proof
kind: route
title: Proof that descending window-zero shell endomorphisms have centralizers of finite exponent
target: descending-shell-endomorphisms-have-finite-exponent-centralizers
requires:
  - fw-shell-inputs-at-window-zero-are-highly-transitive
  - fw-window-zero-descending-sign-proof
---

**Setup.** By `fw-window-zero-descending-sign-proof` Steps 1--2 (with `θ = ψ`) there are a
cofinite `ρ(P)`-invariant `N_1` and an injective `s' : N_1 -> N`, near equal to `s`, with
`s'(ρ_g x) = ρ_(ψ(g)) s'(x)` exactly for `x in N_1`. By
`fw-shell-inputs-at-window-zero-are-highly-transitive`, the infinite `P`-orbits are finitely
many, `O_0, ..., O_(p-1)`, their union is cofinite, and `P` acts highly transitively on each.
Each `O_r` lies in `N_1`, since `N_1` is `P`-invariant and cofinite. So `s'` carries the
`P`-set `O_r` isomorphically, along `ψ`, onto `s'(O_r)`, and `ψ(P)` acts highly transitively
on each `s'(O_r)`. Every other `ψ(P)`-orbit lies in the finite set
`N - (s'(O_0) ∪ ... ∪ s'(O_(p-1)))`.

**Lemma.** If a group acts 2-transitively on a set `Y` with `|Y| >= 3`, its centralizer in
`Sym(Y)` is trivial. If `c` fixes some `y`, it fixes `gy` for all `g`, hence everything. If
`cy = y' != y`, pick `z` outside `{y, y'}` and `g` with `gy = y`, `gy' = z`; then
`cy = cgy = gcy = gy' = z`, contradicting `cy = y'`.

**Item 1.** Let `c` be in `C_P(ψ(P))`. Then `ρ_c` commutes with `ρ(ψ(P))`, so it permutes the
`ψ(P)`-orbits and preserves their sizes, hence permutes the `p` sets `s'(O_r)`. Some power
`c^k` with `k | p!` preserves each of them, and by the Lemma acts trivially on each. So
`ρ_(c^k)` has finite support, and `c^k = 1`.

**Item 2.** Let `Q <= C_P(ψ(P))` have no proper finite-index subgroup. The kernel of its
permutation action on the `p` sets `s'(O_r)` has finite index, so it is `Q`. By the Lemma `Q`
acts trivially on every `s'(O_r)`, so each of its elements has finite support, and `Q = 1`.
An infinite simple group has no proper finite-index subgroup, and `wψ(P)w^-1 ≅ ψ(P) ≅ P`
(`ψ` is injective under the infinite-support hypothesis).

**Item 3.** `L = L_(F_2)(1,2)` gives an FW group: `EL_n(L)` is Kazhdan, simple and infinite
(`binary-leavitt-elementary-groups-have-trivial-core-endomorphisms`, item 1). The unit
`u = s_2 t_1 + s_1 t_2` satisfies `u^2 = 1`, `u s_1 = s_2` and `t_1 u = t_2`, so the scalar
matrix `w = u I_n`, which lies in `GL_n(L) = EL_n(L)`, gives `w F(g) w^-1 = I + s_2 (g - I) t_2`.
Since `t_1 s_2 = 0 = t_2 s_1`,
`(I + s_1 X t_1)(I + s_2 Y t_2) = I + s_1 X t_1 + s_2 Y t_2 = (I + s_2 Y t_2)(I + s_1 X t_1)`.
So `w F(P) w^-1` is a conjugate of `F(P)` commuting with `F(P)`, and item 2 excludes (D1).

---
rg: 2
id: heisenberg-not-in-full-groups-of-z4-actions-proof
kind: route
title: A point locally free at scale ~j has no short Z^4-period and an injective displacement map on a j-ball; Pansu flattens its blow-down onto a plane, whose thin neighbourhood in Z^4 holds only ε^2 j^4 points
target: heisenberg-not-in-full-groups-of-z4-actions
requires:
  - faithful-heisenberg-actions-are-locally-free-at-every-scale
  - pansu-differentiability-of-lipschitz-carnot-maps
---

Norms on `Z^4` and `R^4` are `ℓ^1` unless marked `|·|_2`. `|·|_w` and `d_w`
are the word length and the left-invariant word metric of `H` for
`{a^{±1}, b^{±1}}`. `B_w(ρ)` is the word ball around `e`. This proof follows
`heisenberg-not-in-full-groups-of-z3-actions-pansu-proof` (the "rank-3 route")
with two changes:

- the lower count comes from exact injectivity, via
  `faithful-heisenberg-actions-are-locally-free-at-every-scale`;
- the upper count is taken in `R^4`.

## 0. Set-up

Let `ρ : H → [[Z^4 ↷ X]]` be a homomorphism, and suppose `ρ(c)` has infinite
order. Then `ρ` is injective, since a nontrivial normal subgroup of `H` meets
`⟨c⟩`. For `s ∈ {a^{±1}, b^{±1}}` choose `v_s : X → Z^4` with
`ρ(s)y = T^{v_s(y)}y` and `|v_s(y)| ≤ K`, where `K ≥ 1`. Each `Z^4`-orbit is
`ρ(H)`-invariant.

For `v ∈ X`, let `S_v` be its `H`-stabilizer and `Λ_v ≤ Z^4` its
`Z^4`-stabilizer.

**Word balls.** For `n ≥ 1`, `0 ≤ z ≤ n^2` and `|x|, |y| ≤ n`:

- `|c^z|_w ≤ 8√z + 2`, by (G2) below;
- so `|a^x b^y c^z|_w ≤ 12n`;
- these `(2n+1)^2(n^2+1) ≥ n^4` elements are distinct.

Hence `|B_w(ρ_w)| ≥ (ρ_w/24)^4` for `ρ_w ≥ 24`.

**Displacement along words.** If `ρ(h)v = T^D v` is reached by a word of length
`L` for `h`, the sum `D` of the steps has `|D| ≤ KL`. In particular
`ρ(B_w(ρ_w))v ⊆ {T^q v : |q| ≤ Kρ_w}`.

## 1. Locally free points have no short period vector

Let `v` satisfy `S_v ∩ B_w(R) = {1}`, with `R ≥ 48` and
`R > R_* := 48^4 · 6250 K^4`.

Suppose `λ ∈ Λ_v ∖ {0}` has `|λ| ≤ 10K`.

- **Counting the target ball.** For `r ≥ 1`, each point `T^q v` with
  `|q| ≤ r` gives the vectors `q + kλ`, `|k| ≤ r/|λ|`. They are distinct,
  lie in the ball of radius `2r` in `Z^4`, and are disjoint for distinct
  points, because a point determines `q mod Λ_v`. There are at least
  `r/|λ|` of them per point, and the ball holds at most
  `(4r+1)^4 ≤ 625 r^4` vectors. So
  `|{T^q v : |q| ≤ r}| ≤ 625|λ| r^3 ≤ 6250 K r^3`.
- **Injectivity.** `h ↦ ρ(h)v` is injective on `B_w(R/2)`, since
  `S_v ∩ B_w(R) = {1}`.
- **Contradiction.** This map sends `B_w(R/2)` into the set above with
  `r = KR/2`. So `(R/48)^4 ≤ 6250 K (KR/2)^3 ≤ 6250 K^4 R^3`, i.e.
  `R ≤ R_*`, a contradiction.

So `Λ_v` has no nonzero vector of norm `≤ 10K`.

## 2. The displacement map is injective on a ball

Let `v` be as in §1. Then `Λ_v` has no nonzero vector of norm `≤ 10K`.
Build `F : H → Z^4` exactly as in §2 of the rank-3 route. For a word
`w = s_n ⋯ s_1`, put `y_0 = v` and `y_i = ρ(s_i)y_{i−1}`, and let
`D(w) = Σ_i v_{s_i}(y_{i−1})`.

- **Backtracks.** A backtrack `ss^{-1}` contributes a vector in `Λ_v` of norm
  `≤ 2K`, so it contributes `0`.
- **Relators.** A relator loop (length 10) contributes a vector in `Λ_v` of
  norm `≤ 10K`, so it also contributes `0`.

So `F(h) = D(w)` is well defined, and it satisfies `F(e) = 0`,
`T^{F(h)}v = ρ(h)v` and `F(sh) = F(h) + v_s(ρ(h)v)`.

Put `f(g) = F(g^{-1})`. Then `|f(gs) − f(g)| ≤ K`, so `f` is `K`-Lipschitz
on `(H, d_w)`.

**Injectivity.** Suppose `f(g) = f(g')`. Then `ρ(g^{-1})v = ρ(g'^{-1})v`, so
`g'g^{-1} ∈ S_v`. Hence `f` is injective on every set `A ⊆ H` with
`|g|_w ≤ R/2` for all `g ∈ A`, since then `|g'g^{-1}|_w ≤ R`.

## 3. H as a lattice in G = H_3(R)

We use `G`, its CC distance `d`, its dilations `δ_λ`, the lattice
`Γ ≅ H`, and facts (G1)–(G6) with constants `C_1, C_2 ≥ 1`, `μ`, `δ_D`,
`c_6`, all from §4 of the rank-3 route. That section does not mention the
target group. We recall:

- **(G2)** `d_w(g,g') ≤ C_2 d(g,g') + C_2`, and `|c^s|_w ≤ 8√|s| + 2`.
- **(G3)** `d(g,g') ≥ μ > 0` for `g ≠ g'` in `Γ`.
- **(G6)** `|Γ ∩ B(z,ρ)| ≥ c_6 ρ^4` for every `z ∈ G` and `ρ ≥ 2δ_D`.

## 4. Blow-down

**Base points.** For each integer `j ≥ j_0 := ⌈(R_* + 48)/C_2⌉`, apply
`faithful-heisenberg-actions-are-locally-free-at-every-scale` to the
faithful action `ρ` on `X`, with `R_j = 6C_2 j`. This gives `v_j` with
`S_{v_j} ∩ B_w(R_j) = {1}`. Since `R_j > R_*` and `R_j ≥ 48`, §1 and §2
apply. They give a `K`-Lipschitz `f_j : H → Z^4` with `f_j(e) = 0` that is
injective on `{g : |g|_w ≤ 3C_2 j}`. Identify `H = Γ`.

**Rescaled maps.** For `g ≠ g'` in `Γ`, (G2) and (G3) give
`|f_j(g) − f_j(g')|_2 ≤ K d_w(g,g') ≤ K C_2(1 + 1/μ) d(g,g')`. Put
`φ_j(δ_{1/j}g) = f_j(g)/j` on `δ_{1/j}Γ`. It is `K_1`-Lipschitz into
`(R^4, |·|_2)`, where `K_1 = K C_2(1 + 1/μ)`.

Extend each coordinate by McShane's formula. This gives `u_j : G → R^4`,
`K_2`-Lipschitz for `K_2 = 2K_1`, with `u_j(e) = 0`.

**Limit.** `(G,d)` is proper, so by Arzelà–Ascoli and a diagonal argument a
subsequence converges uniformly on compact sets to a `K_2`-Lipschitz map
`u : G → R^4`. We still index this subsequence by `j`.

**Differential.**

- By `pansu-differentiability-of-lipschitz-carnot-maps` (target `R^4`), `u`
  is Pansu differentiable almost everywhere.
- The ball `B(e,1)` has positive Haar measure. So pick `x_0` with
  `d(x_0) < 1` at which `u` is differentiable, with group linear
  `L : G → R^4`.
- As in §5 of the rank-3 route, `L` kills the centre and
  `L(x,y,t) = x L(exp X) + y L(exp Y)`. So `L(G)` lies in a 2-plane
  `P ⊆ R^4`.
- `L(δ_λ h) = λL(h)` and `d(δ_λ h) = λ d(h)`, so
  `L(h) = lim_{λ→0} (u(x_0 δ_λ h) − u(x_0))/λ`. Hence
  `|L(h)|_2 ≤ K_2 d(h)`.

**Constants.** Put `C_5 = π^2 (K_2 + 3)^2`. Choose, in this order:

1. `ε ∈ (0,1)` with `9 C_5 ε^2 < c_6`;
2. `r ∈ (0,1]` with `|u(x_0 h) − u(x_0) − L(h)|_2 ≤ ε d(h)` whenever
   `d(h) ≤ r`;
3. `j ≥ j_0` in the subsequence with `sup_{B̄(x_0,r)} |u_j − u|_2 ≤ εr` and
   `rj ≥ max(2δ_D, 1/ε)`.

Let `A_j = Γ ∩ B(δ_j x_0, rj)`.

**Lower count.**

- Every `g ∈ A_j` has `d(g) ≤ d(δ_j x_0) + rj < 2j`.
- By (G2), `|g|_w ≤ 2C_2 j + C_2 ≤ 3C_2 j`.
- So `f_j` is injective on `A_j`.
- By (G6), `|f_j(A_j)| = |A_j| ≥ c_6 (rj)^4`.

**Upper count.**

- For `g ∈ A_j` put `y = δ_{1/j}g ∈ B(x_0, r)` and `h = x_0^{-1}y`, so
  `d(h) < r`.
- Then `f_j(g) = j u_j(y)` and
  `|u_j(y) − u(x_0) − L(h)|_2 ≤ |u_j(y) − u(y)|_2 + ε d(h) ≤ 2εr`.
- So `f_j(A_j)` lies within Euclidean distance `η = 2εrj` of the disc
  `D = j u(x_0) + {p ∈ P : |p|_2 ≤ K_2 rj}`.
- The unit cubes `p + [−1/2, 1/2]^4` for `p ∈ f_j(A_j)` have disjoint
  interiors. Each lies within distance `1` of its centre.
- So the cubes lie in the set of points `z` with
  `|pr_P(z − j u(x_0))|_2 ≤ K_2 rj + η + 1` and
  `|pr_{P^⊥}(z − j u(x_0))|_2 ≤ η + 1`. Here `P^⊥` is 2-dimensional.
- That set has volume `π(K_2 rj + η + 1)^2 · π(η + 1)^2`.
- Since `rj ≥ 1/ε ≥ 1` and `ε < 1`, `K_2 rj + η + 1 ≤ (K_2 + 3) rj` and
  `η + 1 ≤ 3εrj`.
- Hence `|f_j(A_j)| ≤ C_5 (rj)^2 · 9ε^2 (rj)^2 = 9 C_5 ε^2 (rj)^4`.

**Contradiction.** `c_6 (rj)^4 ≤ 9 C_5 ε^2 (rj)^4 < c_6 (rj)^4`. So `ρ(c)`
has finite order. ∎

## 5. Trust surface

- **Imported on this graph.**
  - `faithful-heisenberg-actions-are-locally-free-at-every-scale`
    (elementary, unreviewed). It is used in §4 and, through §1, rules out
    short periods. This replaces the quadratic-growth import and the lossy
    subgroup count of the rank-3 route.
  - `pansu-differentiability-of-lipschitz-carnot-maps` (target `R^4`).
- **Reused text.** The facts (G1)–(G6) and the linear-algebra description
  of `L` come from §4–§5 of
  `heisenberg-not-in-full-groups-of-z3-actions-pansu-proof`. They do not
  depend on the target dimension.
- **Standard, not imported.** McShane extension, Arzelà–Ascoli on a proper
  space, and presentations.
- **Why the rank-3 route stopped at 3.** Its lower count had only
  `(rj)^3`, because a stabilizer can meet a word ball in `~ρ` elements when
  `m_v ~ ρ^2`. Exact local freeness at scale `~j` restores `(rj)^4`. The
  planar upper count in `R^N` is `~ε^{N−2}(rj)^N`, which beats `(rj)^4` for
  `N ≤ 4` only. For `N ≥ 5` it does not, so `W(Z^5)` stays open.
  `heisenberg-group-embeds-in-wobbling-group-of-some-zn` gives `H ≤ W(Z^N)`
  for some large `N`.

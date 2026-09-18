---
rg: 2
id: free-group-boundary-shift-rigidity-proof
kind: route
title: The edge rule makes each edge carry one projection and its complement, so along any geodesic the backward-pointing projections form a commuting increasing chain that every label at every vertex sits in or against
target: free-group-boundary-shifts-are-quantum-rigid
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - quantum-rigidity-is-product-stable
---

Notation as in the target: `Λ`, `S`, the tree `T`, and `X_∂ ⊆ S^Λ`. Fix `D >= 1`, a field `k`, and a
`D`-quantum family `E_s(g)` (`s ∈ S`, `g ∈ Λ`) on a `k`-vector space `W`. Here (Q1) at each `g` the
`E_s(g)` are orthogonal idempotents summing to `I`; (Q2) idempotents at sites within distance `2D`
commute; (Q3) products over `B_D`-patterns that do not occur in `X_∂` vanish.

## Step 0. Coding (item 1)

- **Each `x` is an end.**
  - The edge rule orients every edge, and `x(g)` names one out-edge at each `g`. So `x` has exactly
    one out-edge at each vertex.
  - Following out-edges from `g` gives a path with no backtracking, since the edge just used points
    forward. In a tree that path is a ray `ρ_g`.
  - For two vertices `g, h`, the path between them contains no vertex with two out-edges on it. So its
    orientation is `g → … → g_k ← … ← h`, and `ρ_g`, `ρ_h` both pass through `g_k` and then agree.
  - All rays therefore share a tail, defining `ξ(x) ∈ ∂T`.
- **Each end is an `x`.** Conversely, `x_ξ(g)` = the first letter of the geodesic ray from `g` to `ξ`
  satisfies the edge rule.
- **Topology and dynamics.** `x ↦ ξ(x)` is a `Λ`-equivariant bijection, continuous both ways (cylinder
  sets correspond). The action on `∂T` is minimal and topologically free: a nontrivial `g` fixes at
  most two ends. It is not free, since a hyperbolic `g` fixes its attracting end.

## Step 1. Local identities

Fix an edge `{g, gs}` and put `P = E_s(g)`, `R = E_(s^(-1))(gs)`.

- **(a) `PR = RP = 0`.** The pattern `{g ↦ s, gs ↦ s^(-1)}` does not occur. Its extensions to
  `gB_D ⊇ {g, gs}` do not occur, so by (Q3) each product over `gB_D` vanishes. All idempotents on
  `gB_D` commute, by (Q2), since its diameter is `2D`. So the sum of these products over all extensions
  is `PR·∏_(other f) (Σ_a E_a(gf)) = PR`, which must vanish. The same argument gives `RP = 0`.
- **(b) `E_u(g)·E_v(gs) = 0` for `u ≠ s` and `v ≠ s^(-1)`.** Same argument: the pattern violates the
  edge rule.
- **(c) `R = I − P`.**
  - By (b) and (Q1), `(I − P) E_v(gs) = Σ_(u≠s) E_u(g) E_v(gs) = 0` for `v ≠ s^(-1)`.
  - So `(I − P)(I − R) = 0`, i.e. `I − P ≤ R`.
  - With (a), `R = R(P + (I − P)) = R(I − P) = I − P`, using that `R` and `P` commute (adjacent sites).

So each oriented edge `g → gs` carries one idempotent `O(g,s) = E_s(g)`, with `O(gs, s^(-1)) = I − O(g,s)`.

## Step 2. The chain along a geodesic

Let `g_0, g_1, …, g_n` be a geodesic, with `g_(i+1) = g_i s_i` and `s_i ≠ s_(i-1)^(-1)`. Put
- `P_i = E_(s_i)(g_i)` for `0 <= i < n`, the forward arrow at `g_i`;
- `Q_i = E_(s_(i-1)^(-1))(g_i)` for `1 <= i <= n`, the backward arrow at `g_i`.

For operators, write `A ⊑ B` for `AB = BA = A`, and `A ⊥ B` for `AB = BA = 0`.

- **(i)** `Q_(i+1) = I − P_i`, by Step 1(c).
- **(ii)** For `1 <= i < n`, `P_i ⊥ Q_i` by (Q1) at `g_i`, because the labels are distinct
  (`s_i ≠ s_(i-1)^(-1)`). Hence `Q_i ⊑ I − P_i = Q_(i+1)`.
- **(iii) Chain.** For `1 <= i < j <= n`, `Q_i ⊑ Q_j`, by induction on `j`:
  - `Q_i Q_j = (Q_i Q_(j-1)) Q_j = Q_i (Q_(j-1) Q_j) = Q_i Q_(j-1) = Q_i`;
  - `Q_j Q_i = Q_j (Q_(j-1) Q_i) = (Q_j Q_(j-1)) Q_i = Q_(j-1) Q_i = Q_i`.

  In particular all `Q_i`, and all `P_i = I − Q_(i+1)`, commute with one another.
- **(iv) Every label is in or against the chain.** Let `u ∈ S`.
  - At `g_i` with `0 <= i < n` and `u ≠ s_i`, and also `u ≠ s_(i-1)^(-1)` when `i >= 1`: `E_u(g_i) ⊥ P_i`
    by (Q1), so `E_u(g_i) ⊑ I − P_i = Q_(i+1)`. When `i >= 1`, also `E_u(g_i) ⊥ Q_i` by (Q1).
  - At `g_n` with `u ≠ s_(n-1)^(-1)`: `E_u(g_n) ⊥ Q_n`.
  - The remaining labels are `E_(s_i)(g_i) = I − Q_(i+1)` and `E_(s_(i-1)^(-1))(g_i) = Q_i`.

## Step 3. Every pair commutes (item 2)

Take `0 <= i < j <= n`. A label idempotent at `g_i` is `I − Q_(i+1)`, or `Q_i`, or a *side* idempotent
`A` with `A ⊑ Q_(i+1)` and (if `i >= 1`) `A ⊥ Q_i`. A label idempotent at `g_j` is `I − Q_(j+1)` (if
`j < n`), or `Q_j`, or a side idempotent `B` with `B ⊥ Q_j` (and `B ⊑ Q_(j+1)` if `j < n`).

- **Chain against chain.** Commute by (iii).
- **`A` against `Q_k`, `k >= i+1`.** `AQ_k = AQ_(i+1)Q_k = AQ_(i+1) = A` and
  `Q_k A = Q_k Q_(i+1) A = Q_(i+1) A = A`.
- **`B` against `Q_k`, `k <= j`.** `Q_k ⊑ Q_j` gives `BQ_k = BQ_j Q_k = 0` and `Q_k B = Q_k Q_j B = 0`.
- **`A` against `B`.** Using `A ⊑ Q_(i+1) ⊑ Q_j` and `B ⊥ Q_j`:
  - `AB = A Q_(i+1) B = A Q_(i+1)(Q_j B) = 0`;
  - `BA = B Q_(i+1) A = (B Q_j) Q_(i+1) A = 0`.

Hence any label idempotent at `g_i` commutes with any label idempotent at `g_j`. Any two sites of `Λ`
are the endpoints of a geodesic of `T`, so the whole family commutes, and `X_∂` is `D`-quantum rigid.
Only (Q1), and (Q2)–(Q3) on single edges, were used, so every `D >= 1` and every field work. ∎

## Step 4. Products (item 3)

`quantum-rigidity-is-product-stable` applies with both factors `D`-rigid by Step 3. That node's
dynamics clause gives minimality. For topological freeness: if `(g_1, g_2) ≠ 1` fixed a product open
set `U_1 × U_2` pointwise, then some `g_i ≠ 1` would fix `U_i` pointwise, contradicting item 1. ∎

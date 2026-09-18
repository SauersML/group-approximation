---
rg: 2
id: virtually-free-contracting-rsg-proof
kind: route
title: Code the ends of the Bass–Serre tree by left-normalized normal forms with the vertex-group head kept; left multiplication is a prefix replacement, same-type cones are matched by normal-form quotients, and minimal tree dynamics make the core irreducible
target: virtually-free-groups-are-contracting-rsgs
---

Lane `bh-free-52`, 2026-09-18. This is an elementary lane proof and has not been reviewed. BBMZ means Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224v3; its TeX is at `gq/src/bh-free-03/bbmz2-2309.06224.tex`. BBMZ definitions used: `Irreducible`, `Irreducible core`, Thompson-like homeomorphisms, `def:rsg`, and `def:contracting` (nucleus).

## 0. Setup

- **The graph of groups.** By Karrass–Pietrowski–Solitar, `G = π_1(𝔾, v_0)` for a finite connected graph of finite groups `𝔾` with underlying graph `X`.
  - For a directed edge `e` of `X`, write `o(e)` and `τ(e)` for its endpoints and `ē` for the reverse.
  - `G_e^τ ≤ G_{τ(e)}` is the image of the edge group.
- **Reduction.** Collapse leaves as follows. If a vertex `w` has degree 1, with edge `e` into it, and `G_e^τ = G_w`, contract `e`; this does not change `π_1`. After finitely many steps, no vertex `w` of degree 1 has its edge group surjecting onto `G_w`. Since `G` is infinite, `X` still has an edge.
- **The tree.** Let `T` be the Bass–Serre tree, which is locally finite. The reduction makes `T` leafless: a vertex of `T` of degree 1 would be exactly a reduced-away leaf.
- **The action on `T`.** `G` acts on `T` cocompactly, with quotient `X`.
  - A leafless tree with a cocompact action is minimal: a proper invariant subtree would leave vertices at bounded distance from it, hence a leaf.
  - Since `G` is not virtually cyclic, `T` is not a line and `G` fixes no end. So the action is minimal and non-elementary.
- **Transversals.** For each directed edge `e`, fix a set `S_e ∋ 1` of representatives of the left cosets `G_e^τ s` in `G_{τ(e)}`.

## 1. Normal forms and the coding

Serre's normal form theorem for graphs of groups (Trees, §I.5.2, Thm. 11), in the standard left-normalized transversal form: every element of the path group from `v_0` has a unique expression
`g_0 · e_1 s_1 · e_2 s_2 ⋯ e_n s_n`.
- Here `g_0 ∈ G_{v_0}` is arbitrary, the `e_i` form an edge path from `v_0`, and `s_i ∈ S_{e_i}`.
- It is reduced: `e_{i+1} = ē_i` implies `s_i ≠ 1`.
- The relation `e·a^τ = a^o·e` for `a ∈ G_e` pushes every edge-group element to the left, into the head `g_0`.

Letters: put `L_1 = (g_0, e_1)` and `L_i = (s_{i−1}, e_i)` for `i ≥ 2`.

The graph `Γ`:
- **Nodes:** a root `r`, plus one node for each directed edge `e` of `X`.
- **Edges out of `r`:** one edge `(g_0, e_1): r → e_1` for each `g_0 ∈ G_{v_0}` and each `e_1` with `o(e_1) = v_0`.
- **Edges out of `e`:** one edge `(s, e'): e → e'` for each `s ∈ S_e` and each `e'` with `o(e') = τ(e)`, excluding the pair `(e', s) = (ē, 1)`.

A finite path from `r` is exactly a reduced prefix. `α = L_1 ⋯ L_n` represents the path-group element `α̂ = g_0 e_1 s_1 ⋯ s_{n−1} e_n`, which ends at `τ(e_n)`, and `t(α) = e_n`. Put `E = C_r`, the set of infinite reduced words.

**No empty cones.** Node `e` has `|S_e|·deg(τ e) − 1 ≥ 1` out-edges, because the reduction rules out `deg = 1` together with `|S_e| = 1`.

## 2. The action

For `g ∈ G` and `y = L_1 L_2 ⋯ ∈ E` with prefixes `y_n`:
- **The rule.** Define `g·y` as the infinite word whose `n`-th prefix is the normal form of `g·ŷ_m` truncated, for `m ≫ n`. It is well defined because reduction is local.
- **Why only a bounded prefix changes.** Write `g = h_0 f_1 r_1 ⋯ f_L r_L` as a loop at `v_0` in normal form, and form `g·ŷ_m`.
  - Each cancellation `f ⋯ ē` at the junction consumes one edge letter of `g` and one of `ŷ_m`, so there are at most `L` of them.
  - The surviving tail `e_k s_k e_{k+1} ⋯` of `ŷ_m`, with `k ≤ L + 1`, is already normalized.
  - Left-normalization only rewrites what lies to the left of `e_k`.
  - So `L_{k+1}, L_{k+2}, …` are unchanged.
- **Consequences.**
  - Every `g` acts as a prefix replacement. There are a finite partition of `E` into cones `C_{α_i}` and cones `C_{β_i}` such that `g` maps `α_i ω ↦ β_i ω`, and `t(α_i) = t(β_i)` because the letter after the replaced prefix is unchanged.
  - So `g` is Thompson-like and `G → V_{Γ,E} ≤ R_{Γ,E}`.
  - It is a homomorphism, because normal forms of products are computed consistently.
- **Faithful.** A single fixed point does not force `g = 1`: `a` fixes `a^∞` in `F_2`. So suppose `g` acts trivially on all of `E`.
  - Take `y` whose tail after its first `L + 1` letters is not eventually periodic. Such tails exist, because `Γ_0` is not a directed cycle (§4).
  - `g` replaces a prefix `P` of `y` by a prefix `P′` and keeps the tail `τ`. If `|P′| ≠ |P|`, then `P′τ = Pτ` would make `τ` eventually periodic. So `|P′| = |P|`, and then `P′ = P`.
  - So `g·ŷ_m` and `ŷ_m` have the same normal form, hence are equal in the path group, and `g = 1`.
  - In particular a nontrivial finite normal subgroup acts nontrivially. On the head, an element of `N ∩ G_{v_0}` acts by `g_0 ↦ n g_0`.

## 3. The RSG property and the nucleus

- **The RSG property.** Let `C_α, C_β ⊊ E` be cones with `t(α) = t(β) = e`. Both `α̂` and `β̂` are path-group elements from `v_0` to `τ(e)`, so `h := β̂ α̂^{-1} ∈ π_1(𝔾, v_0) = G`.
  - For `α ω ∈ E`, we have `h·(α̂ ω̂) = β̂ ω̂`.
  - The concatenation `β ω` is reduced, because whether the next letter `(s, e')` is allowed depends only on the node `e`.
  - So `h` maps `C_α` onto `C_β` by the canonical similarity, which is `def:rsg`.
- **The nucleus.** By §2, for each `g` all but finitely many cones `C_α` are mapped to cones `C_β` by canonical similarities, and every such local action `g|_α` is `id_{C_{t(α)}}`. So `Nuc_G = {id_{C_v}}` is finite.

## 4. The irreducible core

Take `Γ_0` to be the full subgraph on the directed-edge nodes. Conditions (ii) and (iii) of `Irreducible core` hold with `N = 1`, since every edge out of `r` enters `Γ_0` and no edge leaves `Γ_0`. It remains to show that `Γ_0` is strongly connected and is not a directed cycle.

**Not a directed cycle.** If every node had exactly one out-edge, then `|S_e|·deg(τ e) = 2` for all `e`. So every vertex of `T` would have degree 2, and `T` would be a line, contradicting non-elementarity.

**Strongly connected.** Directed edges of `T` over a given `e` form one `G`-orbit. A path `e → ⋯ → e'` in `Γ_0` is exactly a non-backtracking edge path in `T` that starts with a lift `ε` of `e` and ends with a lift of `e'`: a letter `(ē, s)` with `s ≠ 1` is a different edge of `T` over `ē`. So it suffices to prove the following.

> For directed edges `ε, ε'` of `T`, some non-backtracking path starts with `ε` and ends with a `G`-translate of `ε'` (same orientation).

Two standard facts about minimal, non-elementary actions on trees (Culler–Morgan, *Group actions on R-trees*, Proc. LMS 55 (1987), §2–3):
- (F1) `T` is the union of the axes of hyperbolic elements.
- (F2) No `G`-orbit of ends is finite. Vertex stabilizers are finite, so the action is proper and end stabilizers are finite or virtually cyclic. A finite orbit would then make `G` virtually cyclic.

The proof.
1. **An axis through `ε` pointing into its half-tree.** By (F1), `ε` lies on the axis `L_h` of a hyperbolic `h`. Replacing `h` by `h^{-1}` if needed, `h` translates along `ε` towards the half-tree `T_ε` beyond `ε`. Write `ξ_±` for its attracting and repelling ends, so `ξ_+ ∈ ∂T_ε`.
2. **An axis through a translate of `ε'`, avoiding `ξ_−`.** By (F1), `ε'` lies on the axis `L'` of a hyperbolic `k`, oriented along the translation of `k` (again after replacing `k` by `k^{-1}` if needed). By (F2), some `g` has `ξ_− ∉ g·∂L'`: otherwise `G·ξ_−` would lie in the two-point set `∂L'`. Replace `ε'` by `gε'`, `L'` by `gL'`, and `k` by `gkg^{-1}`.
3. **Push that axis deep into `T_ε`.** The projection of `L'` to `L_h` is a segment, or a ray towards `ξ_+`, since `ξ_− ∉ ∂L'`. So for large `n`, the line `M := h^n L'` lies in `T_ε` at distance `≥ 1` from `τ(ε)`. `M` is the axis of `m := h^n k h^{-n}` and contains `h^n ε'` in the direction `m` translates.
4. **Build the path.** Let `σ` be the geodesic from `τ(ε)` to its first point `x` on `M`.
   - `σ` lies in `T_ε`, so `ε·σ` does not backtrack.
   - `σ` reaches `M` through an edge not on `M`, so either direction along `M` continues without backtracking.
   - Go along `M` in `m`'s direction far enough to cross `m^j h^n ε'` for large `j`. That is a translate of `ε'`, crossed in its own orientation.

## 5. Calibrations

- **`SL_2(Z) = ⟨a⟩ *_{⟨z⟩} ⟨b⟩`,** with `|a| = 4`, `|b| = 6` and `a^2 = b^3 = z`.
  - `X` is one edge `e: A → B`.
  - `S_e = {1, b, b^2}` and `S_ē = {1, a}`.
  - `Γ_0` consists of `e → ē` via `(b, ē)` and `(b^2, ē)`, and `ē → e` via `(a, e)`: strongly connected and not a cycle.
  - From `r` there are 4 edges `(g_0, e)`, one for each `g_0 ∈ ⟨a⟩`.
  - Points are `g_0 · b^{±1} a b^{±1} a ⋯`. The center `z` sends the head `g_0` to `a^2 g_0`.
- **`D_∞ = Z/2 * Z/2`, and `Z/4 *_{Z/2} Z/4`.** Here `|S_e| = |S_ē| = 2` and `deg = 1`, so `Γ_0` is a directed 2-cycle and there is no irreducible core. This matches the exclusion of the elementary case.
- **`F_2`, as one vertex with trivial group and two loops.** `Γ_0` is the non-backtracking graph on 4 directed loops, which is the standard free-group coding; the head is trivial.

---
rg: 2
id: nonascending-hnn-end-shifts-satisfy-e3-prime-proof
kind: route
title: Reduced HNN words turn the Bass–Serre tree boundary into the path space of a pseudo-free self-similar graph whose units are the edge groups; Li's Zappa–Szép theorem then gives F_n for V times it, and multiplicities merge through V
target: nonascending-hnn-end-shifts-satisfy-e3-prime
requires:
  - topologically-free-subshift-full-groups-force-quantum-rigidity
  - v-times-ample-full-groups-are-generated-by-transpositions
  - nekrashevych-symmetric-and-alternating-full-groups
  - fp-v-times-minimal-action-full-groups-have-type-a-actions
---

Lane proof (bh-e3prime, 2026-09-18). Elementary except for Li's theorem, whose hypotheses are listed
in Step 6 against the source (`$GQ/src/kep/li-garside-II-2110.04505v2.tex`, `thm:deg`, `thm:ZS`,
`rem:ZS-Stab`, `ex:ZS`, and (F) at l.1454–1456). Not reviewed. Notation is that of the target node.

## Step 0. Reduced words

- For a finite path `μ = (ε_1, h_1) ⋯ (ε_r, h_r)` in `E_T` put `μ̂ = h_1 t_(ε_1) ⋯ h_r t_(ε_r) ∈ Γ`.
- The rule `(ε_(i+1), h_(i+1)) ≠ (ε̄_i, 1)` is exactly Britton's condition that `t_(ε_i) h_(i+1)
  t_(ε_(i+1))` does not pinch, since `t_ε b t_ε^(-1) ∈ H` iff `b ∈ A_ε̄` and `T_ε̄ ∩ A_ε̄ = {1}`.
- So `μ ↦ μ̂ v_0` is a bijection from paths of length `r` starting at a state `ε_0` onto the vertices
  at distance `r` from `v_0` whose geodesic from `v_0` does not start with the edge `f_ε̄_0`. It
  extends to a homeomorphism `ω ↦ ω̂` from the infinite path space `∂Ω(ε_0)` onto
  `R_(ε_0) := ∂T ∖ Sh(f_ε̄_0)`, where `Sh(f)` is the set of ends beyond the far vertex of a directed
  edge `f`.
- `Sh(f_ε) = t_ε R_ε`, and the edges at `v_0` are the `h f_ε` (`h ∈ T_ε`), so
  `∂T = ⊔_ε ⊔_(h ∈ T_ε) h t_ε R_ε`. Put `Y_ε = Sh(f_ε)` and `Y = ⊔_ε Y_ε`.

## Step 1. The end shift is an SFT (item 1)

- **Equivariance and continuity.** `x_(ηξ)(γ) = x_ξ(η^(-1)γ)` by definition, and `x_ξ(γ)` depends
  only on the first `d(v_0, γ v_0) + 1` edges of the ray from `v_0` to `ξ`. So `ξ ↦ x_ξ` is continuous
  and equivariant. It is injective because the ray from `v_0` to `ξ` can be read off `x_ξ`.
- **The rules hold.** (R1): `x_ξ(γh)` is the first edge from `v_0 = h v_0` toward `h^(-1)γ^(-1)ξ`,
  which is `h^(-1) x_ξ(γ)`. (R2): put `ξ' = γ^(-1)ξ` and `w = t_ε v_0`. If the ray from `v_0` to `ξ'`
  starts with `f_ε`, the ray from `w` does not return to `v_0`; otherwise it starts with `[w, v_0]`.
  Now `x_ξ(γ t_ε) = t_ε^(-1)·(first edge from w toward ξ')`, and `t_ε^(-1)[w, v_0] = f_ε̄`.
- **Surjectivity.** Let `x ∈ X_T`. (R1) extends from generators to all of `H`, so `o(γ v_0) := γ·x(γ)`
  is a well-defined outgoing edge at each vertex. Every edge is `γ h f_ε`, and (R2) at `γh` says that
  exactly one endpoint of it points along it. So out-degree is 1, no edge is used in both directions,
  and following `o` from any vertex gives a ray. Adjacent vertices give the same end, so all vertices
  give one end `ξ`, and `o(w)` is the first edge from `w` toward `ξ`. Hence `x = x_ξ`.
- `∂T` is compact, so `ξ ↦ x_ξ` is a homeomorphism. The rules live on the windows `{1, h}` and
  `{1, t_ε}`, so `X_T` is an SFT.

## Step 2. Minimality (item 2)

- In `E_T` every state `ε` has an edge to every state `ε'`: take `h = 1` if `ε' ≠ ε̄`, and `h ≠ 1` in
  `T_ε̄` otherwise (index at least 2). Every state has `[H : A_ε] >= 2` loops.
- Each directed edge of `T` has a unique type `ε` (it is `γ f_ε`), and `Γ` is transitive on directed
  edges of each type. `Sh(γ f_ε) = γ t_ε R_ε ≅ ∂Ω(ε)`, and `Sh(f)` for `f` of type `ε` contains
  `Sh(f')` for a following edge `f'` of any prescribed type.
- Given an end `ξ` and a nonempty open `U`, pick `Sh(f) ⊆ U` and an edge `f_1` of type `ε_1` on the
  ray from `v_0` to `ξ`, directed toward `ξ`. By the previous bullet there is a directed edge `f'` of type `ε_1` beyond `f`, so
  `Sh(f') ⊆ Sh(f)`. Pick `γ` with `γ f_1 = f'`. Then `γ ξ ∈ Sh(f') ⊆ U`.

## Step 3. Topological freeness and (TF) (items 2 and 7)

- If `γ ≠ 1` fixes a nonempty open set of ends, it fixes some `Sh(f)`, which has at least two ends. So
  `γ` is not hyperbolic, and it fixes every ray into `Sh(f)`. `T` has no leaves, so every vertex
  beyond `f` lies on such a ray, and `γ` fixes the half-tree beyond `f` pointwise. The converse is
  clear. So topological freeness of `Γ ↷ ∂T` is exactly (TF).
- **Recursive form.** Conjugate the half-tree to `Y_ε ∪ {its vertices}`. Its pointwise fixator is
  `t_ε N_ε t_ε^(-1)`, where `N_ε ⊴ A_ε̄` is the kernel of `A_ε̄ ↷ R_ε`. The family `(N_ε)` is the
  largest family of subsets `N_ε ⊆ A_ε̄` such that every `u ∈ N_ε` lies in `h A_ε' h^(-1)` and has
  `θ_ε'(h^(-1) u h) ∈ N_ε'` for every allowed `(ε', h)` at `ε`. (TF) says `N_ε = 1` for all `ε`.
- **Residual finiteness.** Under (TF), `Γ` acts faithfully on `T`, so `H = Stab(v_0)` acts faithfully
  on the locally finite rooted tree `(T, v_0)`. The fixators of balls are finite-index normal
  subgroups of `H` with trivial intersection.
- **FA subgroups.** By Serre, an FA subgroup fixes a vertex, so it lies in a conjugate of `H`. So it
  is residually finite, and it is never infinite simple.

## Step 4. The self-similar action is the Γ-action in coordinates (item 3)

- For `g ∈ A_ε̄` and an allowed edge `(ε', h)` at `ε`, write `g h = h' a` with `h' ∈ T_ε'` and
  `a ∈ A_ε'`. Then `g h t_ε' = h' t_ε' θ_ε'(a)` in `Γ`, by the relation `a t_ε' = t_ε' θ_ε'(a)`.
  `(ε', h')` is allowed: if `ε' = ε̄` and `h' = 1`, then `gh ∈ A_ε̄`, so `h ∈ A_ε̄`, so `h = 1`.
- Iterating, `g μ̂ = (g·μ)^ φ(g, μ)` in `Γ` for every path `μ`, and Britton normal forms determine
  `g·μ` and `φ(g, μ)` uniquely. So the three cocycle identities and `g·(μν) = (g·μ)(φ(g,μ)·ν)` of
  Li's self-similar actions (`ss:ZS`) hold, because they are associativity in `Γ`. The action is
  degree preserving, and `g·ω̂ = (g·ω)^` on infinite paths.
- **Pseudo-freeness.** If `g·(ε', h) = (ε', h)` and `φ(g, (ε', h)) = 1`, then `a = h^(-1) g h` and
  `θ_ε'(a) = 1`, so `a = 1` and `g = 1`. By induction the same holds for every path.
- **Right cancellativity of `D = C_(E_T) ⋈ 𝔊`.** Suppose `(a, g)(b, k) = (a', g')(b, k)`. Then
  `a (g·b) = a' (g'·b)` and `φ(g, b) = φ(g', b)`. Lengths and unique factorization give `a = a'` and
  `g·b = g'·b`. The cocycle identity gives `φ(g'^(-1) g, b) = φ(g'^(-1), g'·b) φ(g', b) = 1`. So
  pseudo-freeness gives `g = g'`. By Li l.1456, condition (F) holds for `D`.

## Step 5. The groupoids coincide under (TF) (item 3)

- **Pseudogroups.** Let `P` be the pseudogroup on `Y ≅ ⊔_ε ∂Ω(ε)` generated by prefix maps
  `μ : ∂Ω(d(μ)) -> μ ∂Ω(d(μ))` and unit maps `g : ∂Ω(ε) -> ∂Ω(ε)`.
  - Each generator is a restriction of an element of `Γ`: the unit `g` at `ε` acts on `Y_ε = t_ε R_ε`
    as `t_ε g t_ε^(-1)`, and the one-step prefix `(ε', h)` at `ε` maps `Y_ε'` into `Y_ε` as `t_ε h`.
  - Conversely, let `γ ∈ Γ`, `y ∈ Y` with `γ y ∈ Y`, and let `x_i = μ_i^ v_0` be the vertices of the
    ray to `y`. For large `n`, `γ x_(n-1), γ x_n` are consecutive vertices `x'_(n+l-1), x'_(n+l)` on
    the ray to `γ y`. Then `u := (μ'_(n+l)^)^(-1) γ μ_n^` fixes `v_0` and the back edge `f_ε̄_n`, so
    it is a unit at the state `ε_n`, and near `y`, `γ = μ'_(n+l) ∘ u ∘ μ_n^(-1)`.
  - So `P` is the restriction to `Y` of the pseudogroup of `Γ ↷ ∂T`.
- **Effectiveness of both sides.** Under (TF), `Γ ⋉ ∂T` is effective, so it is the groupoid of germs
  of its pseudogroup.
  - For Li's groupoid, every arrow is `[c d^(-1), χ]` with `c = (μ', g_1)` and `d = (μ, g_2)`, acting
    by `μ ν ↦ μ' (g ν)` with `g = g_1 g_2^(-1)`.
  - Suppose it acts trivially near `χ`. If `|μ| ≠ |μ'|`, a cylinder of one length would equal a
    cylinder of a shorter length, but every state has at least two outgoing edges. So `μ = μ'`, and
    after refining along a prefix `κ`, `φ(g, κ)` acts trivially on `∂Ω(d(κ))` and `g·κ = κ`.
  - By Step 3 and (TF), `φ(g, κ) = 1`. By pseudo-freeness `g = 1`, so the arrow is a unit.
  - Hence both groupoids are the germ groupoid of `P`, and `(Γ ⋉ ∂T)|_Y ≅ (I_l(D) ⋉ ∂Ω_D)|_(⊔ ∂Ω(ε))`.

## Step 6. V times the coding, and Li's theorem (item 4)

- **The 2-graph.** `C_2` is the one-vertex graph with two loops. `C' = C_2 × C_(E_T)` is a finite
  2-graph. `𝔊` acts by `g·(w, μ) = (w, g·μ)` with `φ(g, (w, μ)) = φ(g, μ)`. This is self-similar,
  degree preserving and pseudo-free, so `D' = C' ⋈ 𝔊` is right cancellative (as in Step 4). The
  argument of Step 5, run on the second factor, identifies Li's groupoid of `D'` reduced to `C × Y`
  with `G_V × (Γ ⋉ ∂T)|_Y`.
- **Li, Example `ex:ZS` (II).** Hypotheses, each checked:
  - `C'` is a finite 2-graph, so `P = Z_(>=0)^2` (left reversible) and `C'` satisfy the assumptions of
    Theorem `thm:deg` exactly as Li checks them for `thm:k-graphs` (§`ss:k-graphs`). (F) holds for
    `C'` and for `D'`, which are right cancellative (l.1456). `d(g·a) = d(a)`.
  - For every state `ε` and `s ∈ S_P`, `# ε d^(-1)(s) ε >= 2`. Degree `(1,0)` gives 2 loops, degree
    `(0,1)` gives `[H : A_ε] >= 2`, and degree `(1,1)` gives their product.
  - `X = ∂Ω`, `Y_v = ∂Ω(v)` for all states `v`.
  - The units are `D'^*(ε, ε) = St(𝔊, ε) = A_ε̄` (`rem:ZS-Stab`, since `C'^* = C'^0`). These are of
    finite index in `H`, so of type `F_n` (resp. `F_∞`).
- So `F(G_V × (Γ ⋉ ∂T)|_Y)` is of type `F_n`.
- **Multiplicities.** For each `ε` choose a prefix code `{u_h : h ∈ T_ε}` of `C`. Then
  `B = ⋃_(ε, h) {(u_h w, h^(-1) y) <- (w, y) : y ∈ h Y_ε}` is a compact open bisection of
  `G_V × (Γ ⋉ ∂T)` with source `C × ∂T` and range `C × Y`. Conjugation by `B` gives
  `F(G_V × (Γ ⋉ ∂T)) ≅ F(G_V × (Γ ⋉ ∂T)|_Y)`, and Step 1 transports this to `X_T`.

## Step 7. Host and rigidity (item 5)

- `G_V × (Γ ⋉ X_T)` is minimal (Step 2), effective (Step 3) and ample. So `F = A` by
  `v-times-ample-full-groups-are-generated-by-transpositions`.
- `A` is simple by Nekrashevych's Theorem 4.1 (`nekrashevych-symmetric-and-alternating-full-groups`).
- Type (A) holds by `fp-v-times-minimal-action-full-groups-have-type-a-actions`.
- `γ ↦ id_C × γ` embeds `Γ`, by faithfulness.
- `X_T` is a topologically free subshift over the finitely generated group `Γ`, and its V-stabilized
  full group is finitely presented. So `topologically-free-subshift-full-groups-force-quantum-rigidity`
  makes it quantum rigid and of finite type.

## Step 8. Complexity (item 6)

- **Lower bound.** `H <= Γ <= F`, with fixed words for the generators.
- **Upper bound.** An element of `F` is a finite table of rows `(μ'_i, u_i, μ_i)`, where the `μ_i`
  and `μ'_i` are two partitions of `C × Y` into cylinders and `u_i` is a unit. It acts by
  `μ_i ν -> μ'_i (u_i·ν)`.
  - Composing two tables refines cylinders along prefixes `κ`. This replaces a label `u` by
    `φ(u, κ)`, of length at most `M^(|κ|) |u|`, where `M` bounds the lengths of `φ(s, e)` over
    generators `s` and edges `e`.
  - For a word of length `ℓ` in the generators of `F`, every refinement depth is `O(ℓ)`. So there
    are `2^(O(ℓ))` rows with labels of length `M^(O(ℓ))`.
  - Computing `u·κ` and `φ(u, κ)` needs only the finite permutation actions of the generators on
    each `H/A_ε'` and the Reidemeister–Schreier rewriting of `θ_ε'`. That is polynomial in the label
    length.
  - The product is trivial iff every row has `μ'_i = μ_i` and `u_i = 1`. Equal lengths are forced as
    in Step 5, and faithfulness of units is (TF). That is `2^(O(ℓ))` word problems in `H` of length
    `M^(O(ℓ))`.

## Step 9. Baumslag–Solitar calibration

- `H = Z = ⟨a⟩`, `A_e = mZ`, `A_ē = kZ`, `θ_e(mj) = kj`, `|m|, |k| >= 2`. So `Γ = ⟨a, t | t^(-1) a^m t =
  a^k⟩`.
- At each state an element `u` fixes every allowed edge iff `u ∈ mZ ∩ kZ`: both types occur, since
  there are at least `|m| - 1, |k| - 1 >= 1` of each. Its sections are `uk/m` (type `e`) and `um/k`
  (type `ē`).
- So `N_e = N_ē = N`, the largest subset of `lcm(m,k) Z` stable under `u ↦ uk/m` and `u ↦ um/k`.
- If `|m| ≠ |k|`, write `k/m = k'/m'` in lowest terms, with say `|k'| >= 2`. Then `u ∈ N` forces
  `(m'/k')^j u ∈ Z` for all `j`, so `u = 0`, and (TF) holds.
- If `|m| = |k|`, `N = lcm Z ≠ 0`.
- `H = Z` is `F_∞`, so Steps 6–7 give the calibration statement.

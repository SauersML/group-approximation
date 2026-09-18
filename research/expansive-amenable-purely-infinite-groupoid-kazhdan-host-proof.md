---
rg: 2
id: expansive-amenable-purely-infinite-groupoid-kazhdan-host-proof
kind: route
title: "Horofunction subshift of a hyperbolic Kazhdan group, made free and minimal, crossed with the full two-shift groupoid"
target: expansive-amenable-purely-infinite-groupoid-hosts-kazhdan
requires:
  - caprace-kassabov-hyperbolic-kazhdan-alternating-quotients
  - hyperbolic-cayley-graph-ozawa-boundary-facts
---

Throughout, `Γ` is an infinite hyperbolic group with property (T)
(`caprace-kassabov-hyperbolic-kazhdan-alternating-quotients`: the KMS groups "are infinite
hyperbolic as soon as p is an odd prime; they have property (T) if p ≥ 7").

- `S = S^{-1} ∌ e` is a finite generating set, and `K = Cay(Γ, S)` has edges `{g, gs}`.
- `d` is the word metric. Left multiplication is a graph automorphism, and `Γ` acts
  simply transitively on vertices.
- `C = {0,1}^N` and `G_2` are as in `amenable-purely-infinite-groupoid-kazhdan-host-proof`.

## Sources (verbatim, read from the arXiv source tex, 2026-09-17)

- **Ozawa**, arXiv:math/0501555.
  - Theorem, l.93–101: "Let $\G$ be a group acting on a countable fine hyperbolic graph
    $K$ with finite quotient. Let $Y$ be a compact space on which $\G$ acts. We assume
    that, for every vertex $x$ in $K$, the restricted action of the vertex stabilizer
    $\G^x$ on $Y$ is amenable. Then, the diagonal action of $\G$ on $\dk\times Y$ is
    amenable."
  - Definition, l.425–438: the action on compact `Ω` is amenable "if for every finite
    subset $E\subset\G$ and $\e>0$, there exists a continuous map
    $\mu\colon\Omega\ni\omega\mapsto\mu_\omega\in\prob(\G)$ such that
    $\max_{s\in E}\sup_{\omega\in\Omega}\|s\cdot\mu_\omega-\mu_{s\omega}\|\le\e$."
  - l.443–444: "A group $\G$ is amenable iff the trivial action on a singleton set is
    amenable."
  - Boundary and topology (l.203–225): quoted in
    `hyperbolic-cayley-graph-ozawa-boundary-facts`.
- **Gao–Jackson–Seward**, *Group colorings and Bernoulli subflows*, arXiv:1201.0513.
  - `chapter01.tex` l.78: "A subflow of $X$ is called \emph{free} if it consists entirely
    of aperiodic points".
  - l.173 (theorem): "If $G$ is a countably infinite group and $k > 1$ is an integer,
    then the collection of hyper aperiodic points in $k^G$ (equivalently the union of the
    free subflows of $k^G$) is dense in $k^G$."
- **Nekrashevych**, *Simple groups of dynamical origin*, arXiv:1511.08241 (`fullgr.tex`).
  - l.790–792: "A groupoid $\G$ is said to be \emph{compactly generated} if there exists a
    compact set $S\subset\G$ (called a \emph{generating set}) such that
    $\G=\bigcup_{n\ge 1}(S\cup S^{-1})^n$."
  - l.825–829: expansive cover, quoted in the target.
  - Proposition `pr:bebasis`, l.862–872: for "a finite cover by bisections of a compact
    generating set $S$", (1) "The cover $\mathcal{S}$ is expansive" is equivalent to (2)
    "The sets $\be(F)$ for $F\in\bigcup_{n\ge 1}(\mathcal{S}\cup\mathcal{S}^{-1})^n$ form a
    basis of topology on $\G^{(0)}$", where `\be` is the source map (l.12, l.178–179).

## Step 1. Amenability on the compactification

`K` is countable and locally finite. A circuit of length `≤ n` through an edge lies in a
ball of radius `n`, so `K` is fine. `Γ` acts with one vertex orbit and trivial vertex
stabilizers. `K` is hyperbolic in Ozawa's sense by item 1 of
`hyperbolic-cayley-graph-ozawa-boundary-facts`.

Apply Ozawa's Theorem with `Y` a point. The stabilizer action is that of the trivial group
on a point, which is amenable by l.443. So `Γ ↷ ΔK` is amenable. Any compact `Γ`-space `P`
with a continuous equivariant `p: P → ΔK` is amenable, with `μ ∘ p` as witness.

## Step 2. Topology of `ΔK` used

- **Vertices are open.** Let `A` be the set of neighbours of `x`. A geodesic from `x` to
  `z ≠ x` passes through a neighbour at time 1, so `M(x, A) = {x}`. Hence `V(K)` is open and
  `∂K = ΔK ∖ V(K)` is closed.
- **First countable.** Each point has the countable neighbourhood base `M(x, A)`, with `A`
  running over the finite subsets of `Γ` (Theorem bowditch).

## Step 3. The horofunction subshift `Z`

- **The space `H`.** Let `H = {h: Γ → Z : h(e) = 0, |h(g) − h(gs)| ≤ 1 for all g, s}` with
  the product topology. Since `|h(g)| ≤ |g|`, `H` is compact metrizable.
  - The action is `(γ·h)(g) = h(γ^{-1}g) − h(γ^{-1})`.
  - `Δ: H → A^Γ` with `A = {−1,0,1}^S` is given by `Δh(g)_s = h(gs) − h(g)`.
  - `Δ` is continuous and injective (`h(e) = 0` and the increments recover `h`), so it is a
    homeomorphism onto its closed image.
  - `Δ(γh)(g)_s = h(γ^{-1}gs) − h(γ^{-1}g) = Δh(γ^{-1}g)_s`, so `Δ` conjugates `Γ ↷ H` to
    a closed shift-invariant subset of `A^Γ` with the shift `(γ·u)(g) = u(γ^{-1}g)`.
- **Busemann functions.** For `x ∈ Γ` put `b_x(g) = d(x, g) − d(x, e) ∈ H`. Left invariance
  of `d` gives `γ·b_x = b_{γx}`.
- **The spaces `X` and `X∞`.** Let `X` be the closure of `{(b_x, x) : x ∈ Γ}` in
  `H × ΔK`, and put `X∞ = X ∩ (H × ∂K)`.
  - `X` is compact, first countable and invariant under the diagonal action (each `γ` acts
    by a homeomorphism, by Theorem bowditch). So `X∞` is compact and invariant.
  - By Step 2, a point `(h, x)` of `X` with `x ∈ V(K)` is the limit of a sequence that is
    eventually `(b_x, x)`. So `X = {(b_x, x)} ⊔ X∞`.
  - `X∞ ≠ ∅`. Take distinct `x_j` and a cluster point of `(b_{x_j}, x_j)`. It is not at a
    vertex, since vertices are open and the `x_j` are distinct.
- **The subshift.** Let `q: X∞ → H` be the projection and `Z = q(X∞)`, which is compact and
  invariant. `Δ(Z)` is a subshift.

## Step 4. `q` is injective, so `Γ ↷ Z` is amenable

Let `(h, ξ) ∈ X∞`, with `(b_{x_j}, x_j) → (h, ξ)`. The `x_j` leave every finite set: if not,
a subsequence is constant, equal to `x`, and then `ξ = x ∈ V(K)`.

- **An `h`-ray.** Let `g ∈ Γ`. Choose `j` with `b_{x_j} = h` on the ball `B(g, 1)` and
  `x_j ≠ g`. A geodesic from `g` to `x_j` starts at some `gs` with
  `d(x_j, gs) = d(x_j, g) − 1`, so `h(gs) = h(g) − 1`. Choose such an `s` by a fixed rule
  depending only on `h` (least in a fixed order of `S`), starting from `α(0) = e`. This
  gives a path `α` with `h(α(k)) = −k`. Since `h` is 1-Lipschitz, `d(e, α(k)) ≥ k`, so `α`
  is an infinite geodesic. It depends only on `h`.
- **The ray ends at `ξ`.** Fix `R`. For all large `j`, `b_{x_j} = h` on `B(e, R)`. Then
  `d(x_j, α(R)) = d(x_j, e) − R`, so `α[0, R]` followed by a geodesic from `α(R)` to `x_j` is
  a geodesic `α_j ∈ F(e, x_j)` extending `α[0, R]`. Choose `j_1 < j_2 < …` with `α_{j_n}`
  extending `α[0, n]`. Since `x_{j_n} → ξ`, item 2 of
  `hyperbolic-cayley-graph-ozawa-boundary-facts` gives `α ∈ F(e, ξ)`, that is, `α_+ = ξ`.
- **Conclusion.** `ξ = α_+` is determined by `h`, so `q` is injective. `q` is a continuous
  bijection from a compact space onto the Hausdorff space `Z`, hence an equivariant
  homeomorphism. The projection `X∞ → ∂K ⊆ ΔK` is continuous and equivariant, so by Step 1,
  `Γ ↷ X∞` is amenable. Hence `Γ ↷ Z` is amenable, with witness `μ ∘ p ∘ q^{-1}`.

## Step 5. A free minimal amenable Cantor subshift `M`

- **A free subflow.** By Gao–Jackson–Seward l.173 (with `k = 2`, `Γ` countably infinite),
  `2^Γ` contains a free subflow `F`. Their shift convention may be the right shift. The map
  `u ↦ u ∘ inv` conjugates the right shift `(γ·u)(g) = u(gγ)` to the left shift
  `u ↦ u(γ^{-1}·)`, so a free subflow exists for the convention of Step 3.
- **The product.** Let `W = Δ(Z) × F ⊆ (A × 2)^Γ`. `W` is a subshift. The diagonal action is
  free because it is free on `F`, and amenable by pullback along `W → Z` (Step 4).
- **Minimal subset.** By Zorn, `W` has a minimal nonempty closed invariant subset `M`. `M` is
  a free, minimal, amenable subshift over `A × 2`.
- **Cantor.** `M` has no isolated points. The set of isolated points is open and invariant,
  so by minimality it is empty or all of `M`. If it is all of `M`, then `M` is finite, and a
  point has finite-index stabilizer, which is nontrivial because `Γ` is infinite. That
  contradicts freeness. So `M` is a Cantor set.
- **The transformation groupoid.** Put `𝓗 = M ⋊ Γ`, with arrows `(γu, γ, u)`. It is amenable
  in sense (A) by Step 0 of `amenable-purely-infinite-groupoid-kazhdan-host-proof`, which
  converts continuous `μ_n: M → Prob(Γ)` with vanishing Ozawa defect into (A). A sequence
  of witnesses for `E_n ↑ Γ` and `ε_n ↓ 0` gives such `μ_n`.
- It is principal (free), minimal and ample.

## Step 6. Properties 2–6 for `𝒢 = 𝓗 × G_2`

This repeats Step 4 and Step 5, items 1–5, of
`amenable-purely-infinite-groupoid-kazhdan-host-proof`. That argument uses only that
`𝓗 = M ⋊ Γ` comes from a free, minimal, amenable action on a Cantor set, together with
Matui's quotes for `G_2`. Both referee lenses of that route passed these steps. For
completeness:

- Amenability is the product of the systems of Step 5 and `m_N^x = (1/N) Σ_{j<N} δ_{(x,j,σ^j x)}`.
- Minimality: orbits are `Γu × G_2(x)`.
- Essential principality: `int 𝒢' = int 𝓗' × int G_2' = M × C`.
- Pure infiniteness: rectangles `B_i × D_i` with the properly infinite pairs of `G_2`.
- `Γ ≤ [[𝒢]]` via `U_γ = (M × {γ}) × C`, injective since the action is free.

## Step 7. Property 1: `𝒢` is compactly generated and expansive

For a clopen `P ⊆ M` and `s ∈ Γ`, write `B(s, P) = {(su, s, u) : u ∈ P}`, a compact open
bisection of `𝓗`. Write `[a]_g = {u ∈ M : u(g) = a}` for `a ∈ A × 2`, and recall
`U_{μ,ν}` from Matui (l.1783–1789 as quoted in the host route), with
`s(U_{∅,w}) = C_w` and `U_{a,∅}U_{b,∅} = U_{ab,∅}`.

- **Generating set.** `𝒮 = {B(s, [a]_e) × C : s ∈ S ∪ {e}, a ∈ A×2} ∪ {M × U_{0,∅}, M × U_{1,∅}}`.
  - Every element is a compact open bisection, and their union `S_𝒢` is compact open.
  - **It generates.** `(h, g) = (h, r(g)) · (s(h), g)`.
    - `h = h_1⋯h_k` with each `h_i ∈ M × S`, so `(h, r(g)) = (h_1, r(g))⋯(h_k, r(g))`.
    - For `g = (x, k − l, y)` with `σ^k x = σ^l y`, `g = (x, k, σ^k x)(σ^l y, −l, y)`, a
      product of `k` arrows of `U_{0,∅} ∪ U_{1,∅}` and `l` inverses. Units come from
      `(x, 1, σx)(σx, −1, x)`.
    - So `𝒢 = ⋃_n (S_𝒢 ∪ S_𝒢^{-1})^n`, and `𝒢` is compactly generated (l.790–792).
- **Sources of products form a basis of `M × C`** (condition (2) of `pr:bebasis`).
  - Let `u ∈ M`, `x ∈ C`, `E ⊆ Γ` finite and `w` a prefix of `x`.
  - Choose `s_1, …, s_k ∈ S ∪ {e}` such that the elements `t_i^{-1}`, with
    `t_i = s_i ⋯ s_1` and `t_0 = e`, run through `E`. This is possible because
    `t_i^{-1} = t_{i−1}^{-1} s_i^{-1}` is a walk in `K`, which is connected.
  - Put `a_i = u(t_{i−1}^{-1})` and `P = B(e, [u(t_k^{-1})]_e) · B(s_k, [a_k]_e) ⋯ B(s_1, [a_1]_e)`.
    - `v ∈ s(P)` exactly when `(t_{i−1}v)(e) = a_i` for `i ≤ k` and `(t_k v)(e) = u(t_k^{-1})`.
    - `(t v)(e) = v(t^{-1})`, so `s(P) = {v : v(t_i^{-1}) = u(t_i^{-1}), 0 ≤ i ≤ k}`. This is a
      neighbourhood of `u` inside the cylinder `{v : v|_E = u|_E}`.
  - For `w = w_1 ⋯ w_m`, the product `(P × C) · (M × U_{∅,w_m}) ⋯ (M × U_{∅,w_1})` of
    factors from `𝒮 ∪ 𝒮^{-1}` equals `P × U_{∅,w}`, since
    `U_{∅,b}U_{∅,a} = (U_{a,∅}U_{b,∅})^{-1} = U_{∅,ab}`. Its source is `s(P) × C_w`.
  - These sets contain `(u, x)` and lie in any prescribed basic neighbourhood.
- By `pr:bebasis` (2) ⇒ (1), `𝒮` is expansive.

## Conclusion

`𝒢` has properties 1–6 of the target. The only inputs not quoted verbatim are items 1–2 of
`hyperbolic-cayley-graph-ozawa-boundary-facts`, used in Step 1 and Step 4. ∎

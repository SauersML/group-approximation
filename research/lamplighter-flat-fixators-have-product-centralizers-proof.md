---
rg: 2
id: lamplighter-flat-fixators-have-product-centralizers-proof
kind: route
title: "Proof: in a product of trees Min is the product of the factor Min-sets, the centralizer of an element acts cocompactly on its Min-set (Bridson–Haefliger II.6.10), integrality of translation lengths puts a coordinate-axis vector in the translation lattice of a regular element, discreteness gives finite conjugation orbits for an a-elliptic element, and the proper DL action of the lamps forces the hulls Y_b, Y_c to branch"
target: lamplighter-flat-fixators-have-product-centralizers
requires:
  - lamplighter-cut-outs-act-freely-on-the-third-tree
---

Verification tier: proposed-established.

Ingredients:
- Theorems B1, B2 of `tree-cut-outs-force-locally-finite-by-abelian-quotients`.
- Theorem E2 of `lamplighter-cut-outs-act-freely-on-the-third-tree`.
- Bridson–Haefliger II.6.8–II.6.10: Min-sets, products, and cocompactness of
  centralizers for proper cocompact actions.
- Sageev–Wise: the Tits alternative for proper actions on CAT(0) cube
  complexes.
- Serre: a free action on a tree means the group is free.

`X = T_a × T_b × T_c` is CAT(0). Since `Λ` is discrete, torsion-free and
cocompact, it acts **freely** (no element fixes a point: stabilizers are
finite, hence trivial), properly and cocompactly on `X`. For
`g = (g_a, g_b, g_c)` the displacement is `d_g(x)² = Σ_j d_{g_j}(x_j)²`, so
`Min(g) = Min(g_a) × Min(g_b) × Min(g_c)` (BH II.6.9). In a tree, `Min` of a
hyperbolic element is its axis, and `Min` of an elliptic one is its fixed
subtree. Passing to the barycentric subdivision removes inversions and
changes nothing below.

## Step 1: a cocompactness lemma

**Lemma 1.** Let `g ∈ Λ`, and let `C′ ≤ C_Λ(g)` be the subgroup of index at
most `2^3` that preserves the orientation of every axis factor of `Min(g)`.
Let `I ⊆ {a, b, c}` be the set of factors where `g` is hyperbolic, and let
`χ : C′ → Z^I` record the translation lengths along the axes `ℓ_j(g)`,
`j ∈ I`. Then:
1. `χ(C′)` has finite index in `Z^I`.
2. `ker χ` fixes `∏_{j∈I} ℓ_j(g)` pointwise, and acts freely and cocompactly
   on `∏_{j∉I} Fix_j(g)`.

*Proof.*
- **Setup.** `C_Λ(g)` acts cocompactly on `Min(g)` (BH II.6.10(2)), and so
  does its finite-index subgroup `C′`. Pick a compact `D ⊆ Min(g)` with
  `C′·D = Min(g)`. An element of `C′` preserves each factor and commutes with
  `g`, so it acts on each axis `ℓ_j(g)` as an orientation-preserving
  isometry, that is, a translation. Translation lengths in a tree are
  integers (vertices go to vertices), so `χ` takes values in `Z^I`.
- **Part 1.** `χ(C′)` acts cocompactly on `∏_{j∈I} ℓ_j ≅ R^I`, because
  `Min(g)/C′` surjects onto `R^I/χ(C′)`. A subgroup of `Z^I` acting
  cocompactly on `R^I` has full rank, hence finite index.
- **Part 2, fixing the axes.** Elements of `ker χ` translate each `ℓ_j` by
  0, so they fix it pointwise.
- **Part 2, cocompactness.** Fix `p ∈ ∏_I ℓ_j`. For
  `y ∈ Y := ∏_{j∉I} Fix_j(g)`, choose `h ∈ C′` with `h(p, y) ∈ D`. Then
  `p + χ(h)` lies in the bounded projection of `D`, so `χ(h)` lies in a
  finite set `E`. Choose `h_e ∈ C′` with `χ(h_e) = e` for each `e ∈ E`.
  Then `h_e^{-1}h ∈ ker χ`, and `(p, y) ∈ ker χ · ⋃_e h_e^{-1}D`. So
  `ker χ` acts cocompactly on `{p} × Y ≅ Y`. It acts freely because `Λ`
  does. ∎

## Step 2: Theorem F

**Part 1.** `τ` is hyperbolic in all three trees, so `I = {a, b, c}`.
- By Lemma 1, `χ(C′)` has finite index in `Z^3`, so it contains `(m, 0, 0)`
  for some `m ≥ 1`. Pick `λ₀ ∈ C′` with `χ(λ₀) = (m, 0, 0)`.
- `λ₀` translates `ℓ_b(τ)` and `ℓ_c(τ)` by 0, so it fixes them pointwise.
  Hence `λ₀ ∈ Λ_F(τ)`.
- `λ₀` translates `ℓ_a(τ)` by `m`, so `λ₀ ≠ 1`, and `λ₀` commutes with `τ`.
- In fact `C′ ∩ Λ_F(τ) = χ^{-1}(Z × 0 × 0)` is infinite cyclic up to finite
  index. It is the kernel of the `(b,c)`-part of `χ` and acts freely and
  cocompactly on `ℓ_a(τ)`.

**Part 2.** `τ` is elliptic in `a`, so `I = {b, c}`. Let `λ ∈ Λ_F(τ)`.
- **Conjugates stay in a compact set.** `τ` preserves `ℓ_b × ℓ_c`, so each
  conjugate `τ^k λ τ^{-k}` again fixes `ℓ_b × ℓ_c` pointwise. Their
  `(b,c)`-parts therefore lie in the compact group `Fix(ℓ_b) × Fix(ℓ_c)`.
  If `τ` fixes the vertex `x ∈ T_a`, then
  `d(x, τ^kλτ^{-k}x) = d(x, λx)`, so their `a`-parts lie in a compact
  subset of `G_a`.
- **Finite orbit.** `Λ` is discrete, so the orbit of `λ` under conjugation
  by `τ` is finite. Some `τ^D`, and hence `τ^{D!}`, centralizes `λ`.
- **Increasing union.** It follows that `Λ_F(τ) = ⋃_D C_{Λ_F}(τ^{D!})`, and
  the union is increasing.
- **Each term acts cocompactly.** Apply Lemma 1 to `g = τ^{D!}`, which has
  `I = {b, c}`. Then `ker χ ⊆ C_{Λ_F}(τ^{D!})`, and `ker χ` acts freely and
  cocompactly on `Fix_a(τ^{D!})`. Also `C_{Λ_F}(τ^{D!})` preserves
  `Fix_a(τ^{D!})`, acts freely, and contains `ker χ`. So it acts freely and
  cocompactly too.
- **The triviality criterion.** If every `Fix_a(τ^D)` is bounded, each term
  is a finite torsion-free group, hence trivial, so `Λ_F(τ) = 1`. If one of
  them is unbounded, the corresponding term is infinite.
- **The abelian criterion.** Each term is free (Serre). A free cocompact
  action on a tree with at least three ends has a non-cyclic free group.
  Conversely, if every `Fix_a(τ^{D!})` has at most two ends, every term is
  trivial or `Z`. An increasing union of cyclic groups is abelian.

**Part 3.** An element `τ₀ ∈ H` lifting `t^m` is nontrivial, so it is
hyperbolic in `a` by E2, and it is hyperbolic in `b` and `c` by B1.
- Part 1 gives `Λ_F(τ₀) ≠ 1`.
- Corollary B′ needs `Λ_F = 1` for every element hyperbolic in at least two
  tree factors. It therefore fails for any `Λ` containing an element
  hyperbolic in all three trees, and every putative witness `H` supplies
  one.
- So the Λ_F = 1 kill can never be certified for a cocompact host. Any kill
  must use finer information about `N ⊆ Λ_F(τ₀)`, as Theorem W does.

## Step 3: Theorem W

Let `n ∈ N∖1`. By E2, `n` is hyperbolic in `a`. Since `N ⊆ Σ`, `n` is
elliptic in `b` and `c`, and by B2(3), `ρ(n)` fixes `Y_b × Y_c` pointwise.

**Part 1: `Y_j` has infinitely many ends (`j = b, c`).**
- `Y_j` is the convex hull of the lines `Ĥ·ℓ_j`, so it is leafless.
- **Suppose `Y_b` is a line.** Then `Y_b = ℓ_b` is `Ĥ`-invariant, so
  each lamp acts on it as an isometry of finite order that fixes the end
  `ξ_b`, which is trivial. So `L` acts trivially on `Y_b`. B2 says `P`
  acts properly on `Y_b × Y_c`, so `L` acts properly on `Y_c`.
- **Finite lamp groups fix vertices of `ℓ_c`.** Let `F ≤ L` be a nontrivial
  finite subgroup, for example the lamps at positions in `[-r, r]`. `F`
  fixes a vertex, and hence the ray from that vertex to `ξ_c`. This ray
  meets `ℓ_c`, because `ξ_c` is an end of `ℓ_c` (`τ` fixes `ξ_c` and is
  hyperbolic). So `F` fixes a vertex `x ∈ ℓ_c`, and therefore fixes the
  ray `[x, ξ_c)`.
- **Suppose `τ` translates towards `ξ_c`.** Then `τ^{-k}x` lies on
  `ℓ_c` further from `ξ_c`, and `τ^{-k}Fτ^k` fixes `[τ^{-k}x, ξ_c) ∋ x`.
  So the stabilizer `L_x` contains `⋃_{k ≥ 0} τ^{-k}Fτ^k`. This is
  infinite, since conjugating by `t` shifts lamp positions and `F ≠ 1`.
  That contradicts properness.
- **Suppose `τ` translates away from `ξ_c`.** Use `k ≤ 0` and get the same
  contradiction.
- **The end count.** So `Y_b` is a leafless tree that is not a line, and
  therefore has at least three ends. Its end set is closed and
  `Ĥ`-invariant. If it were finite, a finite-index subgroup of `Ĥ` would
  fix every end, including a power of the hyperbolic `τ`. But a hyperbolic
  automorphism fixes exactly two ends, a contradiction. The case `Y_c` is
  symmetric.
- Hence `Fix_j(n) ⊇ Y_j` has infinitely many ends.

**Part 2.** Apply Lemma 1 to `g = n`, which has `I = {a}`.
- `C_0 := ker χ` fixes `ℓ_a(n)` pointwise and acts freely and cocompactly
  on `Fix_b(n) × Fix_c(n)`.
- `n` is central in `C_Λ(n)` and `χ(n) ≠ 0`. So `⟨n⟩ ∩ C_0 = 1`, and
  `C_0 × ⟨n⟩ = χ^{-1}(χ(n)Z)` has finite index in `C′`, and hence in
  `C_Λ(n)`.

**Part 3.**
- `C_0` acts freely and cocompactly on the CAT(0) square complex
  `Fix_b(n) × Fix_c(n)`, so it is quasi-isometric to it.
- `Fix_b(n)` has infinitely many ends and a cocompact action (the
  projection of `C_0`). Its leafless core therefore has branch vertices
  within bounded distance of every vertex, so it has exponential growth, and
  so does `C_0`. In particular `C_0` is not virtually abelian.
- By the Tits alternative for groups acting properly on finite-dimensional
  CAT(0) cube complexes with bounded torsion (Sageev–Wise 2005),
  `F_2 ≤ C_0`.
- So `C_0` is non-amenable, and `F_2 × ⟨n⟩ ≤ Λ`.
- Caution: the image of `C_0` in `Aut(Fix_b(n))` may fix an end, as in the
  Bass–Serre tree of `BS(1,2)`. So ping-pong in a single factor is not used.

## Step 4: Corollaries W1, W2

**W1.**
- Suppose a cut-out exists. By B2(3), `N ≠ 1`. Any `n ∈ N∖1` is
  hyperbolic in exactly one tree (Part 1) and has a non-amenable
  centralizer (Part 3). This contradicts the first hypothesis.
- `n` is elliptic in `b`, and `Fix_b(n)` has infinitely many ends. This
  contradicts the second hypothesis. If `pr_b(λ) = 1` for some `λ ≠ 1`,
  then `Fix_b(λ) = T_b`, which is why the second hypothesis includes
  injectivity.
- **Arithmetic case.** `Λ ≤ D^×/F^×` for a quaternion division algebra `D`.
  The centralizer of `n ≠ 1` lies in the `F`-points of a maximal torus, so
  it is abelian.
- **Fixed-set description (not needed above).** Equivalently, in
  `PGL_2(F_v)` a nontrivial semisimple elliptic element fixes a bounded set
  (anisotropic torus) or a bounded neighbourhood of one apartment (split
  torus). That set has at most two ends.

**W2.**
- **Stabilizers in the one-vertex complex.** Let `v₀ = (r_a, r_b, r_c)` be
  the base vertex. Each letter maps `v₀` to a neighbour in its own factor
  and fixes the other two coordinates. So `⟨A⟩` acts simply transitively
  on `T_a × {(r_b, r_c)}`. By simple transitivity of `Λ`,
  `Stab_Λ(r_b, r_c) = ⟨A⟩` and `Stab_Λ(r_a) = ⟨B ∪ C⟩`.
- **Reduction to a cyclically reduced `a`-word.** Take `n ∈ N∖1` and a
  vertex `v ∈ ℓ_a(n) × Fix_b(n) × Fix_c(n)`, and let `g ∈ Λ` satisfy
  `g v₀ = v`. Then `w = g^{-1} n g` fixes `(r_b, r_c)`, so it is an
  `a`-word. Its axis in the Cayley tree `T_a` passes through `r_a`, so it
  is cyclically reduced. It has the same fixed-set shapes as `n`, so it is
  doubly branching by Part 1.
- **The commuting subgroup.** `g^{-1}C_0 g` fixes `ℓ_a(w) ∋ r_a`, so it
  lies in `⟨B ∪ C⟩`. It is non-amenable and commutes with `w`.
- **The automaton.** A vertex of `T_b` is `β r_b` for a unique reduced
  `B`-word `β`. Pushing `w` through `β` letter by letter gives
  `wβ = β′w′` with `|w′| = |w|`, and `w′` fixes `r_b`. So `w` fixes `β r_b`
  iff `β′ = β`. The fixed vertices are the paths from `w` in the automaton
  with states `a`-words of length `|w|` and edges `s --y--> s′` whenever
  `s y = y s′`, reduced by forbidding `y` followed by `y^{-1}`.
- **The exact end test.** After pruning nodes with no infinite
  continuation, the sphere sizes of `Fix_b(w)` are the path counts from the
  start node. They are unbounded iff some reachable node on a cycle has
  out-degree at least 2 among alive nodes:
  - A node on a cycle with a second alive out-edge gives two
    distinguishable continuations that recur along the cycle, so the path
    counts grow without bound.
  - If every cyclic node has out-degree 1, each path eventually enters a
    simple cycle with no exits, so the counts are eventually constant.
  - A leafless tree has finitely many ends iff its sphere sizes are
    bounded.
- This is `ends_infinite` in `branching.py`. The heuristic sphere-count
  classifier agrees with it on all words tested.

## Scope and what is not claimed

- Theorem F needs cocompactness through BH II.6.10. For non-uniform tree
  lattices, Corollary B′ may still apply.
- W1 is a sufficient condition. It is not known whether irreducible
  non-arithmetic three-tree lattices have amenable centralizers.
- No irreducible one-vertex cube complex was produced. The SAT searches
  are recorded in the experiments directory as negative calibration only.

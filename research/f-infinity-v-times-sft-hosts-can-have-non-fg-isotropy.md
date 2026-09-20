---
rg: 2
id: f-infinity-v-times-sft-hosts-can-have-non-fg-isotropy
kind: claim
title: "An F_infinity simple V-times-SFT host over a finitely presented group can have a point whose isotropy germ group is Z[1/2]; so finite presentation of these hosts forces no finiteness of germs or point stabilizers"
distinct_from:
  v-times-rigid-topologically-free-sft-full-groups-are-fp: that is gate E3′, finite presentation of every rigid minimal topologically free V-times-SFT host; this settles its recorded isotropy worry, showing that infinitely generated point stabilizers occur in F_infinity hosts, so they cannot be what blocks E3′.
  cocompact-tree-end-shift-hosts-are-f-infinity: that proves F_infinity of tree end-shift hosts; this applies it to one explicit Z^2 HNN extension and computes an end stabilizer and a germ group, which that node does not do.
  shell-envelope-fp-forces-fp-germ-group: that proves finite presentation forces a finitely presented germ group for shell envelopes; this shows that the implication fails for V-times-SFT hosts, where even finite generation of germ groups is not forced.
  fp-almost-v-groups-have-fp-germ-groups: that proves germ finiteness is necessary between V and the almost-V group; this shows no such necessity for the product groupoid G_V x (Lambda ⋉ X).
  rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer: that gives a finitely generated non-amenable point stabilizer, and does not decide finite presentation of the host; this gives a point stabilizer that is not finitely generated, inside a host proved F_infinity.
  end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups: that constrains vertex stabilizers when the acting group contains (Q,+); here the vertex group is Z^2, and the non-finitely-generated group Z[1/2] appears only as an end stabilizer.
---

**ESTABLISHED** (lane bh-last-mile, swarm-0917-w19, 2026-09-19; elementary, not reviewed; no
priority claimed). The route is `non-fg-isotropy-f-infinity-hosts-via-tree-ends`. It uses two
ESTABLISHED nodes, `cocompact-tree-end-shift-hosts-are-f-infinity` and
`locally-finite-tree-end-shifts-are-quantum-rigid-sfts`, and an explicit computation.

## Statement

Let

    Λ = ⟨ x, y, t | [x,y] = 1,  t⁻¹ x t = x²,  t⁻¹ y² t = y ⟩.

This is the HNN extension of `A = Z² = ⟨x,y⟩` along `φ : M → N`, where `M = ⟨x, y²⟩`,
`N = ⟨x², y⟩` and `φ(a,b) = (2a, b/2)`. Let `T` be its Bass–Serre tree, `X_T ≅ ∂T` the end shift
of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`, and
`F = F(G_V × (Λ ⋉ X_T))`.

1. `Λ` is finitely presented and torsion-free. `T` is 4-regular, and `Λ` acts on it minimally,
   cocompactly, strongly faithfully and with no fixed end.
2. `X_T` is a D-quantum-rigid, minimal, topologically free SFT over `Λ` with torsion-free
   isotropy, and `F` is simple and of type `F_∞`.
3. There are uncountably many ends `ω` with `Stab_Λ(ω) ≅ Z[1/2]`.
4. For any such `ω` and any `ξ ∈ C` that is not eventually periodic, the germ group of `F` at
   `p = (ξ, ω)` is `Z[1/2]`. So `Stab_F(p)` surjects onto `Z[1/2]` and is not finitely generated.

## Proof

**Step 1: the tree and transport.** Vertices of `T` are the cosets `gA`, and edges are the cosets
`gM`, joining `gA` to `gtA`. Since `t⁻¹Mt = N`, the edge from `A` to `tA` has stabilizer
`A ∩ tAt⁻¹ = M`, and the edge from `A` to `t⁻¹A` has stabilizer `N`. Call these edges *forward*
and *backward* at `A`. `Λ` preserves the type, so it acts without inversions and preserves the
orientation of edges.

- There are `[A:M] = 2` forward edges and `[A:N] = 2` backward edges at each vertex, so `T` is
  4-regular, with one vertex orbit and one edge orbit.
- `A` is abelian, so both forward edges at `A` have stabilizer `aMa⁻¹ = M`, and both backward
  edges have stabilizer `N`.
- **Coordinates.** Identify each vertex group `gAg⁻¹` with `Z²` via `g`. If `m ∈ M` fixes a
  forward edge `a·(A, tA)`, then `m = a t φ(m) t⁻¹ a⁻¹`, so its coordinate at the far end is
  `φ(m)`. Backward steps apply `φ⁻¹`. This does not depend on the coset representative, again
  because `A` is abelian.

**Step 2: path stabilizers.** Take a path from a vertex `v_0` with steps `ε_j = ±1` (forward or
backward) and prefix sums `s_0 = 0`, `s_j = ε_1 + … + ε_j`. Write `φ^s(a,b) = (2^s a, 2^(-s) b)`.
An element of `Stab(v_0)` with coordinate `g` fixes the first `j` edges iff each `φ^(s_i)(g)`,
`i < j`, lies in `M` (for a forward step) or `N` (for a backward step). That holds iff
`φ^(s_i ± 1)(g) ∈ Z²` for each step. The prefix sums fill the integer interval
`[min s, max s]`, which contains 0. So the pointwise stabilizer of the path is

    { (a,b) ∈ Z² : 2^(−min_j s_j) | a  and  2^(max_j s_j) | b },

where `2^∞ | b` means `b = 0`.

**Step 3: every step sequence is a geodesic.** Arriving at a vertex along a forward edge uses one
of its backward edges. The next step still has two forward edges and one unused backward edge
available, and symmetrically after a backward step. So every `ε ∈ {±1}^N` is realised by a
non-backtracking path, which in a tree is a geodesic ray. Whenever `ε_{j+1} = ε_j` there are two
choices of edge, so each `ε` with infinitely many repeated steps is realised by uncountably many
rays from `v_0`, with pairwise distinct ends.

**Step 4: an end with stabilizer Z[1/2].** Put `ε_j = −1` for `j = k²` (`k ≥ 2`) and `ε_j = +1`
otherwise. Then `s_j ≥ j − 2√j → +∞`, and `ε` is not eventually periodic, because the gaps
between its `−1`s grow. Let `ω` be the end of a ray `(v_0, v_1, …)` realising `ε`, and let `C_n` be
the pointwise stabilizer of the subray from `v_n`.

- Every automorphism of a locally finite tree without inversions is elliptic or hyperbolic. An
  elliptic `g` fixing `ω` fixes some vertex `w`, hence the ray `[w, ω)`, hence a subray
  `[v_n, ω)`. So the elliptic part of `Stab_Λ(ω)` is `⋃_n C_n`, an increasing union.
- **No hyperbolic element fixes `ω`.** Such an `h` has an axis with end `ω` and translates along
  it by some `ℓ ≥ 1`. It preserves edge orientations, so the step sequence along the axis is
  `ℓ`-periodic. The ray to `ω` eventually runs along the axis, so `ε` would be eventually
  periodic.
- **Each `C_n` is infinite cyclic.** By Step 2 applied at `v_n`, the subray has
  `max = +∞` and `min = m_n − s_n`, where `m_n = min_{j ≥ n} s_j`. So in coordinates at `v_n`,
  `C_n = { (a, 0) : 2^(s_n − m_n) | a }`.
- **The indices.** Transport to `v_{n+1}` multiplies the coordinate `a` by `2^(ε_{n+1})`. So the
  image of `C_n` is `2^(s_{n+1} − m_n) Z × 0`, inside `C_{n+1} = 2^(s_{n+1} − m_{n+1}) Z × 0`,
  with index `2^(m_{n+1} − m_n)`.
- Since `s_j → ∞`, `m_n → ∞`. An increasing union of infinite cyclic groups whose indices are
  powers of 2 with unbounded product is `Z[1/2]`.

So `Stab_Λ(ω) = ⋃ C_n ≅ Z[1/2]`, which is not finitely generated. Step 3 gives uncountably many
such `ω`. This proves item 3.

**Step 5: strong faithfulness.** Let `g` fix a half-tree `H` pointwise, and pick a vertex
`w ∈ H`. Three of the four edges at `w` lie in `H`, so `H` contains one forward and one backward
edge at `w`. By Step 3 the all-forward and all-backward rays from `w` can be started along these
edges, and they stay in `H`. By Step 2 the coordinate `(a,b)` of `g` at `w` satisfies `2^n | b` and
`2^n | a` for all `n`. So `g = 1`.

**Step 6: the other hypotheses of item 1.**
- `Λ` is finitely presented, as displayed, and torsion-free, as an HNN extension of `Z²`.
- There is one vertex orbit and one edge orbit, so the action is cocompact. It is minimal,
  because an invariant subtree contains a vertex and hence all of them.
- The tree is 4-regular, so it has no leaves and more than two ends.
- **No fixed end.** A fixed end is fixed by `A = Stab(v_0)`, so `A` fixes the ray from `v_0` to
  it, hence its first edge. That puts `A` inside `M` or `N`, which is false.
- Edge stabilizers are conjugates of `Z²`, which is `F_∞^+`.

Item 1 is proved. Item 2 follows. By `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`
(items 1–3), `X_T` is a D-quantum-rigid SFT conjugate to `∂T`, minimal, topologically free
(Step 5), and has torsion-free isotropy (`Λ` is torsion-free). The Setting of
`cocompact-tree-end-shift-hosts-are-f-infinity` is exactly item 1 plus `F_∞^+` edge groups, so its
item 1 gives that `F` is simple and `F_∞`.

**Step 7: the germ group (item 4).** The groupoid `𝒢 = G_V × (Λ ⋉ X_T)` is effective: both factors are
topologically principal (the product of their dense sets of points with trivial isotropy is
dense), so the germ group `Germ_F(p)` of `F` at `p = (ξ, ω)` embeds in the isotropy group
`𝒢_p^p = (G_V)_ξ^ξ × Stab_Λ(ω)`.

- **Upper bound.** For `ξ ∈ C = {0,1}^N` not eventually periodic, `(G_V)_ξ^ξ = 1`. A germ of V at
  `ξ` that fixes `ξ` is a prefix replacement `uη ↦ u'η` with `ξ = uη = u'η`. If `u ≠ u'`, say
  `|u'| = |u| + k` with `k > 0` (equal lengths force `u = u'`), then
  `σ^|u| ξ = η = σ^(|u|+k) ξ` for the shift `σ`, so `ξ` is eventually periodic. So
  `Germ_F(p) ≤ Stab_Λ(ω)`.
- **Lower bound.** For `λ ∈ Λ`, the map `id_C × λ` is the global bisection `{(1_C, (λ, x))}` of
  `𝒢`, so it lies in `F`. When `λ ∈ Stab_Λ(ω)` it fixes `p`, and its germ there is
  `(1, (λ, ω))`.

So `Germ_F(p) = Stab_Λ(ω) ≅ Z[1/2]`. The germ map `Stab_F(p) → Germ_F(p)` is onto by definition,
and `Z[1/2]` is not finitely generated, so neither is `Stab_F(p)`. `∎`

## What this kills

**The obstruction class.** Call a refutation strategy for E3′ *germ-necessity* if it runs:
(i) finite presentation of `F(G_V × (Λ ⋉ X))` forces the germ groups at some class of points to be
finitely generated, or finitely presented, or to pass an HNN or window gate; (ii) exhibit a rigid,
minimal, topologically free SFT violating this at one point. This is the pattern of
`shell-envelope-fp-forces-fp-germ-group` and `fp-almost-v-groups-have-fp-germ-groups`, where it
works.

- **Invariant:** the isotropy germ group at points `(ξ, ω)` with `ξ` not eventually periodic,
  which equals `Stab_Λ(ω)`.
- **Where every member dies:** at step (i). The host above is `F_∞`, yet its germ group
  `Z[1/2]` is not even finitely generated. So no finiteness property of germ groups or point
  stabilizers that `Z[1/2]` fails can be necessary for finite presentation (or `F_∞`) of
  V-times-SFT hosts. That covers finite generation, finite presentation, type `F_n`, and any
  gate implying these.
- The necessity arguments in the shell and almost-V settings rely on the germs being carried by
  a single V-like coordinate. In the product groupoid the V factor has trivial germs at such
  points, and the `Λ`-germs are absorbed by the transformations `Λ_e` of the Thumann operad.

**What it does not kill.** It says nothing about germ groups at points where `ξ` is eventually
periodic, which mix `Z` with `Stab_Λ(ω)`. It does not constrain refutations through
non-residually-finite point stabilizers, or through failure of the nonlinear one-scale filling
(`one-scale-filling-decides-fp-of-v-times-subshift-hosts`, Part 5). The host here is
non-amenable, so the Z²-type amenable frontier of E3′ is untouched.

## Lesson for general BH

The worry recorded in E3′, that infinitely generated point stabilizers might block finite
presentation, is unfounded. They already occur in `F_∞` simple hosts over a finitely presented
torsion-free group. So E3′ should be attacked or refuted on the filling side, the nonlinear
upgrade of quantum rigidity, and not on the isotropy side. This also bears on the shell
programme. Its germ gates come from the shell's V-coordinate carrying the germs. They are not a
general feature of finitely presented type (A) hosts, so a type (A) route through V-times-SFT
hosts need not pass them.

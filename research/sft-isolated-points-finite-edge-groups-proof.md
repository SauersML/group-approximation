---
rg: 2
id: sft-isolated-points-finite-edge-groups-proof
kind: route
title: Recode to nearest-neighbour constraints, cut the Cayley graph at the finite interface of each Bass–Serre edge, and use branch independence plus isolation to make every piece beyond the core the unique extension of its entry pattern
target: sft-isolated-points-are-finite-state-across-finite-edge-groups
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
---

Lane proof (bh-g3-topfree, 2026-09-18). Elementary; not reviewed. Notation is that of the target. The
finite tables below depend on `Y` and `y_*`; they are not claimed to be computable from them.

## §0. Nearest-neighbour form

Fix a finite symmetric generating set `S` of `A` as follows:
- **amalgam:** `S = S_1 ∪ S_2`, with `S_i` generating `B_i` and containing `K`;
- **HNN:** `S = S_B ∪ {t^(±1)}`, with `S_B` generating `B` and containing `K ∪ φ(K)`.

Let `r` bound the diameters of the forbidden patterns of `Y`. The higher-block map `y ↦ y^[r]`, with
`y^[r](g) = (y(gb))_(b ∈ B_r)`, is an `A`-equivariant homeomorphism onto an SFT cut out by single-site
constraints and constraints along the edges `{g, gs}` (`s ∈ S`) of `Cay(A, S)`. Overlap consistency along
edges is global consistency because balls are connected.
- Isolated points and stabilizers correspond under this map.
- `y_*(g)` is a coordinate of `y_*^[r](g)`.

So assume from now on that `Y` is **nearest-neighbour**. Let `W ∋ 1` be a finite window with
`{y ∈ Y : y|_W = y_*|_W} = {y_*}`.

## §1. Pieces and finite cuts

**Amalgam `A = B_1 *_K B_2`.**
- The *pieces* are the left cosets `gB_1` and `gB_2`.
- Each element lies in exactly two pieces, `gB_1` and `gB_2`, and they meet in `gK`.
- Every `S`-edge lies inside one piece.
- The Bass–Serre tree `T` has the pieces as vertices and the cosets `gK` as edges.
- For the edge `f = gK` put `I(f) = gK`.

**HNN `A = B *_K`, with `t^(-1) k t = φ(k)`.**
- The pieces are the cosets `gB`; they partition `A`.
- `S_B`-edges lie in pieces. A `t`-edge `h — ht` joins `hB` to `htB`.
- The `t`-edges realizing the tree edge `f = {gB, gtB}` are exactly `gk — gkt` for `k ∈ K`. Indeed
  `gbt ∈ gtB` iff `t^(-1) b t ∈ B`, which holds iff `b ∈ K` by Britton's lemma.
- Put `I(f) = gK ∪ gKt`, and note `gKt = gt·φ(K)`.

**Cut property.** Orient `f`. Let `A_f^+` be the union of the pieces in the half-tree `T_f^+`, and
`F^+(f) = A_f^+ ∖ I(f)`. Then every `S`-edge with an endpoint in `F^+(f)` has its other endpoint in
`F^+(f) ∪ I(f)`.
- *Amalgam.* Let `h ∈ F^+(f)`. Both pieces of `h` are adjacent in `T` along `hK ≠ f`, so both lie in
  `T_f^+`. An `S`-edge at `h` lies in one of them, so its other endpoint lies in `A_f^+`.
- *HNN.* `S_B`-edges stay in their piece. A `t`-edge between pieces on opposite sides realizes `f`, so
  both of its endpoints lie in `I(f)`.

Translation acts compatibly: `I(γf) = γI(f)` and `F^+(γf) = γF^+(f)`. There are two orbits of oriented
edges.

## §2. Branch independence and unique extension

- **(BI)** Let `y ∈ Y`, and let `y'` agree with `y` off `F^+(f)`. Then `y' ∈ Y` iff `y'` satisfies the
  constraints at the sites of `F^+(f)` and along the edges inside `F^+(f) ∪ I(f)`. By the cut property,
  no other constraint involves `F^+(f)`. So the admissible fillings of the far side depend only on the
  labels on `I(f)`.
- **(UE)** Suppose `W ∩ A_f^+ = ∅`. Then `y_*|_(A_f^+)` is the only configuration on `A_f^+` that
  satisfies the constraints at the sites of `A_f^+` and along the edges meeting `A_f^+`, where sites
  outside `A_f^+` carry the labels of `y_*`. For an HNN extension the outside neighbours lie in
  `I(f) ∖ A_f^+`; for an amalgam they lie in the parent piece (referee note).
  - *Proof.* Put any such configuration on `A_f^+` and keep `y_*` elsewhere. Every constraint of `Y` then
    holds, so the result lies in `Y`. It agrees with `y_*` on `W`, so it is `y_*`.

## §3. Every piece is an isolated point over its vertex group

**Coordinates.** A piece `P = gB_v` is read as `z_P(b) = y_*(gb)`. Its interfaces, in coordinates, are:
- **amalgam:** `bK`, for `b ∈ B_v`;
- **HNN:** `bK`, leading to `gbtB` (type `+`), and `bφ(K)`, leading to `gbt^(-1)B` (type `−`).

Write `J_τ` for `K`, respectively `φ(K)`.

**The piece SFTs.** Let `L_τ` be the set of patterns on `J_τ` that admit an extension across an
interface of type `τ`: labels on the rest of `I(f)` and a configuration on `F^+(f)` satisfying all
constraints inside `F^+(f) ∪ I(f)`. This depends only on `τ`, by translation. Define
`Y_v^L ⊆ Σ^(B_v)` by:
- the single-site and `S_v`-edge constraints of `Y`;
- `z|_(bJ_τ) ∈ L_τ` for every `b ∈ B_v` and every interface type `τ`.

This is an SFT over `B_v` with windows `J_τ`. Every `z_P` lies in it, because every far side of `P` is
filled by `y_*`.

**The core.** `T_W` is the convex hull in `T` of the finitely many pieces that meet `W`. It is finite.

**(P1) Pieces outside the core.** Let `P ∉ T_W`, and let `f` be the edge from `P` toward `T_W`, oriented
toward `P`. Let `P_-` be the parent piece, the other end of `f`. The *entry data* is
`p = y_*|_(I(f) ∩ P_-)`. For an amalgam `I(f) ∩ P_- = I(f) ⊆ P`. For an HNN extension it is the
parent's half of `I(f)`, and `P`'s half sits at the fixed position `J = φ(K)` (entry along `t`) or `J = K`
(entry along `t^(-1)`) in `P`'s coordinates. Then:
- `z_P` is the unique point `z ∈ Y_v^L` compatible with `p`. For an amalgam this means `z|_K = p`. For
  an HNN extension it means that `p` and `z|_J` satisfy the constraints along the `|K|` edges of `f`.
- *Proof.* Let `z` be compatible. Fill each other interface of `P` by an extension (it exists, since
  `z ∈ Y_v^L`); their far sides are pairwise disjoint and meet `P` only at those interfaces. This gives
  a configuration on `A_f^+` of the kind in (UE), and `W ∩ A_f^+ = ∅` because no piece beyond `f` lies
  in `T_W`. So `z = z_P`.
- The compatible set is a finite union of cylinders on `J`, and it is a single point. So `z_P` is
  isolated in `Y_v^L`.
- `z_P = z_(v, τ, p)` depends only on the vertex type, the entry type and the entry pattern. These
  range over a finite set.

**(P2) Core pieces.** For `P ∈ T_W`, let `E_P` be `(W ∩ P)` together with the parts in `P` of the
interfaces toward other core pieces. Any `z ∈ Y_v^L` agreeing with `z_P` on `E_P` can be completed:
- fill the other interfaces of `P` by extensions;
- keep `y_*` everywhere else.

The result lies in `Y` by (BI) and agrees with `y_*` on `W`, so `z = z_P`. So `z_P` is isolated in
`Y_v^L`.

## §4. The recursion, complexity and the corollaries

**Normal forms.**
- *Amalgam:* `g = a_1 ⋯ a_m`, with the syllables alternating in `B_1 ∖ K` and `B_2 ∖ K`.
- *HNN:* the Britton form `g = b_0 t^(ε_1) b_1 ⋯ t^(ε_m) b_m`, with no pinch.
- Either form is computed from a word by merging syllables and testing membership in the finite sets
  `K` or `φ(K)`. That is polynomially many calls to the word problems of the vertex groups, on words of
  length at most the input length plus a constant.

**Evaluation.**
- The normal form lists the pieces `P_0 ∋ 1, P_1, ..., P_m ∋ g` along the tree path, with the
  representative of `P_(i+1)` equal to that of `P_i` times its syllable (followed by `t^(ε_i)` in the HNN
  case). It also gives the exit coordinate `b_i` of each `P_i`, and the coordinate `b_m` of `g` in `P_m`.
- Whether `P_i ∈ T_W` is a membership test against finitely many fixed cosets.
- Evaluating `z_(P_i)` at the `|K|` elements of its exit interface `b_i J_τ` gives the entry data of
  `P_(i+1)`. With its type this names `z_(P_(i+1))`, a core point or some `z_(v, τ, p)`.
- Finally `y_*(g) = z_(P_m)(b_m)`.
- This is item 1 of the target.
- Membership in `C` follows: `C = {h : y_*(hw) = y_*(w) for all w ∈ W}`. Indeed, `g·y_* = y_*` iff
  `(g·y_*)|_W = y_*|_W`, by isolation, and `C = C^(-1)`.
- This proves item 2 for one edge.

**Graphs of groups.**
- Removing one edge of a finite graph of groups exhibits `π_1` as an amalgam or an HNN extension over
  that finite edge group. The vertex groups are the `π_1` of the smaller graphs.
- Their word problems, and their isolated points, reduce by induction, and polynomial reductions
  compose finitely often. This is item 2.

**Item 3.**
- *Pass to a free subgroup.* Let `F ⊴ A` be free of finite index, with `A = ⊔_(c ∈ R) Fc`. The
  recoding `y^F(f) = (y(fc))_(c ∈ R)` is `F`-equivariant. It carries `Y` to an SFT over `F` and `y_*` to
  an isolated point with stabilizer `C ∩ F`.
- *Isolated points over `Z`.* Write `F_n = Z * F_(n−1)` and induct on `n`. The `z_j` are isolated points of
  SFTs over `Z` and over `F_(n−1)`. Every isolated point of a `Z`-SFT is eventually periodic in both
  directions. Beyond the window, a position `p` is a cut
  point, so by (UE) the right tail from `p` is the unique extension of its label. A repeated label at
  `p < p'` then forces period `p' − p`, and a finite alphabet forces a repeat.
- *A finite automaton.* So a `Z`-syllable `x^e` is evaluated by a finite automaton reading `x^(±1)` letter
  by letter, and an `F_(n−1)`-syllable by the automaton given by induction. Syllables end where the letter
  changes factor, so the finite control of §4 composes these into one finite automaton on reduced words
  computing `y_*^F`.
- *Regularity.* The reduced word of `hw` is that of `h` with a suffix of length at most `|w|` cancelled
  and a word appended. So an automaton that remembers its last `max_(w ∈ W) |w|` states decides
  `y_*(hw) = y_*(w)` for all `w ∈ W`. Hence the reduced words of `C ∩ F` form a regular language.
- *Finite generation.* `C ∩ F` is a rational subset of `F`, hence finitely generated (Anisimov–Seifert:
  a subgroup is a rational subset iff it is finitely generated). It has finite index in `C`, so `C` is
  finitely generated too.
- *The equivalence.* It follows with corollary (a) of `relative-seeds-glue-graphs-of-groups-into-class-c`.

**Item 4.** Dunwoody: a finitely presented group is accessible. So it is `π_1` of a finite graph of
groups with finite edge groups and finitely generated vertex groups with at most one end. Isolated points
over finite vertex groups are finite data. Apply item 2. `∎`

## §5. Compression collapses light cones

This proves the last remark of the target.
- **Set-up.** Let `T` be `d`-regular with an end `ξ`. Levels are Busemann levels. `a_m(v)` is the
  ancestor of `v` at height `m` toward `ξ`, and `D_ρ(w)` is the set of descendants of `w` at depth `ρ`.
- **Windows are caps.** Two vertices at one level are at distance `2h`, where `h` is the height of
  their common ancestor. So the window of horospherical radius `r` around `u` is `D_ρ(a_ρ(u))`, with
  `ρ = ⌊r/2⌋`.
- **The recursion.** Let `z(v)` be a function of `z` on the window around `parent(v)`, together with
  bounded base data. That window is `D_ρ(a_(ρ+1)(v))`. For `u` in it, `a_(ρ+1)(u) = a_(ρ+2)(v)`, so the
  windows of all such `u` are the one set `D_ρ(a_(ρ+2)(v))`.
- **Induction.** The dependence of `z(v)` at `m` levels up is the single cap `D_ρ(a_(ρ+m)(v))`, which
  has `(d−1)^ρ` vertices.
- **Conclusion.** Hence `s(w) = z|_(D_ρ(w))` obeys `s(w') = Θ(s(w))` for each child `w'` of `w`, with `Θ`
  depending on bounded base data. The layer is a finite-state transport away from `ξ`.

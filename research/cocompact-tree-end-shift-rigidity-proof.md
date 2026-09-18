---
rg: 2
id: cocompact-tree-end-shift-rigidity-proof
kind: route
title: Vertex-stabilizer rules collapse every quantum family onto the vertices of the tree, and the edge rule then makes the away-pointing projections along each geodesic a monotone chain
target: cocompact-tree-end-shifts-are-quantum-rigid
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products
  - farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts
  - cantor-crossed-product-leavitt-tensors-are-k-trivial
  - deterministic-extensions-of-rigid-sfts-are-rigid
---

Unlike `free-group-boundary-shift-rigidity-proof`, which runs the chain on a tree Cayley graph, where
each site is a vertex, Step 1 here first identifies all sites coding one vertex. That is what makes
infinite vertex stabilizers harmless.

Notation as in the target. Write `[w → u]` for the edge from `w` to its neighbour `u`, and `hc v_i` for
`(hc)·v_i`.

## Step 0. Coding (item 1)

- **Locality.** (R1) involves the sites `h, hs` with `|s| <= D_0`. (R2) involves `hc, hc'` with
  `|c|, |c'| <= D_0`. Both lie in `hB_{D_0}`, so `X_T` is an SFT with forbidden patterns in `B_{D_0}`.
- **`x_ξ ∈ X_T`.**
  - (R1): for `s ∈ Λ_i` we have `hs v_i = h v_i`, so
    `x_ξ(hs)_i = s^{-1} h^{-1}[edge at h v_i toward ξ] = s^{-1} x_ξ(h)_i`.
  - (R2): the arrow at `hc v_i` is `hc·x_ξ(hc)_i`, and it runs along `h·ε` iff `x_ξ(hc)_i = ε_c`. The end
    `ξ` lies beyond exactly one endpoint of the edge `h·ε`, so exactly one endpoint points across.
- **Every `x ∈ X_T` is some `x_ξ`.**
  - *Arrows are well defined.* For a vertex `w = g v_i`, set `P(w) = g·x(g)_i`. (R1) for `s` gives
    `x(h s^{-1})_i = s·x(h)_i`, so (R1) holds for all `λ ∈ Λ_i` by induction on word length. If
    `g v_i = g' v_i` then `g' = gλ` with `λ ∈ Λ_i`, and `g'x(g')_i = gλλ^{-1}x(g)_i = P(w)`.
  - *Each edge is crossed once.* Every edge is `h·ε` for some `h` and some representative `ε`, and (R2)
    at `h` says exactly one endpoint's arrow crosses it.
  - *The field is an end.* Follow arrows from any vertex. Arriving at `b` from `a` means
    `P(a) = [a → b]`, so `P(b) ≠ [b → a]`, and the path never backtracks. A non-backtracking infinite
    path in a tree is a geodesic ray.
  - *All rays agree.* For adjacent `a, b`, one of them points to the other, so one ray is a tail of the
    other. `T` is connected, so all rays define one end `ξ`, and `P(v)` is the first edge from `v`
    toward `ξ`. So `x = x_ξ`.
- **Homeomorphism.**
  - Each `x_ξ(h)_i` is locally constant in `ξ`, and `ξ ↦ x_ξ` is bijective. Both spaces are compact
    Hausdorff.
  - Equivariance: `x_{λξ}(h)_i = h^{-1}λ·[edge at λ^{-1}h v_i toward ξ] = x_ξ(λ^{-1}h)_i`. ∎

## Step 1. Stabilizer collapse (item 3)

Fix `D >= D_0`, a field `k` and a `D`-quantum family `(E_a(h))`. Replace each `S_i` by `S_i ∪ S_i^{-1}`,
which changes no length.

- **Marginals.** `E^i_b(h) = Σ_{a_i = b} E_a(h)`. For fixed `h` and `i` these are orthogonal idempotents
  summing to `I`. Orthogonality of the `E_a(h)` gives `E_a(h) = ∏_i E^i_{a_i}(h)`.
- **Partial-pattern lemma.** Let `F ⊆ hB_D`, and prescribe one coordinate value `b_g` of the letter at
  each `g ∈ F`. If no pattern occurring in `X_T` satisfies the prescription, the product of the
  prescribed marginals is `0`.
  - All factors sit at sites of `hB_D`, pairwise at distance `<= 2D`, so they commute (Q2).
  - Multiply by `Σ_a E_a(g) = I` for each `g ∈ hB_D \ F` and expand the marginals. Every term is a full
    `hB_D`-pattern extending the prescription, hence does not occur in `X_T`, hence is `0` (Q3).
- **Relabeling for `s ∈ S_i`.** The sites `h, hs` lie in `hB_D`, and every point of `X_T` obeys (R1).
  So `E^i_b(h) E^i_{b'}(hs) = 0` whenever `b' ≠ s^{-1}b`. Insert `I = Σ_{b'} E^i_{b'}(hs)` and
  `I = Σ_{b''} E^i_{b''}(h)`:
  `E^i_b(h) = E^i_b(h) E^i_{s^{-1}b}(hs) = E^i_{s^{-1}b}(hs)`.
- **All of `Λ_i`.** Write `λ = s_1 ⋯ s_n` with `s_t ∈ S_i` and apply the relabeling `n` times:
  `E^i_b(h) = E^i_{λ^{-1}b}(hλ)`. This is item 3.
- **Vertex operators.** Let `w = g v_i` and let `e = [w → u]` be an edge at `w`. Set
  `P[w → u] = E^i_{g^{-1}e}(g)`.
  - It is well defined. `i` is fixed by the orbit of `w`. If `g' v_i = w` then `g' = gλ` with
    `λ ∈ Λ_i`, and `E^i_{g'^{-1}e}(g') = E^i_{λ^{-1}g^{-1}e}(gλ) = E^i_{g^{-1}e}(g)`.
  - For each vertex `w`, the `P[w → u]` over the neighbours `u` of `w` are orthogonal idempotents
    summing to `I`.
  - `E^i_b(h) = P[h v_i → u]`, where `h·b = [h v_i → u]`. So every `E_a(h)` is a product of
    vertex operators. ∎

## Step 2. The edge rule: `P[u → w] = I − P[w → u]`

- Every edge is `h·ε` for some `h` and representative `ε = {c v_i, c' v_j}`. Name its endpoints
  `w = hc v_i` and `u = hc' v_j`.
- `hc·ε_c = h·ε = [w → u]`, so `P[w → u] = E^i_{ε_c}(hc)`. Likewise `P[u → w] = E^j_{ε_{c'}}(hc')`.
- The sites `hc, hc'` lie in `hB_{D_0} ⊆ hB_D`, and (R2) forbids "both" and "neither". By the
  partial-pattern lemma:
  - "both" gives `P[w → u] P[u → w] = 0`;
  - "neither" gives `(I − P[w → u])(I − P[u → w]) = Σ_{b ≠ ε_c, b' ≠ ε_{c'}} E^i_b(hc) E^j_{b'}(hc') = 0`.
- Expanding the second and using the first gives `I − P[w → u] − P[u → w] = 0`. ∎

## Step 3. Monotone chains

For idempotents write `p <= q` when `pq = qp = p`. This is transitive: if `p <= q <= r`, then
`pr = pqr = pq = p` and `rp = rqp = qp = p`. For a directed edge `e = [u → w]`, the half-tree `T_e` is
the set of vertices closer to `w` than to `u`, and `ē = [w → u]`, so `T_ē` is the complement of `T_e`.

- **Elementary step.** Let `u ≠ z` be neighbours of `w`. Then `P[w → z] <= P[u → w]`.
  - `P[w → z]` and `P[w → u]` are orthogonal (Step 1, same vertex).
  - So `P[w → z](I − P[w → u]) = P[w → z] = (I − P[w → u]) P[w → z]`. Step 2 turns `I − P[w → u]`
    into `P[u → w]`.
- **Chain lemma.** If `T_f ⊆ T_e`, then `P[f] <= P[e]`.
  - Let `e = [u → w]`, `f = [u' → w']` and `f ≠ e`.
  - `w' ∈ T_f ⊆ T_e` and `u ∉ T_e`, so the geodesic from `u` to `w'` crosses `e`, and first, as
    `u → w`.
  - `T_ē ⊆ T_f̄` and `u ∈ T_ē`, so `u` is on the `u'` side of `f`. The geodesic from `u` to `w'` crosses
    `f`, and last, as `u' → w'`.
  - So there is a geodesic `u = y_0, w = y_1, …, y_m = u', y_{m+1} = w'`, and `m >= 1` since `f ≠ e`.
  - Consecutive vertices of a geodesic are distinct, so the elementary step gives
    `P[y_t → y_{t+1}] <= P[y_{t-1} → y_t]` for `1 <= t <= m`. Transitivity finishes. ∎

## Step 4. Any two vertex operators commute

- **Tree trichotomy.** For directed edges `e, f`, one of `T_f ⊆ T_e`, `T_e ⊆ T_f`, `T_e ∩ T_f = ∅`,
  `T_e ∪ T_f = V(T)` holds.
  - If `e, f` are the same undirected edge, then `f = e` or `f = ē`, and `T_ē` is the complement of `T_e`.
  - Otherwise `T − e = X ⊔ Y` with `f` inside `Y`. Then `Y − f = Y_1 ⊔ Y_2`, where `Y_1` contains the
    endpoint of `e` in `Y`.
  - The half-trees of `e` are `X` and `Y_1 ∪ Y_2`. Those of `f` are `Y_2` and `X ∪ Y_1`, which is
    connected through `e`.
  - Each of the four pairings is nested, disjoint, or covers `V(T)`.
- **Commutation.** Let `p = P[e]` and `q = P[f]`.
  - Nested: `p <= q` or `q <= p` by the chain lemma, so `pq = qp`.
  - Disjoint: `T_f ⊆ T_ē`, so `q <= P[ē] = I − p` (Step 2). Hence `q(I − p) = q = (I − p)q`, so
    `qp = 0 = pq`.
  - Covering: `T_ē ⊆ T_f`, so `I − p <= q`, and `I − p` commutes with `q`. Hence so does `p`.

## Step 5. Conclusion (item 2)

By Step 1 every `E_a(h)` is a product of vertex operators, and by Step 4 these commute pairwise. So the
family commutes, for every `D >= D_0` and every field `k`. No step used a property of `k`, nor any
commutation beyond Q2 inside one ball `hB_D`. ∎

## Item 4. Dynamics

- **Topological freeness.** Assume every vertex has degree `>= 3` and there are no nontrivial
  half-tree fixators. By item 1 we may work on `∂T`, whose sets `∂T_f` form a basis.
  - Suppose `λ` fixes a nonempty open set pointwise. Then it fixes some `∂T_f` pointwise,
    `f = [v → y]`.
  - Every vertex `z ∈ T_f` is the centre of a tripod of ends in `∂T_f`, that is, it has three
    neighbours whose half-trees away from `z` meet `∂T_f`.
    - If `z ≠ y`, take two neighbours of `z` away from `y`, and the neighbour toward `y`. The last
      works because `y` has a neighbour other than `v` and not toward `z`.
    - If `z = y`, pick a neighbour `a ≠ v` of `y`. Then `a ≠ y` is fixed by the previous case, and so
      is a second such neighbour `a'`. `y` is the midpoint of the geodesic `a, y, a'`, so it is fixed.
    - Half-trees are infinite and contain ends, since no vertex is a leaf.
  - An automorphism fixing three ends fixes the unique vertex common to the three lines they span.
  - So `λ` fixes `T_f` pointwise, and `λ = 1`.
- **RF obstruction.**
  - `Λ_i` fixes `v_i`, so it permutes the finite ball `B_n(v_i)`. The kernel `K_n` has finite index.
  - The finite residual `R_i` lies in every `K_n`, so it fixes `T` pointwise and acts trivially on
    `∂T ≠ ∅`.
  - If the action is topologically free, `R_i = 1`, so `Λ_i` is residually finite.
  - A subgroup with property FA fixes a vertex (Serre, recalled), so it lies in a conjugate of some
    `Λ_i` and is residually finite.
- **Minimality.** Recalled, as stated.

## Item 5. Finite fibres

- `H` fixes `ξ`, so it fixes `x_ξ` and permutes the nonempty finite set `π^{-1}(x_ξ)`.
- The kernel of `H → Sym(π^{-1}(x_ξ))` has finite index in the infinite group `H`, so it contains
  some `λ ≠ 1`. `λ` fixes a point of `Z`.
- Deterministic extensions have finite fibres
  (`deterministic-extensions-of-rigid-sfts-are-rigid`, item 3).
- For `W ⊆ X_T × Y`, the projection of `W` to `X_T` is closed, nonempty and `Λ`-invariant, so by
  minimality it is all of `X_T`. Pick `(x_ξ, y) ∈ W` and `1 ≠ λ ∈ H`. Then `(λ, 1)` fixes
  `(x_ξ, y)`. ∎

## Item 6. Calibration

Let `Λ = PSL_2(Z[1/p])` act on `T = T_{p+1}`, with `∂T = P^1(Q_p)`.

- **Hypotheses of item 2.** `Λ` is finitely presented. It is an amalgam of two copies of `PSL_2(Z)`
  over the image of `Γ_0(p)` (Serre, recalled). There are two vertex orbits, and the stabilizers are
  conjugates of `PSL_2(Z)`, which are finitely generated. So `X_T` is rigid.
- **Minimal.**
  - `Z[1/p] ⊇ p^{-n}Z` is dense in `Q_p`. So the elementary unipotents of `Λ` are dense in those of
    `PSL_2(Q_p)`, and these generate `PSL_2(Q_p)`.
  - Hence `Λ` is dense in `PSL_2(Q_p)`, which is transitive on `P^1(Q_p)`, so every orbit is dense.
- **Topologically free.** A non-identity Möbius transformation fixes at most two points, and
  `P^1(Q_p)` has no isolated points. The degree is `p + 1 >= 3`, and an element fixing a half-tree
  fixes infinitely many ends, so it is trivial. So item 4 applies too.
- **Finite-order elements are fixed-point free.**
  - Let `A ∈ SL_2(Z[1/p])` with `A ≠ ±I` and `A^n = ±I`. A fixed point of `A` on `P^1(Q_p)` is an
    eigenline over `Q_p`, with eigenvalue `μ ∈ Q_p` and `μ^{2n} = 1`.
  - `μ = ±1` would make `A` equal to `±I` or `±`(unipotent), and the latter has infinite order. So `μ`
    is a root of unity other than `±1`, and `μ + μ^{-1} = tr A` is rational.
  - That forces `μ` to have order 3, 4 or 6, so `Q_p` contains `i` or `ζ_3`.
  - `i ∈ Q_p` iff `p ≡ 1 mod 4`, and `ζ_3 ∈ Q_p` iff `p ≡ 1 mod 3`. Neither holds for `p = 2`, `p = 3`
    or `p ≡ 11 mod 12`.
- **Ring gates.**
  - (E): `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.
  - Simplicity and centre: recalled, as in the target.
  - (K): `farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`, which needs only finite
    subgroups acting freely.
- **Torsion-free `Γ`.** Take a principal congruence subgroup of level `N >= 3`, `p ∤ N`. It is
  torsion-free and of finite index, with finitely generated vertex stabilizers of finite index.
  - Rigidity is by item 2.
  - `PSL_2(Q_p)` is simple and `Γ` has finite index, so the open closure of `Γ` is all of
    `PSL_2(Q_p)`. So `Γ` is minimal, as above, and it is topologically free.
  - (K) comes from `cantor-crossed-product-leavitt-tensors-are-k-trivial`.
  - `Γ` meets the Borel subgroup `Z[1/p] ⋊ Z` in a finite-index subgroup. That subgroup contains a
    copy of `m Z[1/p]`, which is abelian and not virtually cyclic. Abelian subgroups of virtually
    free groups are virtually cyclic, so `Γ` is not virtually free. ∎

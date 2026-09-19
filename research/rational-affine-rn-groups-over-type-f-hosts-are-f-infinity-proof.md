---
rg: 2
id: rational-affine-rn-groups-over-type-f-hosts-are-f-infinity-proof
kind: route
title: Full-rank S-arithmetic affine hosts act cocompactly on a product of Bruhat-Tits trees with cyclic stabilisers, so they are F_infinity and SWZ Theorem 4.15 transfers this to V_p; the non-FP_2 host Z[1/6] x <2/3> escapes FP1, FP2, SWZ and N = K_infinity
target: rational-affine-rn-groups-over-type-f-hosts-are-f-infinity
requires:
  - rover-nekrashevych-finite-presentation-criteria
  - rover-nekrashevych-fp-iff-finite-lift-presentation
  - persistent-automata-rn-group-fp-iff-group-fp
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/kinf_affine_test.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-kinf-affine-test.txt
---

Notation is that of the claim.

## Imports (quoted from arXiv:1712.05361v3, read 2026-09-19)

- **SWZ Theorem 4.15.** The extracted text reads "Let G ≤ Aut(T_d) be self-similar. If G is of type F_{n−1} then so is
  V_d(G)." The subscript is garbled in extraction. The proof ends: "The group N × (C_k, C_k) is G ≀ S_k, which is
  virtually isomorphic to G^k and therefore of type F_n by assumption. Applying the theorem it follows that V_d(G) …
  is of type F_n." Either reading gives: `G` of type `F_∞` implies `V_d(G)` of type `F_∞`. That is all we use.
- **SWZ Lemma 5.3.** "Let d ≥ 3. Let G be a group with a faithful self-similar action on T_{d−1}. Then G admits a
  faithful, persistent self-similar action on T_d. If the action on T_{d−1} is finite-state then so is the action on
  T_d."
- **SWZ Theorem 5.8.** "Let G ≤ Aut(T_d) be a persistent, finite-state self-similar group. If V_d(G) is of type F_n
  (or FP_n) then so is G."
- **Brown's criterion** (K. S. Brown, *Finiteness properties of groups*, JPAA 44 (1987), Prop. 1.1). A group acting
  cellularly and cocompactly on a contractible CW complex, with every cell stabiliser of type `F_∞`, is of type `F_∞`.

## Step 1. The affine action is self-similar and finite-state

Let `g(x) = ux + b` with `u ∈ U_0` and `b ∈ Z[1/m]`. Write `x = i + p y` with `i ∈ {0, …, p-1}`. Since `p ∤ m`, `u`
is a `p`-adic unit and `Z[1/m] ⊂ Z_p`. So `ui + b ≡ j (mod p)` for a unique digit `j`, and
`g(i + py) = j + p(uy + b_i)` with `b_i = (ui + b - j)/p`. Now `Z[1/m] ∩ pZ_p = pZ[1/m]`, so `b_i ∈ Z[1/m]`, and the
section `g|_i = (x ↦ ux + b_i)` lies in `H(m, U_0)`. The action is faithful, because an affine map of `Z_p` that is the
identity is `u = 1, b = 0`.

For finite-state, work in the real absolute value. We have `|b_i| ≤ (|b| + (|u| + 1)(p - 1))/p`. So if
`|b| ≤ C` with `C ≥ |u| + 1`, then `|b_i| ≤ C`. Let `D` be the lcm of the denominators of `u` and `b`. Then
`ui + b - j ∈ D^{-1}Z`, and dividing by `p` stays in `D^{-1}Z` because the result lies in `Z[1/m]` and `p ∤ D`. So
every iterated section `x ↦ ux + b'` has `b' ∈ D^{-1}Z` with `|b'| ≤ max(|b|, |u| + 1)`. There are finitely many such
`b'`, so the set of sections is finite.

## Step 2. Part (1)

`BS(1,2) = ⟨a, t | a t a^{-1} = t^2⟩` is an HNN extension of `Z` over `Z`. Its presentation complex is a finite
`K(π, 1)`, so it is of type `F`. It is the case `m = 2`, `U_0 = ⟨2⟩` of Step 1 on `Z_3`, so it is a self-similar subgroup
of `Aut(T_3)`. SWZ 4.15 gives `V_3(BS(1,2))` of type `F_n` for every `n`.

## Step 3. Part (2): full-rank hosts are `F_∞`

Let `P_m = {ℓ_1, …, ℓ_r}`. Let `Y = ∏_i BT_{ℓ_i}`, a CAT(0) cube complex and hence contractible.

- **The action.** Identify the vertices of `BT_ℓ` with the balls `c + ℓ^k Z_ℓ` of `Q_ℓ` (for `c ∈ Q_ℓ`, `k ∈ Z`), with
  edges for inclusions of index `ℓ`. `Aff(Q_ℓ)` acts on balls, preserving inclusion, so it acts on `BT_ℓ`. The map
  `x ↦ ux + b` shifts the level `k` by `v_ℓ(u)`. So `H = H(m, U_0)` acts diagonally, cellularly and without
  inversions on `Y`.
- **Cocompactness.** The valuation map `v = (v_{ℓ_1}, …, v_{ℓ_r}) : U_0 → Z^r` has finite-index image, since `v` maps
  `U_m` isomorphically onto `Z^r` and `U_0` has finite index in `⟨-1⟩ × U_m`. So there are finitely many level vectors
  mod `v(U_0)`. For a fixed level vector `(k_1, …, k_r)`, the translations act transitively on the tuples of balls
  `(c_i + ℓ_i^{k_i} Z_{ℓ_i})_i`. The reason is that `Z[1/m]` is dense in `∏ Q_{ℓ_i}`: it contains `Z`, which is dense
  in `∏ Z_{ℓ_i}` by the Chinese remainder theorem, together with every `m^{-k} Z`. So there are finitely many vertex
  orbits. Each cube is determined by its lowest vertex and a subset of the `r` directions together with a child ball,
  and there are finitely many choices for these. So there are finitely many cell orbits.
- **Stabilisers.** Let `g = (x ↦ ux + b)` stabilise a cube `σ`. The levels of the vertices of `σ` form a translate
  of `{0,1}^J`, and `g` shifts levels by `v(u)`. So `v(u) = 0`, which gives `u = ±1`. Then `g` fixes every vertex of
  `σ`, because it preserves levels and the vertices of a cube have distinct level vectors.
  - For `u = 1`: `b` moves every ball `c_i + ℓ_i^{k_i} Z_{ℓ_i}` to itself, so `v_{ℓ_i}(b) ≥ k_i` for all `i`. Then
    `b ∈ Z[1/m] ∩ ⋂_i ℓ_i^{k_i} Z_{ℓ_i} = M Z` for `M = ∏ ℓ_i^{k_i}`, which is infinite cyclic.
  - If `-1 ∈ U_0`, the stabiliser may also contain reflections `x ↦ -x + b`. It is then `MZ` or `MZ ⋊ Z/2`
    (infinite dihedral).
  - Either way it is of type `F_∞`.
- **Conclusion.** By Brown's criterion `H(m, U_0)` is of type `F_∞`. By Step 1 and SWZ 4.15, `V_p(H(m, U_0))` is of
  type `F_∞`. With `U_0 = Z[1/m]^×` this is `V_p(Aff(Z[1/m]))`. ∎

**Remark (why rank matters).** If `rank U_0 < r`, then `v(U_0)` has infinite index and the action on `Y` is not
cocompact. For `H_*`, `v(2/3) = (1, -1)`, so `H_*` acts cocompactly only on the horocyclic sublevel `k_2 + k_3 = 0`.
That is the Diestel–Leader graph `DL(2,3)`, which has cycles and so is not contractible, and the vertex stabilisers
are `MZ`. So Brown's criterion gives nothing, which matches `H_*` not being `FP_2`.

## Step 4. Part (3), the corrections

- (a) follows from (2) with `m = 2`, `U_0 = ⟨2⟩` and `p = 3`.
- (b) follows from (2) with `m = 6`, `U_0 = ⟨-1, 2, 3⟩`. The Σ-theoretic reason is that the archimedean character
  is not in `Σ^c`. The monoid `U_{χ_∞} = {u : |u| ≥ 1}` contains `3/2` and `4/3`. So the `Z[U_{χ_∞}]`-submodule
  generated by `1` is a ring containing `1/2 = 3/2 - 1` and `1/3 = 4/3 - 1`, hence all of `Z[1/6]`. Only the finite
  places contribute, and for full rank their characters are linearly independent. Over
  `F_q(t)`, by contrast, `∞` is a valuation like any other, and the product formula makes the three characters of
  Bux's example sum to zero.

## Step 5. Part (4): the host `H_* = Z[1/6] ⋊ ⟨2/3⟩` on `Z_5`

- **Generation.** `Z[1/6]` is generated by `1` as a `Z[(2/3)^{±1}]`-module: `1/2 = 3/2 - 1` and `1/3 = 1 - 2/3`, and
  the module is closed under products with `2/3` and `3/2`. So `H_* = ⟨t, a⟩`. Step 1 gives faithful, finite-state
  and self-similar. The artifact computes the section-closed generating set
  `S = {(2/3, -2/3), (2/3, -1/3), (2/3, 0), (2/3, 1/3), (1, 1)}` (pairs `(u, b)`).
- **Not `FP_2`.** This is Bieri–Strebel (almost finitely presented soluble groups, 1978): an `FP_2` group without
  non-abelian free subgroups that maps onto `Z` is an ascending HNN extension over a finitely generated base inside
  the kernel. Here the kernel is `Z[1/6]`, whose finitely generated subgroups are the `6^{-k}Z`. `(2/3) · 6^{-k}Z` is
  not in `6^{-k}Z`, and `(3/2) · 6^{-k}Z` is not either, so no such base exists.
- **Not contracting.** Every section of `x ↦ ux + b` has multiplier `u`. A contracting group has a finite nucleus
  containing all sections of `g` at large depth. But `a^n` has multiplier `(2/3)^n`, and these are pairwise
  distinct, so infinitely many elements would have to lie in the nucleus.
- **Not persistent.** Persistence at `i` needs `s(i) = i` for all `s ∈ S`. But `t(i) = i + 1 mod 5`.
- **`N ≠ K_∞`.** The artifact enumerates, for a word `w` in `S^{±1}`, the graph of its freely reduced iterated
  sections. It checks that each vertex acts trivially on the first level, which holds since `w ∈ N`. Then:
  - If this graph is finite and acyclic, `w ∈ K_∞`, since all sections become freely trivial at bounded depth.
  - If it has a directed cycle, some nonempty reduced word recurs at every depth, so `w ∉ K_∞`.
  - The output is `('cyc', n)`, with `n` the graph size: `BS: 5`, and `r_1, …, r_4: 19, 201, 2110, 42456`.
  - This is exact integer and rational arithmetic, and the claim is a finite check.
- **Persistent contrast.** SWZ Lemma 5.3 with `d = 6` gives a faithful, finite-state, persistent action of `H_*` on
  `T_6`. If `V_6(H_*)` were `F_2`, SWZ 5.8 would make `H_*` `F_2`, contradicting "not `FP_2`".

## Step 6. Part (5): the piecewise model, and what is open

An element of `V_5(H_*)` sends each ball `c + 5^k Z_5` of a partition (with `c ∈ Z`) to a ball `c' + 5^{k'} Z_5` by
`x ↦ c' + 5^{k'} h((x - c)/5^k)` with `h ∈ H_*`. This is affine with multiplier in `5^Z ⟨2/3⟩` and translation in
`Z[1/30]`. Conversely, let `x ↦ ux + b` (`u ∈ 5^Z⟨2/3⟩`, `b ∈ Z[1/30]`) map a ball `B = c + 5^k Z_5` onto a ball
`c' + 5^{k'} Z_5`. Then `5^{k-k'} u ∈ ⟨2/3⟩`, and `(uc + b - c')/5^{k'} ∈ Z[1/30] ∩ Z_5 = Z[1/6]`, so the map has
this form. So `V_5(H_*)` is the piecewise group described in the claim. The analogy with `G([0,b]; A, P)` of the
Bieri–Strebel memoir (arXiv:1411.2868, Chapter D) is then direct: `A = Z[1/30]` and `P = ⟨5, 2/3⟩`, with
`Aff(A, P)` not finitely presented. Chapter D, Proposition 3 transfers non-finite-presentation from `Aff(A, P)` to
`G(R; A, P)` and `G([0, ∞); A, P)`. The memoir says that no analogue is known for `[0, b]`. Our Cantor case is
compact, like `[0, b]`, and it is not decided here.

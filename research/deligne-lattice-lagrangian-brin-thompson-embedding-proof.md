---
rg: 2
id: deligne-lattice-lagrangian-brin-thompson-embedding-proof
kind: route
title: Proof that Deligne's lattice embeds in the finitely generated simple commutator subgroup of the Lagrangian Brin-Thompson group
target: deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group
requires:
  - unimodular-maslov-cantorization-is-minimal-expansive
  - deligne-extension-dies-on-lagrangian-cantor-covers
  - lagrangian-thompson-group-contains-deligne-lattice
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - nekrashevych-symmetric-and-alternating-full-groups
  - nekrashevych-expansive-groupoid-criteria
  - ample-groupoid-products-expansive-iff-factors-are
---

The notation is that of the target. Write `Γ = Sp_{2n}(Z)`, `M = Y_u × F_n`, and
`𝒢 = 𝒢_n × G_2`.

## Step 1. The groupoid 𝒢

- **Basic properties.** `𝒢` is Hausdorff, second countable and étale, and its unit space
  `M × C` is a Cantor set.
- **Minimal.**
  - Orbits of a product are products of orbits.
  - `Γ ↷ M` is minimal by items 5 and "Consequences" of
    `unimodular-maslov-cantorization-is-minimal-expansive`.
  - `G_2` is minimal.
- **Effective.**
  - `𝒢_n` is the action groupoid of a topologically free action (item 6 there), so the
    interior of its isotropy is its unit space. `G_2` is effective too.
  - An open set of isotropy in `𝒢_n × G_2` contains a product `U × U'` of open
    bisections, each of which lies in the isotropy of its factor.
  - So `U` and `U'` are units, and the product is effective.
- **Purely infinite.** A clopen set of `M × C` is a finite disjoint union of rectangles
  `Q_i × P_i`.
  - In `G_2`, each `P_i` is properly infinite, via bisections `U_i` and `U'_i` with
    source `P_i` and disjoint ranges in `P_i`.
  - Then `⊔ id_{Q_i} × U_i` and `⊔ id_{Q_i} × U'_i` witness proper infiniteness of the
    union.
  - This is the argument of Step 5 of `amenable-purely-infinite-groupoid-kazhdan-host-proof`.
- **Expansive.**
  - `Γ` is finitely generated, and `Γ ↷ M` is a subshift: item 3, with the finite
    coordinate `F_n` added to the partition.
  - So `(M ⋊ Γ) × G_2` is expansive by item 4 of
    `ample-groupoid-products-expansive-iff-factors-are`.
- **Orbits** are infinite.

## Step 2. The host is simple and finitely generated (item 1)

- **Simplicity.** By the Matui import, `D([[𝒢]])` is simple, and every nontrivial
  subgroup normalized by `D([[𝒢]])` contains it.
- **A = D.**
  - By Theorem 4.1 of the Nekrashevych import, `A(𝒢)` is simple and lies in every
    nontrivial normal subgroup of `[[𝒢]]`. In particular `A(𝒢) ≤ D([[𝒢]])`.
  - `A(𝒢)` is normal and nontrivial, so Matui gives `A(𝒢) ≥ D([[𝒢]])`.
- **Finite generation.** By Theorem 5.6 there, `A(𝒢)` is finitely generated.
- **Word problem.**
  - An element of `[[𝒢]]` is a finite list of pieces. Each piece is a Boolean word in
    cells, times a point of `F_n`, times a dyadic cylinder, and carries a label
    `(γ, g) ∈ Γ × V`.
  - Composition of lists and the test "is the identity" are computable. This uses item 7
    of the Cantorization node, the solvable word problems of `Γ` and `V`, and the fact
    that `(γ, g)` acts trivially on a nonempty open set only if `γ` acts trivially on
    `Y_u × F_n` (`γ = ±I` for odd `n`, `γ = I` for even `n`) and `g` is trivial there.
  - So every finitely generated subgroup has solvable word problem. ∎

## Step 3. The Maslov cocycle

This step follows item 2 of `deligne-extension-dies-on-lagrangian-cantor-covers` and
Step 2 of the proof of `lagrangian-thompson-group-contains-deligne-lattice`.

- **The lift to Λ̃.** `Γ̃_n` acts on the universal cover `Λ̃` of `Λ`, covering the action
  of `Γ`. The deck group is `⟨T⟩`.
  - The generator `z` of `π_1(Sp_{2n}(R))` acts as `T^2`.
  - Let `e` be the endpoint of the lift of `t ↦ e^{iπt} I_n`. Then `e` lies over `−I`,
    `e^2 = z^n`, and `e` acts as `T^n`.
- **The cocycle.**
  - Pull back `Λ̃ → Λ` along `π : Y_u → Λ` and choose a continuous section over the
    Cantor set `Y_u`.
  - This gives a locally constant cocycle `k : Γ̃_n × Y_u → Z` with
    `γ̃ s(y) = T^{k(γ̃,y)} s(γy)`.
  - In particular `k(z, ·) = 2`, and `k(e z^j, ·) = n + 2j`.

## Step 4. The action Φ

Fix `t ∈ V` of infinite order, for instance a nontrivial element of Thompson's group `F ≤ V`, and put

`Φ(γ̃)(y, v, x) = (γy, γ̄v, t^{k(γ̃,y)} x)` on `Y_u × F_n × C`.

- **It is an action.** This is the cocycle identity
  `k(γ̃_1 γ̃_2, y) = k(γ̃_1, γ_2 y) + k(γ̃_2, y)`.
- **It lies in [[𝒢]].** `k(γ̃, ·)` takes finitely many values on clopen sets `Y_j`, and
  on `Y_j × F_n × C` the map `Φ(γ̃)` is `(γ, t^j)`.
- **It is faithful.**
  - *Odd n.* If `Φ(γ̃) = id`, then `γ` acts trivially on `Y_u`, so `γ = ±I`.
    - Hence `γ̃ ∈ ⟨e, z⟩ = ⟨c⟩`, where `c = e z^{-(n-1)/2}` and `k(c, ·) = 1`.
    - So `γ̃ = c^j` acts as `t^j`, which forces `j = 0`.
  - *Even n.* If `Φ(γ̃) = id`, then `γ` acts trivially on `Y_u × F_n`. Since `−I` moves
    every point of `F_n`, this forces `γ = I`.
    - Hence `γ̃ = z^j` acts as `t^{2j}`, which forces `j = 0`.
  - In both cases `⟨z⟩ = ker(Γ̃_n → Γ)` acts on the `C` coordinate alone, by powers of
    `t^2`. For odd `n` the whole center `⟨c⟩` does, by powers of `t`. For even `n` the
    central involution `e z^{-n/2}` acts by `v ↦ −v` on `F_n`.

## Step 5. Landing in the commutator subgroup (item 2)

- **Finite abelianization.** `Γ̃_n` has property (T) for `n ≥ 2`
  (`deligne-universal-cover-lattice-is-non-rf-kazhdan`), so `Γ̃_n^{ab}` is finite
  (textbook). Let `m` be its order.
- **The copies.**
  - Split `C = C_0 ⊔ … ⊔ C_{m−1}` into nonempty clopen sets.
  - In `G_2`, any two nonempty clopen sets are equivalent, since the numbers of cones can
    be equalized by splitting. So there are `G_2`-bisections `β_j : C → C_j`, and
    involutions `σ_j ∈ V` exchanging `C_0` and `C_j` through `β_j β_0^{-1}` and fixing the
    rest.
  - Let `Φ^{(j)}(γ̃)` act as `(id × β_j) Φ(γ̃) (id × β_j)^{-1}` on `Y_u × F_n × C_j`, and
    as the identity elsewhere. Each `Φ^{(j)}` is a homomorphism into `[[𝒢]]`, and
    `Φ^{(j)} = σ_j Φ^{(0)} σ_j^{-1}`.
- **The diagonal.** Put `Φ_m(γ̃) = ∏_j Φ^{(j)}(γ̃)`.
  - The factors have disjoint supports, so `Φ_m` is a homomorphism.
  - Its restriction to `Y_u × F_n × C_0` is conjugate to `Φ`, so it is faithful.
- **The class vanishes.** In `[[𝒢]]^{ab}`,
  `[Φ_m(γ̃)] = m [Φ^{(0)}(γ̃)] = [Φ^{(0)}(γ̃^m)]`.
  - Since `m` kills `Γ̃_n^{ab}`, `γ̃^m ∈ [Γ̃_n, Γ̃_n]`, and so `Φ^{(0)}(γ̃^m) ∈ D([[𝒢]])`.
- **Conclusion.** `Φ_m` embeds `Γ̃_n` in `D([[𝒢]]) = D(2V_Λ(n))`. ∎

## Step 6. The case n = 1 (item 3)

- **The groupoid.**
  - For `n = 1`, `F_1` is a point and `Y_u` is the Farey Cantor set.
  - Conjugation by Minkowski's question-mark function turns piecewise-`PSL_2(Z)` maps
    between Farey arcs into prefix replacements between dyadic arcs (textbook). Mediants
    go to midpoints, and `PSL_2(Z)` preserves mediants.
  - So `𝒢_1` is the Cuntz groupoid on two cones. Moreover `C ⊔ C ≅ C` by `(i, x) ↦ ix`,
    which conjugates `V_{2,2}` to `V`.
- **The group.**
  - Hence `2V_Λ(1) ≅ [[G_2 × G_2]]`.
  - That group is `2V`: clopen sets of `C × C` are finite unions of dyadic bricks, and
    its germs are products of prefix replacements.
  - `2V` is simple (Brin), so Step 5 is not needed.
- **The lattice.** `Γ̃_1` is `B_3`, and its center `⟨c⟩` acts as `t`. ∎

## Step 7. Robustness

- Steps 1–5 used about `Y_u` only minimality, topological freeness and the
  equivariant map `π`. These hold for `Y_Λ` by item 8 of the Cantorization node, so
  simplicity and the embedding transfer.
- Step 1's expansivity, and hence finite generation, used item 3, which is proved only
  for `Y_u`.

---
rg: 2
id: tree-lattice-homogeneous-subshifts-are-not-quantum-rigid
kind: claim
title: The covering-map SFT of a complete square complex (Mozes type), and its algebraic homogeneous subshifts Γ\(H_1 × H_2), carry invariant probability measures over a reducible lattice F_m × F_n but are never quantum rigid, because compact stabilizers rotate every branch at once
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the open question (RA); this answers its test (T1) negatively, since the natural measure-preserving SFTs over products of trees are not rigid.
  thick-building-flat-sfts-are-never-quantum-rigid: that kills flat codings of buildings over their translation lattice Z^d; this kills codings of products of trees over a lattice of the product itself, by tree independence or by compact rotations.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that makes the BOUNDARY of an Ã₂ lattice rigid; this shows the interior homogeneous space of a tree-product lattice is not, which separates boundary dynamics (amenable) from homogeneous dynamics (measure-preserving).
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed; no priority claimed).
Mozes's aperiodic tilings are recalled for context only, not re-read.

## Setting

- `T_1` and `T_2` are regular trees of degrees `>= 3`, and `G = Aut(T_1) × Aut(T_2)`.
- `Λ = Λ_1 × Λ_2 ≤ G`, where each `Λ_i` acts simply transitively on the vertices of `T_i`. For
  example `Λ_i = F_(m_i)`, acting on its Cayley tree.
  - Sites are the vertices of `T_1 × T_2`, identified with `Λ`. The metric is the combinatorial one, so
    `d >= d_(T_i)` on each coordinate.
- `Γ ≤ G` acts freely and cocompactly on `T_1 × T_2`, and `Y_Γ = Γ\(T_1 × T_2)` is a compact square
  complex.
- **The covering SFT `X_Γ`.** Its points are the covering maps `φ : T_1 × T_2 → Y_Γ` that preserve the
  horizontal and vertical directions. The symbol at a site is `φ` restricted to that vertex's closed
  star. Being a covering map is a condition on stars, so `X_Γ` is an SFT over `Λ`, with
  `(λ.φ) = φ ∘ λ^(-1)`.
- **The identification.** Lifting gives `X_Γ ≅ Γ\G`. Every such `φ` equals `π ∘ g` for some `g ∈ G`,
  unique up to `Γ` on the left, and `Λ` acts by right multiplication.
  - So `X_Γ` carries the `G`-invariant probability measure of the cocompact lattice `Γ`, and `Λ`
    preserves it.
  - Hence `Λ ↷ X_Γ` is **not** topologically amenable.
- **Algebraic subshifts.** Let `H = H_1 × H_2 ≤ G` be closed, with `Γ, Λ ≤ H`. Then `Y := Γ\H` is a
  closed `Λ`-invariant subset of `X_Γ`, a subshift that need not be of finite type. It carries the
  `H`-invariant probability measure.

## Theorem

1. **The covering SFT.** For every `D >= 1` and every field, `X_Γ` is not `D`-quantum rigid.
2. **Algebraic subshifts.** Assume:
   - (a) `Γ ∩ (1 × H_2) = 1`;
   - (b) `H_2` is non-discrete, so the pointwise stabilizer in `H_2` of every finite subtree is
     nontrivial;
   - (c) no nontrivial element of `H_2` fixes a half-tree pointwise.

   Then `Y = Γ\H` is not `D`-quantum rigid for any `D`.
   - Example: `H = PGL_2(Q_p) × PGL_2(Q_l)`, with `Γ` an irreducible quaternionic lattice acting simply
     transitively on vertices (Mozes, Burger–Mozes, Rattaggi; recalled).
   - There (c) holds because a nontrivial element of `PGL_2` fixes at most two points of `P^1`, while
     a half-tree has uncountably many ends.
3. **Closed invariant subsets.** The same holds for every closed invariant subset of `X_Γ` or of `Y`
   that contains a point together with the modifications used below. It is not claimed for minimal
   subsets, and whether `Λ ↷ Y` is minimal is not checked.

## Proof

**Agreement.** Two points `Γg` and `Γg'` have the same symbol at a site `v` iff `γg = g'` on the star
of `v` for some `γ ∈ Γ`.
- On a connected region of agreement the element `γ` is constant, because `Γ` acts freely on vertices.

**1. Independence.**
- Choose half-trees `A, A' ⊆ T_1` at distance `> 2D + 4`.
- The rigid stabilizer of `A` in `Aut(T_1)` (fixing `T_1 \ A` pointwise) is uncountable, and so is
  that of `A'`. `Γ` is countable.
- So for `x = Γg` there are `a` and `a'`, supported in `A` and `A'`, with `g(a,1)g^(-1) ∉ Γ` and
  `g(a',1)g^(-1) ∉ Γ`.
- Put `y = Γg(a,1)` and `y' = Γg(a',1)`. Then `y, y' ≠ x`, `Δ(x, y) ⊆ N_1(A) × T_2`, and
  `Δ(x, y') ⊆ N_1(A') × T_2`. These sets are more than `2D` apart.
- Lemma 1 of `quantum-rigid-subshifts-cluster-the-modifications-of-each-point` applies.

**2. Compact rotation.**
- Take `S` = one vertex of `T_2`, `w >= 2D`, and `x = Γh ∈ Y`.
- By (b) there is `k ≠ 1` in `H_2` fixing `N_(w+1)(S)` pointwise. Put `y = Γh(1,k)`.
- `(1,k)` fixes every star in the slab `T_1 × N_w(S)`, so `y` extends the slab state of `x`.
- **`y ≠ x` somewhere in every deep branch `T_1 × C^w`.**
  - Otherwise agreement holds on the connected region `T_1 × C^w` with one `γ`.
  - Then `(1,k)^(-1) h^(-1) γ h` fixes `T_1 × C^w` pointwise. So its first coordinate is `1`, and its
    second fixes a half-tree, so it is `1` by (c).
  - Hence `γ = (1, h_2 k h_2^(-1)) ∈ Γ ∩ (1 × H_2) = 1` by (a). So `k = 1`, a contradiction.
- `T_2` has at least three branches at `S`. So the extensions of one slab state differ in two deep
  branches, which contradicts item 1 of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`.
  - That item holds for every subshift. `Λ_1` plays the role of `Λ_0`, and the free factor is
    `Λ_2 = F_n`.
  - For a general simply transitive `Λ_2`, the same proof runs on the tree `T_2`. ∎

## Lesson for general BH

This separates two kinds of non-elementary dynamics over the same group `F_m × F_n`.
- **Boundary dynamics** (`∂T_m ⊠ ∂T_n`, Ã₂ boundaries) are amenable, and rigid.
- **Homogeneous dynamics** `Γ\H` of an irreducible lattice are measure-preserving, hence non-amenable,
  and never rigid.

The mechanism is a *compact* stabilizer. The stabilizer of a slab state is a compact open subgroup,
and it rotates all branches at once, exactly as the isotropy of an emitter does. So the rotation
creates at least two free branches. Tree independence (the full `Aut`) makes it even easier.

Measure-preserving dynamics tends to have compact stabilizers of local data, and rigidity forbids
them. So test (T1) of `quantum-rigid-minimal-topfree-subshift-actions-are-amenable` comes out on
the side of (RA). A counterexample over `Λ_0 × F_n` must be a *tight* spacetime, one determined by a
single slab.

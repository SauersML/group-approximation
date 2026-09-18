---
rg: 2
id: twisted-bt-type-fn-interval-filtration-proof
kind: route
title: Filter the Stein sublevel complex by interval length, keep only grid intervals, and run a homological Brown criterion for filtered complexes
target: twisted-brin-thompson-type-fn-criterion
requires:
  - twisted-brin-thompson-type-fn-implies-type-an
  - stein-complex-elementary-intervals-are-grid-spheres
  - twisted-brin-thompson-finite-presentation-criterion
---

Sources:
- BZ = Belk--Zaremsky, arXiv:2001.04579, TeX on MSI (`gqsrc/bh-openq/2001.04579/`);
- FFWZ = arXiv:2603.24687v2, text on MSI (`/scratch.global/sauer354/bh-reviewer/2603.24687.txt`).

Let `G` act faithfully on a countable set `S`, and let `Γ = SV_G`. Necessity in items 1 and 2
is `twisted-brin-thompson-type-fn-implies-type-an`. Item 3 is recorded on the target, and
item 4 follows from item 1. It remains to prove sufficiency: `(HA_n) ⇒ FP_n`, and
`(A_n) ⇒ F_n`.

## Step 0. Homological algebra

Take left modules over a ring `R` and chain complexes `K` with `K_i = 0` for `i < 0`. Call
`K` **n-finite** if there is a complex `P` of finitely generated free modules, concentrated
in degrees `0..n`, and a chain map `φ: P → K` with `H_i(φ)` bijective for `i < n` and
surjective for `i = n`.

- **(a) Modules.** If `M` is of type `FP_{n−e}` and `0 ≤ e ≤ n`, then `M[e]` (placed in
  degree `e`) is n-finite: shift a partial resolution `F_{n−e} → ... → F_0 → M`. If
  `e > n`, then `M[e]` is n-finite with `P = 0`. More generally any complex with
  `H_i = 0` for `i ≤ n` is n-finite with `P = 0`.
- **(b) Quasi-isomorphism.** n-finiteness is invariant under quasi-isomorphism. A map from a
  bounded complex of free modules lifts along a quasi-isomorphism up to homotopy.
- **(c) Sums.** A finite direct sum of n-finite complexes is n-finite. A direct sum of an
  n-finite complex and any complex with `H_i = 0` for `i ≤ n` is n-finite.
- **(d) Extensions.** If `0 → K → L → M → 0` is exact and `K`, `M` are n-finite, then `L`
  is n-finite. Take witnesses `φ: P → K` and `ψ: Q → M`.
  1. Lift `ψ` to a graded map `λ: Q → L`. Then `dλ − λd = ατ` for a map `τ: Q → K` of
     degree `−1` with `dτ = −τd`, i.e. a chain map `Q⁻ → K`. Here `Q⁻_i = Q_{i+1}` and
     `d_{Q⁻} = −d_Q`.
  2. The cone `C` of `φ` has `H_i(C) = 0` for `i ≤ n`. `Q⁻` is a complex of free modules in
     degrees `−1..n−1`, so every chain map `Q⁻ → C` is null-homotopic, by building the
     homotopy degree by degree.
  3. By exactness of `Hom_{K(R)}(Q⁻, −)` on the triangle `P → K → C`, there are a chain map
     `ε: Q⁻ → P` and a degree-0 map `s: Q → K` with `τ − φε = ds − sd`.
  4. Put `P ⊕_ε Q` for the complex `P ⊕ Q` with differential `(p, q) ↦ (dp + εq, dq)`, and
     define `Φ(p, q) = αφp + λq − αsq`. A direct check shows `Φ` is a chain map compatible
     with `φ` and `ψ`.
  5. The five lemma on the long exact sequences gives `H_i(Φ)` bijective for `i < n`, and
     the four lemma gives surjectivity at `i = n`.
- **(e) Conclusion.** If `K` is n-finite and `K → Z` (the trivial `ZΓ`-module in degree 0)
  is bijective on `H_i` for `i < n` and surjective on `H_n`, then `Z` is n-finite. That is,
  `Z` has a partial resolution of length `n` by finitely generated free modules, so `Γ` is
  of type `FP_n`.

## Step 1. The complex

- `P_1` is the poset of BZ §5 and `X ⊆ |P_1|` is the Stein complex: chains `v_0 < ... < v_k`
  with `v_0 ⪯ v_k`.
- `X_m` is the full subcomplex on vertices of rank `≤ m`.
- `Γ` acts on `P_1` by order-preserving maps (BZ §6), so the stabilizer of a simplex fixes it
  pointwise, and each `C_k(X_m)` is a permutation module.

**Connectivity.** FFWZ Proposition 4.8(ii) (lines 906–918), for faithful actions: for every
`n` there is `M` such that `X_m` is `(n−1)`-connected for all `m ≥ M`. This comes from BZ
Proposition `prop:E_hi_conn` (descending links `E_m` are at least
`min(ν(m/2)−2, log_2(m/2)−2)`-connected), BZ Proposition `prop:cible` (`X` contractible) and
Bestvina--Brady Morse theory. It uses no hypothesis on `G ↷ S` beyond faithfulness. Fix such
an `m`.

## Step 2. The interval filtration

- For an elementary interval `I = [v, w]`, the length is `rank(w) − rank(v)`. Every chain in
  `[v, w]` is elementary (BZ §5, "and hence v_i ⪯ v_j"), so `|I| ⊆ X_m` when
  `rank(w) ≤ m`.
- Every simplex of `X_m` lies in `|[v_0, v_k]|`.
- Let `F_d` be the union of `|I|` over elementary intervals of length `≤ d` in `X_m`. These
  are `Γ`-subcomplexes, with `F_0` the vertex set and `F_{m−1} = X_m`.
- A simplex lies in `F_d \ F_{d−1}` iff its (min, max) interval `I` has length `d`. Its
  faces omitting the min or the max lie in shorter intervals, and the other faces stay in `I`.
- So `C_*(F_d)/C_*(F_{d−1}) ≅ ⊕_I C_*(|I|, ∂I)` over intervals of length `d`, with
  `∂I = |[v,w)| ∪ |(v,w]|`. Grouping by orbits gives
  `C_*(F_d)/C_*(F_{d−1}) ≅ ⊕_{[I]} Ind_{Γ_I}^{Γ} C_*(|I|, ∂I)`, with `Γ_I` the stabilizer of
  the pair `(v, w)`.

## Step 3. Local homology

By `stein-complex-elementary-intervals-are-grid-spheres`:
- if `I` is a grid interval with `e` colors in total, `C_*(|I|, ∂I)` has homology `Z_χ` in
  degree `e` alone, for a character `χ: Γ_I → {±1}`;
- if `I` is not a grid interval, `C_*(|I|, ∂I)` is acyclic.

Induction is exact, so by Step 0(b),(c) `C_*(F_d)/C_*(F_{d−1})` is quasi-isomorphic to
`⊕_{[I] grid} Ind_{Γ_I}^{Γ} Z_χ[e(I)]`.

## Step 4. Stabilizers of grid intervals

- Write `v = [h]` and `w = [(f_1 ⊕ ... ⊕ f_r) h]` with each `f_i` a full brick split in the
  color set `C_i`. By BZ Proposition `prop:stabs` (applied to the edge `v < w`), `Γ_I` is
  commensurate with `∏_i Stab_G(C_i)`, where `Stab_G(∅) = G`.
- Each `|C_i| ≤ e(I)`. Under `(HA_n)`, `Stab_G(C_i)` is of type `FP_{n−|C_i|}`, hence
  `FP_{n−e}`, and so is `G`. Finite products and commensurable groups preserve `FP_k`, so
  `Γ_I` is of type `FP_{n−e}` when `e ≤ n`.
- `N = ker χ` has index `≤ 2`, so it is also `FP_{n−e}`. `Z_χ` has a resolution by finitely
  generated free `Z[Γ_I/N]`-modules, and `Z[Γ_I/N] = Ind_N^{Γ_I} Z` is `FP_{n−e}` over
  `ZΓ_I`. So `Z_χ` is `FP_{n−e}` over `ZΓ_I` (dimension shifting), and so is
  `Ind_{Γ_I}^{Γ} Z_χ` over `ZΓ`.
- By Step 0(a), `Ind Z_χ[e]` is n-finite for every grid `I`. For `e > n` no hypothesis is
  needed.

## Step 5. Finitely many relevant orbits

- `Γ` is transitive on vertices of each rank (BZ proof of Proposition `prop:cocpt`), with
  stabilizer `𝒢(r) ≅ G ≀ Σ_r` (BZ Lemma `lem:vtx_stab`).
- Grid intervals with bottom `[id_r]` correspond to tuples `(C_1, ..., C_r)` of finite color
  sets. A twist `γ` at root `i` sends `C_i` to `γ C_i` (BZ Lemma `lem:stab_spectrum`), and
  permutations permute roots.
- So `Γ`-orbits of grid intervals with `e ≤ n` and bottom of rank `r` correspond to multisets
  of `G`-orbits of subsets of size `≤ n`. There are finitely many, because finitely many
  orbits on `S^n` give finitely many orbits on `S^k` for `k ≤ n` (embed `S^k` in `S^n` by
  repeating the last coordinate), hence on `k`-subsets.
- By Step 0(c), each quotient `C_*(F_d)/C_*(F_{d−1})` with `d ≥ 1` is n-finite. Grid
  intervals with `e > n` and non-grid intervals contribute nothing in degrees `≤ n`.

## Step 6. Assembly

- `C_*(F_0) = ⊕_{r ≤ m} Ind_{𝒢(r)}^{Γ} Z` is n-finite, since `G ≀ Σ_r` is `FP_n`.
- By Step 0(d) and induction on `d`, `C_*(X_m) = C_*(F_{m−1})` is n-finite.
- By Step 1, the augmentation `C_*(X_m) → Z` is bijective on `H_i` for `i < n`, and it is
  surjective on `H_n = 0`.
- By Step 0(e), `Γ` is of type `FP_n`. This proves `(HA_n) ⇒ FP_n`.

## Step 7. Homotopical finiteness

- Assume `(A_n)`. Then `(HA_n)` holds, so `Γ` is `FP_n`.
- For `n = 1`, `FP_1` is `F_1`.
- For `n ≥ 2`, `(A_n)` gives type `(A)`: `G` is finitely presented, point stabilizers are
  finitely generated, and there are finitely many orbits of pairs. So `Γ` is finitely
  presented by `twisted-brin-thompson-finite-presentation-criterion`.
- A finitely presented group of type `FP_n` is of type `F_n` (K. S. Brown, *Cohomology of
  Groups*, §VIII.7; not re-read at source). This proves `(A_n) ⇒ F_n`.

## Where the hypotheses enter

- The `k`-set stabilizer hypothesis `F_{n−k}` is used only for grid intervals that split one
  cube in `k` colors, in homological degree `≥ k`.
- The orbit hypothesis on `S^n` is used only to count grid intervals with `e ≤ n`.
- Both uses are sharp: FFWZ Cor 4.18 shows they are necessary.

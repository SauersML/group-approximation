---
rg: 2
id: lamplighter-cut-outs-act-freely-on-the-third-tree-proof
kind: route
title: "Proof: conjugates of a flat-fixator element by a T_a-elliptic normalizer lie in a compact set of G_a × G_bc, so discreteness makes the orbit finite; a power then fixes two non-commuting elements of N and their H_L-conjugates, hence centralizes H_L, contradicting C_L(γ) = 1; Serre gives H free; the normalizer of a uniform tree lattice is a finite extension of it (deck transformations), and a discrete cut-out projection makes P virtually free"
target: lamplighter-cut-outs-act-freely-on-the-third-tree
requires:
  - linear-dl-factor-kills-lamplighter-tree-cut-outs
---

Verification tier: proposed-established. Ingredients: Theorems B1, B2 of
`tree-cut-outs-force-locally-finite-by-abelian-quotients`; Theorem D of
`linear-dl-factor-kills-lamplighter-tree-cut-outs` (only: `N ≠ 1`, and
`H_L` is free); discreteness of `Λ`; Serre's theorem (free action without
inversions on a tree ⇒ free group); covering theory of graphs.

Notation as in the claim. `Ĥ = cl ρ(H)`, `M = Ĥ ∩ K`, `Ĥ/M ≅ P`,
`ρ(N) ⊆ M`, and `M` fixes `Y_b × Y_c` pointwise (B2; here `J = {b, c}`).
Fix a vertex `x` of `Y_b × Y_c`; every element of `ρ(N)` fixes `x`.

## Step 1: `N` is non-abelian

`N ≠ 1` (B3) and `N ⊴ H_L` with `H_L` free (Theorem D). `H_L` is not
cyclic, since `H_L/N ≅ L` is infinite locally finite and no quotient of
`Z` is. If `N = ⟨w⟩` were cyclic, `H_L` would normalize `⟨w⟩`; in a free
group the normalizer of `⟨w⟩ ≠ 1` is the maximal cyclic subgroup
containing `w`, so `H_L` would be cyclic. Hence `N` is a non-cyclic
subgroup of a free group, and there are `n_1, n_2 ∈ N` with
`[n_1, n_2] ≠ 1`; then `C_{H_L}(n_1) ∩ C_{H_L}(n_2) = 1`.

## Step 2: E1, the finite-orbit lemma

Let `g ∈ Λ` normalize `N` with `pr_a(g) y = y` for a vertex `y ∈ T_a`.
Fix `n ∈ N` and put `R = d(y, n y)` (distance in `T_a`). For `k ∈ Z`,
`n_k = g^k n g^{-k} ∈ N`, and
- `d(y, n_k y) = d(g^{-k} y, n g^{-k} y) = d(y, n y) = R`;
- `ρ(n_k)` fixes `x`, because `n_k ∈ N`.

So every `n_k` lies in `Λ ∩ (C_R × Stab(x))`, where
`C_R = {γ ∈ G_a : d(y, γ y) ≤ R}` is compact (`T_a` is locally finite)
and `Stab(x) ≤ G_b × G_c` is compact. `Λ` is discrete, so this set is
finite, and the orbit `{n_k}` is finite. Hence `g^d n g^{-d} = n` for some
`d ≥ 1`. For a finite `S ⊆ N` take `D` the least common multiple. ∎

## Step 3: E2, every nontrivial element of `H` is hyperbolic on `T_a`

Let `1 ≠ g ∈ H` with `pr_a(g)` fixing a vertex.

*Case `g ∈ H_L`.* By E1 some `g^D` centralizes `n_1, n_2`, so
`g^D ∈ C_{H_L}(n_1) ∩ C_{H_L}(n_2) = 1`. `H` is torsion-free, so `g = 1`.

*Case `g ∉ H_L`.* The image `γ` of `g` in `P` lies in `P ∖ L`, and so does
every power `γ^D` with `D ≥ 1` (because `P/L ≅ Z`). Let `h ∈ H_L` and
`S = {n_1, n_2, h n_1 h^{-1}, h n_2 h^{-1}} ⊆ N`. By E1 some `g^D`
centralizes `S`. Put `h' = g^D h g^{-D} ∈ H_L`. Then for `i = 1, 2`,

`h n_i h^{-1} = g^D (h n_i h^{-1}) g^{-D} = h' n_i h'^{-1}`,

so `h^{-1} h' ∈ C_{H_L}(n_1) ∩ C_{H_L}(n_2) = 1`, i.e. `g^D` commutes
with `h`. Mapping to `P`, the image `x_h ∈ L` of `h` lies in
`C_L(γ^D) = 1`. So `h ∈ N` for every `h ∈ H_L`, i.e. `L = 1`, a
contradiction.

*`C_L(γ) = 1` for `A ≀ Z`.* Write `γ = l t^e` with `e ≠ 0`,
`L = ⊕_{i ∈ Z} A`. For `u ∈ L`, `γ u γ^{-1} = l (t^e u t^{-e}) l^{-1}`
has support `supp(u) + e` (conjugation by `l ∈ L` preserves supports).
If `γ` centralizes `u`, then `supp(u)` is a finite set invariant under
translation by `e ≠ 0`, so it is empty and `u = 1`.

*Inversions.* If `g ∈ H` inverts an edge, then `g^2 ≠ 1` fixes its
endpoints, which the two cases exclude.

So `H` acts on `T_a` freely and without inversions. By Serre, `H` is
free; it is finitely generated since `H = φ(F)`. Vertex stabilizers of
`pr_a(H)` are trivial, so `pr_a(H)` is discrete, `pr_a` is injective on
`H`, and `pr_a(H)` acts cocompactly on its minimal subtree (a finitely
generated free group acting freely on a tree has a finite quotient core
graph). This is E2.1; E2.3 is the second case.

*E2.2.* `H` is free of rank at least 2 (`P` is not cyclic), and
`N ⊴ H` is nontrivial with `H/N ≅ P` infinite. A finitely generated
nontrivial normal subgroup of a free group has finite index
(Schreier/Karrass–Solitar), so `N` is infinitely generated; it is
non-abelian by Step 1. No condition on finite subgroups of `L` is used.
∎

## Step 4: E3.1, discrete cut-out projections kill

*`ρ(H)` discrete.* Then `Ĥ = ρ(H)` and `M = ρ(H) ∩ K` is finite; `ρ` is
injective on the torsion-free `H`, so `M = 1` and `P ≅ Ĥ ≅ H` is
torsion-free, contradicting `A ≠ 1`.

*`pr_c(H)` discrete* (the case `b` is symmetric). Let `π_c` be the
projection of `Ĥ` to `G_c`. A discrete subgroup is closed, so
`π_c(Ĥ) = pr_c ρ(H)` is discrete and finitely generated. `π_c(M)` is a
compact subgroup of a discrete group, hence finite, and normal in
`π_c(Ĥ)`. Vertex stabilizers of `π_c(Ĥ)` on `T_c` are finite, so
`π_c(Ĥ)` is virtually free. `Q = π_c(Ĥ)/π_c(M)` is a quotient of
`P = Ĥ/M`; the image of `L` in `Q` is locally finite and normal. A
locally finite subgroup of a virtually free group meets a free subgroup
of finite index trivially, so it is finite. So `Q` is finite-by-(a
quotient of `Z`), hence virtually cyclic, and so is `π_c(Ĥ)`. A
virtually cyclic group acting on a tree has bounded orbits or preserves
a line, so `T_c` is a compact or pair-of-ends factor of `Ĥ`. By B1 at
least two factors must be end-fixing horocyclic factors, and only `b`
is left. Contradiction.

Reducible hosts: for `Λ = Λ_a × Λ_{bc}` (discrete factors), `ρ(H) ≤ Λ_{bc}`
is discrete; for `Λ_{ab} × Λ_c`, `pr_c(H) ≤ Λ_c` is discrete; similarly
for `Λ_{ac} × Λ_b`. ∎

## Step 5: E3.2, the core criterion

*Lemma (normalizers of uniform tree lattices).* Let `Γ ≤ Aut(T)` be
discrete, torsion-free and cocompact. Then `N(Γ)` contains `Γ` with
finite index.

*Proof.* `Γ` has trivial vertex stabilizers (they are finite and `Γ` is
torsion-free) and no inversions (an inversion's square fixes a vertex),
so `p : T -> Γ\T` is a covering of a finite graph with deck group `Γ`.
Each `g ∈ N(Γ)` induces an automorphism `ḡ` of `Γ\T`, which gives a
homomorphism `N(Γ) -> Aut(Γ\T)` to a finite group. If `ḡ = 1`, then
`p ∘ g = p`, so `g` is a deck transformation. Pick a vertex `v`; then
`g v = γ v` for some `γ ∈ Γ`, and `γ^{-1} g` is a deck transformation
fixing `v`, hence trivial by unique path lifting. So the kernel is `Γ`.
∎

Now let `Γ' ≤ Σ` be normalized by `H`, with `pr_a(Γ')` a uniform lattice
of `G_a` and `pr_a` injective on `Λ`. `pr_a(Γ')` is torsion-free (`Λ` is),
so the Lemma gives `[pr_a(HΓ') : pr_a(Γ')] < ∞`, and hence
`[HΓ' : Γ'] < ∞`. Then `H ∩ Γ'` has finite index in `H`. But
`H ∩ Γ' ⊆ H ∩ Σ = N`, which has infinite index. Contradiction.

Both cases named in the claim supply such a `Γ'`:
- `Γ' = Σ_H`. It is normalized by `H`, and `pr_a(Σ_H)` is discrete since
  `ρ(Σ_H) ⊆ K` is relatively compact and `Λ` is discrete. If `Λ` is
  cocompact, `Σ = Λ ∩ (G_a × K)` is a uniform lattice in `G_a`. Indeed,
  `U_0 = G_a × K` is open in `G = G_a × G_b × G_c`, so the orbit
  `U_0 Λ ⊆ G/Λ` is open; the orbits of `U_0` partition `G/Λ` into open
  sets, so each is also closed, hence compact. This orbit is
  `U_0 / Σ`, so `Σ` is cocompact in `U_0`, and `pr_a(Σ)` is cocompact in
  `G_a` (`K` is compact). So if `[Σ : Σ_H] < ∞`, then `Σ_H` is a uniform
  lattice.
- `Γ' = Λ ∩ (G_a × U)` for a compact open `U ≤ K` normalized by `Ĥ`. It
  is normalized by `H`, since `hΓ'h^{-1} = Λ ∩ (G_a × ρ(h)Uρ(h)^{-1})`.
  It is uniform in `G_a` by the same argument as for `Σ`.

The equivalence "`[Σ : Σ_H] = ∞` iff `K` has no `Ĥ`-normalized open
subgroup" holds when `ρ(Σ)` is dense in `K`. We only use the direction
proved above. ∎

## Step 6: calibration (abstract hosts)

`F_2 = ⟨a, t⟩`, `π : F_2 ↠ P = Z/2 ≀ Z`, `ψ : F_2 ↪ M` into a profinite
group (residual finiteness). `M` acts faithfully on a rooted locally
finite tree `R`. Hang a copy of `R` at every vertex of each factor of
`DL(2,2) ⊆ T_3 × T_3`. `P × M` acts factorwise (`P` on the DL factors,
`M` on every hair), the image is closed, and `ρ = (π, ψ)` is injective.
For `K = Stab(x_b, x_c)` with `(x_b, x_c) ∈ DL(2,2)`,
`(P × M) ∩ K = M` because `P` acts freely on `DL(2,2)`, so
`H ∩ ρ^{-1}(K) = ker π`. Every conclusion of E2 holds here (`F_2` is free
and acts freely on its Cayley tree, taken as `T_a`), and
`Σ = H ∩ ρ^{-1}(K) = ker π` is not finitely generated. So E1–E3 are
consistent with the abstract shape, and a kill has to use the lattice
property of `Λ`, as E3.2 does.

---
rg: 2
id: linear-dl-factor-kills-lamplighter-tree-cut-outs-proof
kind: route
title: "Proof: the pointwise fixator of an apartment in PGL_2(k) is the compact split torus T(O); the nontrivial torsion-free flat fixator N lies in it, so its infinite-order elements are regular with centralizer T; normality of N in H forces H into N(T) = T x| Z/2; in three-tree lattices, preimages of finite lamp groups are relatively compact in the cut-out factors, hence act freely on the third tree, and the Schreier index formula makes a finitely generated N impossible"
target: linear-dl-factor-kills-lamplighter-tree-cut-outs
requires:
  - tree-cut-outs-force-locally-finite-by-abelian-quotients
---

Verification tier: proposed-established. Ingredients: Theorem B of
`tree-cut-outs-force-locally-finite-by-abelian-quotients` (items B2, B3 and
the identification `Ĥ/M ≅ P`), the lattice description of the Bruhat–Tits
tree of `PGL_2(k)`, Serre's theorem that a group acting freely on a tree
is free, and the Schreier index formula.

## Step 0: what Theorem B gives

`τ = ρ(τ₀)`, `Ĥ` the closure of `ρ(H)`, `M = Ĥ ∩ K` compact open normal
in `Ĥ` with `Ĥ/M ≅ P`, and `ρ(N) = ρ(H) ∩ K ⊆ M`.
- (B2) For every `j ∈ J`, `pr_j M` fixes the axis `ℓ_j` of `τ_j` pointwise.
- (B3) If `H` is torsion-free and `ρ` is injective on `H`, then `N ≠ 1`.
  (The proof of B3 uses only these two facts: a finite `M` would meet
  `ρ(H) ≅ H` in a finite, hence trivial, dense subgroup of the open `M`, so
  `M = 1` and `P ≅ H` torsion-free, contradicting `L ≠ 1`.)

## Step 1: apartment fixators in PGL_2(k)

Let `k` be a non-archimedean local field with ring `O`, uniformizer `π`.
Vertices of the tree `T_k` are homothety classes of `O`-lattices in `k^2`;
geodesic lines are exactly the apartments `A_{e,f}` for bases `(e, f)` of
`k^2` up to scaling each vector, with vertices `[O e ⊕ π^n O f]`, `n ∈ Z`.
(Every geodesic line in `T_k` corresponds to its pair of ends, i.e. a pair
of distinct points of `P^1(k)`, i.e. two lines `ke`, `kf`.)

**Lemma 1.** The pointwise fixator of `A_{e,f}` in `PGL_2(k)` is `T(O)`,
the image of the matrices `diag(u, v)`, `u, v ∈ O^×`, in the basis
`(e, f)`. It lies in the split torus `T` = image of `diag(k^×, k^×)`.

*Proof.* Work in the basis `(e, f)`. Suppose `g ∈ PGL_2(k)` fixes every
`[L_n]`, `L_n = O e ⊕ π^n O f`. Since `g` fixes `[L_0]`, `g` lifts to
`g' ∈ GL_2(O)`; then `g' L_n = c_n L_n` with `c_n ∈ k^×`, and comparing
covolumes (`det g' ∈ O^×`) gives `c_n ∈ O^×`, i.e. `g' L_n = L_n`. Write
`g' = [[a, b], [c, d]]`, so `g' e = a e + c f` and `g'(π^n f) =
π^n(b e + d f)`. From `g' e ∈ L_n` for all `n ≥ 0`, `c ∈ ∩_n π^n O = 0`.
From `g'(π^n f) ∈ L_n` for all `n ≤ 0`, `π^n b ∈ O`, so `b = 0`. Then
`a, d ∈ O^×` as `g' ∈ GL_2(O)`. The converse is clear. ∎

**Lemma 2.** Let `x ∈ T` have infinite order. Then the centralizer of `x`
in `PGL_2(k)` is `T`, and the normalizer `N(T)` is `T ⋊ ⟨w⟩` with
`w = [[0, 1], [1, 0]]`, so `[N(T) : T] = 2` and `T ≅ k^×` is abelian.

*Proof.* `x = [diag(α, 1)]` with `α ≠ 1`, and `α ≠ -1` since `x` has
infinite order (`diag(-1,1)` has order 2 in `PGL_2`). If `y x y^{-1} = x`
in `PGL_2`, lifts satisfy `y' diag(α,1) y'^{-1} = λ diag(α, 1)`. Comparing
eigenvalues, `{α, 1} = {λα, λ}`, so `λ = 1` or `λ = α = 1/α`; the second
means `α^2 = 1`, excluded. So `y'` commutes with `diag(α, 1)`, whose
eigenvalues are distinct, so `y'` is diagonal: `y ∈ T`. For the normalizer,
`y T y^{-1} = T` means `y'` permutes the two eigenlines `ke`, `kf`, so
`y' ∈ diag · {1, w}`. ∎

## Step 2: Theorem C

Assume `H` torsion-free, `ρ_j(H) ≤ PGL_2(k)` acting on `T_j = T_k` in the
standard way, `ρ_j` injective on `H`, and `j ∈ J`.

1. `τ_j = ρ_j(τ₀)` is hyperbolic, with axis `ℓ_j` a geodesic line, hence
   an apartment `A_{e,f}` (Step 1). Let `T` be its torus.
2. By B2, `ρ_j(N) ⊆ pr_j M` fixes `ℓ_j` pointwise, so by Lemma 1,
   `ρ_j(N) ⊆ T(O) ⊆ T`.
3. By B3, `N ≠ 1`. Pick `1 ≠ n ∈ N`. Since `H` is torsion-free, `n` has
   infinite order, and since `ρ_j` is injective on `H`, so has
   `x = ρ_j(n) ∈ T`.
4. For `h ∈ H`, `h n h^{-1} ∈ N` (as `N ⊴ H`), so
   `y = ρ_j(h n h^{-1}) ∈ T` has infinite order. By Lemma 2,
   `C(y) = T`. But also `C(y) = ρ_j(h) C(x) ρ_j(h)^{-1} = ρ_j(h) T
   ρ_j(h)^{-1}`. So `ρ_j(h) ∈ N(T)`.
5. So `ρ_j(H) ≤ N(T)`, and `ρ_j(H) ∩ T` is abelian of index at most 2 in
   `ρ_j(H)`. By injectivity, `H` is virtually abelian, hence so is `P`.
6. Contradiction. `P` is finitely generated and virtually abelian, so it
   has a finite-index free abelian subgroup `A`; `L ∩ A` is torsion in a
   torsion-free group, so trivial, so `L` embeds in the finite `P/A`.
   Then `t` acts on the finite `L` with some power `t^d` (`d ≠ 0`) acting
   trivially, so `C_L(t^d) = L ≠ 1`, contrary to the hypothesis. ∎

**Corollary 1** (arithmetic hosts). If `D` is a quaternion algebra over a
global field `F`, `S` a finite set of places at which `D` splits, and `Λ`
a torsion-free `S`-arithmetic subgroup of `D^×/F^×`, then each
`ρ_v : Λ -> PGL_2(F_v)`, `v ∈ S`, is the restriction of the inclusion `D^×/F^× ↪ (D ⊗ F_v)^×/F_v^×`, so is
injective, and acts on the Bruhat–Tits tree in the standard way. Any tree
cut-out of `Λ` into a subproduct of these factors (with arbitrary closed
`G_v ⊇ ρ_v(Λ)` in `Aut(T_v)`) has `J ≠ ∅` by B1 and satisfies Theorem C at
every `j ∈ J`. Only `ρ_j(H) ≤ PGL_2(k)` was used, never the size of `G_j`.

**Corollary 2** (mixed hosts) is Theorem C verbatim: other factors enter
only through Theorem B.

## Step 3: Theorem D (three trees, no linearity)

Now `Λ` is a torsion-free lattice (discrete suffices) in
`G_a × G_b × G_c` with `G_x ≤ Aut(T_x)` closed, and the cut-out is
`ρ = pr_{bc}`, injective on `Λ`.

**D1.** Let `Q ≤ L` be finite and `E` its preimage in `H`. The preimage
`C_Q` of `Q` under `Ĥ -> Ĥ/M ≅ P` is a finite union of cosets of the
compact `M`, so compact, and `ρ(E) ⊆ C_Q`. So
`E ≤ Λ ∩ (G_a × C_Q)`.
- `pr_a` is injective on `Λ ∩ (G_a × C_Q)`: its kernel `Λ ∩ (1 × C_Q)` is
  discrete in a compact group, so finite, so trivial.
- `pr_a(Λ ∩ (G_a × C_Q))` is discrete: a sequence `λ_n` with
  `pr_a(λ_n) -> 1` has, after passing to a subsequence,
  `pr_{bc}(λ_n)` convergent in `C_Q`, so `λ_n^{-1} λ_{n+1} -> 1` in `G`,
  hence eventually `λ_n = λ_{n+1}`, and so `pr_a λ_n = 1` eventually.
- A torsion-free discrete subgroup of `Aut(T_a)` acts freely: vertex
  stabilizers are compact and discrete, hence finite, hence trivial; an
  inversion `g` has `g^2` fixing an edge, so `g^2 = 1`, so `g = 1`.
So `E` acts freely on `T_a` and is free (Serre, *Trees*, I.3.3).

**D2.** Since `L` is locally finite, every finite subset of `H_L` lies in
the preimage of a finite subgroup of `L`. So every `1 ≠ g ∈ H_L` acts
without fixed points or inversions on `T_a` (D1), `H_L` acts freely and is
free. As `H/H_L ≅ P/L ≅ Z` is free, `H = H_L ⋊ ⟨τ₀'⟩` for any lift `τ₀'`
of `t`.

**D3.** `N ≤ H_L` is free and normal in `H`, and `N ≠ 1` (B3; `ρ` is
injective on `H`). Suppose `N` has finite rank `r_N ≥ 1`. For each finite
`Q ≤ L`, the free group `E ⊇ N` has `[E : N] = |Q|`, so `E` is finitely
generated and `r_N - 1 = |Q| (rk E - 1)` (Schreier). As `L` is infinite
(Step 2.6: a finite `L ≠ 1` violates `C_L(t^d) = 1`) and locally finite, `|Q|`
is unbounded, so `r_N = 1`: `N ≅ Z`. Then `rk E = 1` for every `Q`, so
`E ≅ Z` and `Q ≅ E/N` is cyclic. So if `L` has a non-cyclic finite
subgroup (e.g. `(Z/2)^2 ≤ ⊕ Z/2`), `N` is infinitely generated. An abelian
free group is cyclic, so `N` is not abelian either. ∎

## Remarks

- The argument of Step 2 needs the factor `j` to be in `J`: for a factor
  where `τ₀` is elliptic, `ρ_j(N)` need not fix a line.
- Step 2 extends verbatim to any factor in which the pointwise fixator of
  the axis of a hyperbolic element lies in an abelian subgroup `T` that is
  the centralizer of each of its infinite-order elements, with
  `[N(T) : T] < ∞`. For instance `ρ_j(H) ≤ SL_2(k)` acting through
  `PGL_2(k)` is covered: the map to `PGL_2(k)` has kernel `±1`, so stays
  injective on the torsion-free `H`.
- What remains open is the case where every factor of `J` is non-linear
  on `H`; D then says exactly what the host must supply.

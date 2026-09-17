---
rg: 2
id: rsh-multiplicity-count-sharp-rigidity-threshold-proof
kind: route
title: Perturb each RSH block off the codimension k²−1 multiplicity locus by relative general position, bound trace atoms by extreme traces, compute the threshold obstruction on the maximal torus, and push Euler classes into larger blocks by a block-diagonal equivariant map
target: rsh-multiplicity-count-sharp-rigidity-threshold
requires:
  - bauer-strict-comparison-unit-divides-iff-atomless-element
  - bauer-strict-comparison-pure-iff-divisible-unit
  - toms-winter-bauer-tlfnd-iff-tracially-divisible-unit
---

Complete proof. Theorems A, B and D (including D.5) use only standard topology and C*-algebra facts. Corollary C
imports the three required claims.

## 0. Conventions

- **RSH algebras.** An RSH algebra is built by iterated pullbacks. `B^{(0)} = C(X_0, M_{n_0})`
  with `∂X_0 = ∅`, and
  `B^{(j)} = {(b, f) ∈ B^{(j−1)} ⊕ C(X_j, M_{n_j}) : f|_{∂X_j} = ψ_j(b)}`,
  where `∂X_j ⊆ X_j` is closed and `ψ_j : B^{(j−1)} → C(∂X_j, M_{n_j})` is a unital
  `*`-homomorphism. `B = B^{(J)}`. An element is written `h = (h_0, …, h_J)` with
  `h_j ∈ C(X_j, M_{n_j})`.
- **Irreducible representations (standard).** The restriction `B^{(j)} → B^{(j−1)}` is
  surjective, with kernel `C_0(X_j \ ∂X_j, M_{n_j})`. By induction, every irreducible
  representation of `B^{(j)}` is equivalent to `ev_x : h ↦ h_i(x)` for some `i ≤ j` and some
  `x ∈ X_i \ ∂X_i`, and it has dimension `n_i`. Every finite-dimensional representation of
  `B^{(j)}` is a direct sum of these.
- **Multiplicity loci.** `mult_λ(H)` is the multiplicity of `λ` as an eigenvalue of
  `H ∈ Herm_n`. `L_k = L_k^{(n)} = {H : ∃λ, mult_λ(H) ≥ k}`.
- **Property `(M_ε)`.** For `ε ∈ (0,1]`, a self-adjoint `h ∈ B^{(j)}` has `(M_ε)` if
  `mult_λ(π(h)) < ε · dim π` for every irreducible representation `π` and every `λ`. By the
  description of irreducibles, this says exactly that `h_i(x) ∉ L_{⌈ε n_i⌉}` for all `i ≤ j`
  and `x ∈ X_i \ ∂X_i`.
  - It holds at every `x ∈ X_i`: at `x ∈ ∂X_i`, `h_i(x) = ψ_i(h)(x)` is unitarily a direct sum
    `⊕_t π_t(h)` of irreducibles with `Σ dim π_t = n_i`. So
    `mult_λ = Σ_t mult_λ(π_t(h)) < ε Σ_t dim π_t = ε n_i`.
  - More generally `(M_ε)` passes to every finite-dimensional representation (∗).

## 1. The multiplicity locus

**Lemma 1.** `L_k ⊂ Herm_n ≅ R^{n²}` is closed and semialgebraic, and it is a finite union of
smooth submanifolds, each of dimension `≤ n² − k² + 1`.

*Proof.*
- **Closed.** If `H_m → H` with `mult_{λ_m}(H_m) ≥ k`, the `λ_m` are bounded by `sup ‖H_m‖`.
  Pass to `λ_m → λ`. Then `rank(H_m − λ_m) ≤ n − k` and lower semicontinuity of rank give
  `rank(H − λ) ≤ n − k`.
- **Semialgebraic.** `L_k` is the projection to `Herm_n` of the algebraic set
  `{(H, λ) : all (n−k+1)-minors of H − λ vanish}`.
- **Dimension.** Consider the smooth semialgebraic map
  `Φ : Gr_k(C^n) × R × Herm_{n−k}-bundle → Herm_n`, `(V, λ, h') ↦ λ P_V + h'` with `h'` acting on
  `V^⊥`. It is onto `L_k`: take `V` inside the `λ`-eigenspace. Its source has dimension
  `2k(n−k) + 1 + (n−k)² = n² − k² + 1`.
- The semialgebraic dimension of an image is at most that of the source, and a semialgebraic set
  of dimension `D` is a finite union of Nash submanifolds of dimension `≤ D` (Bochnak–Coste–Roy,
  *Real Algebraic Geometry*, Thm 2.8.8 and Prop. 9.1.8). ∎

## 2. Relative general position

**Lemma 2.** Suppose:
- `X` is compact metrizable with covering dimension `≤ d`, and `C ⊆ X` is closed;
- `L ⊂ R^N` is closed and a finite union of `C¹` submanifolds `M_1, …, M_r`, each of dimension
  `≤ N − d − 1`;
- `f : X → R^N` is continuous with `f(C) ∩ L = ∅`, and `η > 0`.

Then there is a continuous `g : X → R^N` with `g|_C = f|_C`, `‖g − f‖_∞ < η` and
`g(X) ∩ L = ∅`.

*Proof.*
1. **Margin.** If `C ≠ ∅`, `f(C)` is compact and disjoint from the closed set `L`. So
   `dist(f(C), L) = 3δ_0 > 0`. If `C = ∅`, put `δ_0 = 1`. Let
   `W = {x : dist(f(x), L) > 2δ_0}`, an open set containing `C`. Put `η' = min(η, δ_0)`.
2. **Nerve factorization.**
   - Let `ω` be a modulus of uniform continuity of `f`, and pick `δ` with `ω(δ) < η'/2`.
   - Since `dim X ≤ d`, there is a finite open cover `𝒰` of mesh `< δ` and order `≤ d + 1`.
     Take a subordinate partition of unity `(φ_U)`, points `x_U ∈ U`, and the nerve `N(𝒰)`,
     a simplicial complex of dimension `≤ d`.
   - Let `p : X → |N(𝒰)|`, `p(x) = (φ_U(x))_U`, and let `g_0 : |N(𝒰)| → R^N` be affine on
     simplices with `g_0(U) = f(x_U)`.
   - Then `g_0(p(x)) = Σ_U φ_U(x) f(x_U)` is a convex combination of values `f(x_U)` with
     `x ∈ U`, `diam U < δ`. So `‖g_0 ∘ p − f‖_∞ ≤ ω(δ) < η'/2`.
3. **Translation.**
   - For a simplex `σ` of dimension `≤ d` and a submanifold `M_i`, the map
     `M_i × σ → R^N`, `(m, s) ↦ m − g_0(s)`, is locally Lipschitz on a σ-compact set of
     dimension `≤ N − 1`. So its image `Z_{σ,i}` is Lebesgue null.
   - Choose `v ∉ ∪_{σ,i} Z_{σ,i}` with `|v| < η'/2`. Then `(g_0 + v)(|N(𝒰)|) ∩ L = ∅`, so
     `g_1 = (g_0 + v) ∘ p` misses `L` and `‖g_1 − f‖ < η'`.
4. **Gluing.**
   - Let `χ : X → [0,1]` be continuous, `χ = 1` on `C` and `χ = 0` off `W` (Urysohn; if
     `C = ∅` take `χ = 0`). Put `g = χ f + (1 − χ) g_1`.
   - Then `g|_C = f|_C` and `‖g − f‖ ≤ ‖g_1 − f‖ < η' ≤ η`.
   - For `x ∉ W`, `g(x) = g_1(x) ∉ L`.
   - For `x ∈ W`, `|g(x) − f(x)| < δ_0` and `dist(f(x), L) > 2δ_0`, so `g(x) ∉ L`. ∎

## 3. Proof of Theorem A

Put `k_j = ⌈ε n_j⌉`, assume `d_j ≤ k_j² − 2` for all `j`, and prove by induction on `j` that the
elements of `B^{(j)}_sa` with `(M_ε)` are dense.
- `(M_ε)` for `h_j` at interior points is exactly `h_j(x) ∉ L_{k_j}`, since an integer
  `m < ε n_j` iff `m ≤ k_j − 1`.
- `d_j ≤ k_j² − 2` forces `k_j ≥ 2`. Lemma 1 gives strata of dimension
  `≤ n_j² − k_j² + 1 ≤ n_j² − d_j − 1`, which is the hypothesis of Lemma 2 with
  `N = n_j²`, `d = d_j`.

**Base.** `j = 0`: apply Lemma 2 to `f = h_0` with `C = ∅`. Convex combinations and translations
by Hermitian `v` stay in `Herm_{n_0}`. Work in `Herm_n` throughout.

**Step.** Let `h = (b, f) ∈ B^{(j)}_sa` and `η > 0`.
1. **Lower stages.** By induction pick `b' ∈ B^{(j−1)}_sa` with `(M_ε)` and `‖b' − b‖ < η`. By
   (∗) applied to the representations `ev_x ∘ ψ_j`, `x ∈ ∂X_j`, the map `ψ_j(b')` misses
   `L_{k_j}` on `∂X_j`.
2. **Extension.** `e = ψ_j(b' − b) ∈ C(∂X_j, Herm_{n_j})` has `‖e‖ < η`.
   - Extend `e` coordinatewise by Tietze, and compose with the nearest-point retraction (for the
     Hilbert–Schmidt norm) onto the closed convex set `{H : ‖H‖ ≤ ‖e‖}`. That set is closed and
     convex, so the retraction is continuous and fixes it pointwise.
   - The result `ê` extends `e` with `‖ê‖ ≤ ‖e‖`. Put `f'' = f + ê`. Then
     `f''|_{∂X_j} = ψ_j(b')` and `‖f'' − f‖ < η`.
3. **Perturbation.** Lemma 2 with `X = X_j`, `C = ∂X_j`, `L = L_{k_j}` gives `g` with
   `g|_{∂X_j} = ψ_j(b')`, `‖g − f''‖ < η`, and `g` missing `L_{k_j}`.
4. **Conclusion.** `h' = (b', g) ∈ B^{(j)}_sa` has `(M_ε)` and `‖h' − h‖ < 2η`. ∎

## 4. Proof of Theorem B

- **Setup.** Let `B ⊆ A` be unital RSH with `ε := ε_B = max_j √(d_j+2)/n_j ≤ 1`. Then
  `ε n_j ≥ √(d_j+2)`, so `k_j = ⌈ε n_j⌉` satisfies `k_j² ≥ d_j + 2`. Theorem A gives a
  self-adjoint `h ∈ B` with `(M_ε)`. Put `ρ' = max_j (k_j − 1)/n_j < ε`.
- **Uniform window.**
  - Fix `λ ∈ R` and a block `j`. For `δ > 0` let `c_δ(x)` count the eigenvalues of `h_j(x)` in
    `[λ − δ, λ + δ]`, with multiplicity.
  - By continuity of the ordered eigenvalues, `F_m = {x ∈ X_j : c_{1/m}(x) ≥ k_j}` is closed. The
    `F_m` decrease in `m`, and `c_{1/m}(x) ↓ mult_λ(h_j(x)) ≤ k_j − 1`, so `∩_m F_m = ∅`.
  - By compactness some `F_m` is empty. Taking the largest such `m` over the finitely many blocks
    gives `δ > 0` with `c_δ ≤ k_j − 1` on every `X_j`.
- **Test function.** Let `u ∈ C(R)`, `0 ≤ u ≤ 1`, `u(λ) = 1`, `supp u ⊆ [λ − δ, λ + δ]`. For
  `x ∈ X_j`, `tr_{n_j}(u(h_j(x))) ≤ c_δ(x)/n_j ≤ ρ'`.
- **Extreme traces.**
  - Let `σ` be an extreme tracial state of `B`. Then `π_σ(B)''` is a finite factor. `B` is
    `n`-subhomogeneous with `n = max n_j`, so `π_σ(B)''` satisfies the standard polynomial
    identity of degree `2n`, and a II_1 factor does not.
  - So `π_σ(B)'' ≅ M_m`, `π_σ` is a multiple of an irreducible `π`, and `σ = tr ∘ π`. By §0,
    `π = ev_x` for an interior point, so `σ(u(h)) ≤ ρ'`.
- **All traces.** `σ ↦ σ(u(h))` is continuous and affine on the compact convex set `T(B)`. By
  Krein–Milman `T(B)` is the closed convex hull of its extreme points, so `σ(u(h)) ≤ ρ'` for all
  `σ ∈ T(B)`.
- **Atoms.** For `τ ∈ T(A)`, `τ|_B ∈ T(B)`, so
  `μ_{h,τ}({λ}) ≤ ∫ u dμ_{h,τ} = τ(u(h)) ≤ ρ' < ε`.
- **Rigidity consequence.** If `A` is `ε_0`-rigid over `K ≠ ∅`, applying this to `h` gives
  `ε_0 ≤ ρ' < ε_B`. So `ε_0 n_j < √(d_j + 2)` for some `j`. If `ε_B > 1` the inequality holds
  since `ε_0 ≤ 1`. ∎

## 5. Proof of Corollary C

- **Unit divides.** Scale the element `h` of Theorem B to a contraction, which does not change
  atom masses. For every `ε`, `A` then has a self-adjoint contraction whose atoms, at every trace
  and in particular at every extreme trace, are `< ε`. This is (ii) of
  `bauer-strict-comparison-unit-divides-iff-atomless-element`, so the unit is tracially
  `N`-divisible for every `N`.
- **Purity.** `bauer-strict-comparison-pure-iff-divisible-unit` gives purity.
- **ASH case.**
  - If `A = lim A_m` with `A_m` RSH over finite-dimensional spaces, the image of `A_m` in `A` is a
    quotient of `A_m`. A quotient of an RSH algebra is RSH over closed subspaces (restrict each
    `X_j` to a closed subset), so dimensions do not increase and the ratios stay small.
  - Such an `A` is nuclear with (tracially) locally finite nuclear dimension. Item (e) ⟹ (a) of
    `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit` gives `A ≅ A ⊗ Z`. ∎

## 6. Proof of Theorem D

Let `G = PU(n)` act on `Herm_n` by conjugation. `L_k` is invariant.

**D.1 (the fibre).** `L_k` is invariant under `H ↦ H + t·1`, so `U_k ≃ U_k ∩ Herm^0_n`. Use
Alexander duality in `S^{n²} = Herm_n ∪ {∞}` with `K = L_k ∪ {∞}` (compact):
`H̃_q(U_k) ≅ Ȟ^{n² − q − 1}(K) = H_c^{n² − q − 1}(L_k)`.
- **Vanishing below.** `dim L_k = D := n² − k² + 1`, so `H̃_q(U_k) = 0` for `n² − q − 1 > D`,
  i.e. `q ≤ k² − 3`.
- **Simply connected.** `U_k` is the complement of a closed set of codimension `≥ 3` in `R^{n²}`,
  hence simply connected. Hurewicz gives `(k²−3)`-connectedness and
  `π_{k²−2}(U_k) ≅ H_c^D(L_k)`.
- **Top stratum.** Let `L^o ⊂ L_k` be the set of `H` with exactly one eigenvalue of multiplicity
  exactly `k` and no other eigenvalue of multiplicity `≥ k`. On
  `{(V, λ, h') : λ ∉ spec h', h' has no eigenvalue of multiplicity ≥ k}` the map `Φ` of Lemma 1 is
  a homeomorphism onto `L^o`: the `λ`-eigenprojection is continuous under a spectral gap.
- **Singular part.** `L_k \ L^o` consists of matrices with an eigenvalue of multiplicity `≥ k+1`
  (dimension `≤ n² − (k+1)² + 1 = D − 2k − 1`) or with two eigenvalues of multiplicity `≥ k`
  (dimension `≤ D − (k² − 1) ≤ D − 3`).
  - The exact sequence `H_c^{D−1}(L_k \ L^o) → H_c^D(L^o) → H_c^D(L_k) → H_c^D(L_k \ L^o)` has
    both outer terms zero, so `H_c^D(L_k) ≅ H_c^D(L^o)`.
- **Components.** The parameter set fibres over the simply connected `Gr_k(C^n)`. Its fibre over
  `V` is an open subset of `R × Herm(V^⊥)`, with components indexed by
  `i = #{eigenvalues of h' below λ} ∈ {0, …, n−k}`. Each is connected.
  - Before the multiplicity restriction on `h'`, component `i` is
    `{(λ, h') : λ_i(h') < λ < λ_{i+1}(h')}` (with `λ_0 = −∞`, `λ_{n−k+1} = +∞`). That is a bundle of
    open intervals over the contractible `Herm(V^⊥)`, so it is connected.
  - Removing the `h'` with an eigenvalue of multiplicity `≥ k` removes a closed set of
    codimension `≥ 3` and keeps it connected.
  - So `L^o` has `n − k + 1` components, each an orientable `D`-manifold: an open subset of a
    vector bundle with connected structure group over a simply connected base.
  - Hence `H_c^D(L^o) ≅ Z^{n−k+1}`. Component `i` is the locus `λ_{i+1} = … = λ_{i+k}` of the
    ordered eigenvalues.

**D.2 (complete obstruction).**
- **Associated bundle.** `E_k = EG ×_G U_k → BG` is a fibre bundle with `(k²−3)`-connected simple
  fibre over the simply connected `BG`. So the coefficient system `π_{k²−2}(U_k)` is untwisted.
- **Obstruction.** Its primary obstruction `θ_k ∈ H^{k²−1}(BG; Z^{n−k+1})` is natural under
  pullback. For a CW complex of dimension `≤ k² − 1`, it vanishes iff a section exists
  (Steenrod, *Topology of Fibre Bundles*, §§34–37; Whitehead, *Elements of Homotopy Theory*,
  VI.6). The obstruction is primary and the dimension is at most one more than the first
  nonvanishing homotopy degree of the fibre.
- **Translation.** Self-adjoint elements of `A_P` missing `L_k` are exactly the sections of
  `P ×_G U_k = f_P^* E_k`, where `f_P : X → BG` classifies `P`. So they exist iff
  `f_P^* θ_k = 0`.

**D.3 (torsion).**
- **Torus.** For the maximal torus `T ⊂ G` (diagonal unitaries mod scalars), the pullback of
  `E_k` to `BT` is `ET ×_T U_k`. It has the section given by the `T`-fixed point
  `diag(1, 2, …, n) ∈ U_k`, so `θ_k|_{BT} = 0` by naturality.
- **Rational injectivity.** `H^*(BG; Q) → H^*(BT; Q)` is injective (Borel). `H^{k²−1}(BG; Z)` is
  finitely generated, so `θ_k` is torsion.
- **Primes not dividing `n`.** The fibration `K(Z/n, 1) → BSU(n) → BPU(n)` has fibre with
  vanishing reduced `Z_{(p)}`-cohomology. The Serre spectral sequence gives
  `H^*(BPU(n); Z_{(p)}) ≅ H^*(BSU(n); Z_{(p)})`, which is torsion free. So the `p`-primary part of
  `θ_k` vanishes.
- **Untwisted bundles.** `BU(n) → BG` pulls `θ_k` back to a torsion class in the torsion-free
  `H^*(BU(n); Z)`, i.e. to `0`. If `P` is the frame bundle of `End(E)`, `f_P` factors through
  `BU(n)`, so `f_P^* θ_k = 0` and D.2 gives the element.

**D.4 (sharpness).**
- **Moore space.** `M = S² ∪_2 e³` has `H²(M; Z) = 0`, `H³(M; Z) = Z/2 = H²(M; Z/2)`, and
  `β : H²(M; Z/2) → H³(M; Z)` is injective, since `H²(M; Z) = 0` precedes it in the Bockstein
  sequence.
  - `w_2 : BSO(3) → K(Z/2, 2)` is an isomorphism on `π_2`, `π_3 = 0` on both sides, and
    `π_4(K(Z/2,2)) = 0`. So it is 4-connected, and every class in `H²(M; Z/2)` is `w_2` of some
    `SO(3) = PU(2)` bundle `P`.
  - The adjoint bundle `ad P` is the oriented rank-3 bundle itself, with Euler class
    `e = β w_2 ≠ 0` (for odd rank `2m+1`, `e = β w_{2m}`). A nowhere-scalar self-adjoint section
    `h` gives the nowhere-zero section `h − tr(h)/2` of `ad P ⊗ R`, a contradiction. Here
    `k = n = 2`, `d = 3 = k² − 1`, and `θ_2` is the universal `e`, of order 2.
  - Theorem A's hypothesis `d ≤ k² − 2 = 2` fails by exactly one.
- **Pauli tower.** `pauli-tower-sections-are-somewhere-scalar` with `n = 0`, `m = r`: `B_{0,r}` is
  a flat `M_{2^r}`-bundle over `Π_{j ≤ 2r} RP^{2^{j−1}}`, of dimension `4^r − 1 = N² − 1`,
  `N = 2^r`, with every section somewhere scalar. It is rigid at level 1 with `k = N`, on the
  threshold, and its certificate is a 2-primary torsion class, as D.3 requires.
- **Instanton.** Let `E → S⁴` be the `SU(2)` bundle with `c_2 = 1`. If `h ∈ End(E)_sa` is nowhere
  scalar, its two eigenlines are distinct everywhere and span line bundles `L_±` with
  `E = L_+ ⊕ L_−`. Then `c_2(E) = c_1(L_+) c_1(L_−) ∈ H⁴`, which is a product of classes in
  `H²(S⁴) = 0`, a contradiction. So `End(E)`, with trivial Dixmier–Douady class, is rigid at
  level 1 at `d = 4 = k² > k² − 1`, and D.3 fails above the threshold. ∎

**D.5 (sharpness at every level `1/t`).** Let `2 ≤ k`, `t ≥ 1`, `n = kt`, and let `P` be a
principal `PU(k)`-bundle over a CW complex `X` with `dim X ≤ k² − 1`, whose traceless adjoint
bundle `ad_0 P` (oriented, real rank `k² − 1`) has Euler class `e(ad_0 P) ≠ 0`. Put
`Q = P ⊗ 1_t`, the `PU(n)`-bundle induced by `[u] ↦ [u ⊗ 1_t]`, so `A_Q = A_P ⊗ M_t`. Then
every self-adjoint `h ∈ A_P ⊗ M_t` has a point `x` where `h(x)` has an eigenvalue of multiplicity
`≥ k`. So `A_P ⊗ M_t` is `1/t`-rigid over its point traces.

*Proof.*
- **The fibre map.** Normalize `ĥ = (h − tr_k(h)1)/‖h − tr_k(h)1‖` on `U_k(k) = Herm_k \ R·1`, so
  `spec ĥ ⊂ [−1, 1]`. Define `f : U_k(k) → Herm_n`, `f(h) = ⊕_{j=0}^{t−1} (ĥ + 3j·1_k)`.
  - The `t` blocks have disjoint spectra and each block is non-scalar. So every eigenvalue of
    `f(h)` has multiplicity `≤ k − 1`, i.e. `f(h) ∈ U_k(n)`.
  - `f` is `PU(k)`-equivariant for the action through `[u] ↦ [u ⊗ 1_t]`.
- **Naturality.** `f` induces a map of associated bundles `EPU(k) ×_{PU(k)} U_k(k) → f_Q^* E_k`.
  Both fibres are `(k²−3)`-connected, so the primary obstructions satisfy
  `θ_k^{(n)}|_{BPU(k)} = f_* θ_k^{(k)}` with `f_* : π_{k²−2}(U_k(k)) → π_{k²−2}(U_k(n))`
  (Steenrod §35, Whitehead VI.6). For `k = n`, `U_k(k) ≃ S^{k²−2}` is the unit sphere of the
  traceless part, and `θ_k^{(k)}(P) = ±e(ad_0 P)`.
- **Computing `f_*`.** Let `V ⊂ U_k(n)` be the set of block matrices `⊕_j (a_j + 3j·1_k)` with each
  `a_j` non-scalar and `spec a_j ⊂ (−3/2, 3/2)`. Then `V ≃ Π_j S^{k²−2}`, and `f` factors through
  `V` as the diagonal. So `f_*(1) = Σ_j ι_*(e_j)`, where `e_j` is the sphere of block `j` with the
  other blocks fixed at simple spectrum.
  - The disk `{s a : s ∈ [0,1]}` in block `j` (other blocks fixed) meets `L_k` exactly at `s = 0`.
    There block `j` is `3j·1_k` and every other eigenvalue is simple, so the point lies in `L^o`,
    in component `i = jk` (`jk` eigenvalues below).
  - The disk is a normal slice to `L^o` there: the normal space of `L^o` at a matrix with a
    `k`-fold eigenvalue is the traceless Hermitian part on that eigenspace. So `e_j` is the
    linking sphere of component `jk`, and `ι_*(e_j) = ±g_{jk}` in the basis of D.1.
  - Hence `f_*(1) = Σ_{j<t} ±g_{jk}`, a unimodular vector, so `f_*` is a split injection
    `Z → Z^{n−k+1}`.
- **Conclusion.** `f_*` is split injective on coefficients, hence injective on `H^{k²−1}(X; ·)`.
  So `f_Q^* θ_k^{(n)} = f_*(±e(ad_0 P)) ≠ 0`, and D.2 (applicable since `dim X ≤ k² − 1`, `k ≤ n`)
  gives no self-adjoint section missing `L_k`. ∎

**Examples.**
- **Moore bundle.** `k = 2`, `X = S² ∪_2 e³`, `e = βw_2 ≠ 0`: for every `t`, every self-adjoint
  element of `A_P ⊗ M_t` has a repeated eigenvalue somewhere.
  - Direct check for this case: a section with simple spectrum everywhere has `n` global rank-one
    eigenprojections. So `Q` reduces to the maximal torus, whose extension splits, and the
    Dixmier–Douady class `βw_2` would vanish.
- **Pauli tower.** `k = 2^r`, `X = Z_{0,r}`, `dim X = 4^r − 1`. `w_{top}(ad_0 B_{0,r}) ≠ 0`
  (`pauli-tower-sections-are-somewhere-scalar`) is the mod-2 reduction of the Euler class, so
  `e ≠ 0`. For every `t`, `B_{0,r} ⊗ M_t` is `1/t`-rigid.

**Optimality of Theorem B.** In `B_{0,r} ⊗ M_t`, `n = 2^r t` and `d = 4^r − 1`.
- Theorem B permits rigidity levels `ε_0 < √(d+2)/n = √(k²+1)/(kt)`.
- Rigidity levels over point traces are multiples of `1/n`. The largest multiple below the bound
  is `k/n = 1/t`, and D.5 attains it.
- So for every `t`, and at block sizes `n = 2^r t → ∞`, the rigidity inequality `ε_0 n < √(d+2)` is
  attained with the best possible level. The torsion (2-primary, `2 | n`) is as D.3 requires.

## 7. Calibration against known cases

- **Dimension drop algebras.** `Z_{n,n+1}` has blocks of dimension `≤ 1` and size `n(n+1)`, so
  `ε_B → 0`. Corollary C gives divisibility, consistent with `Z`-stable algebras.
- **Unital matrix algebras.** `M_t ⊆ A` (`d = 0`) gives atoms `< √2/t`, matching the elementary
  bound `1/t` from `1 ⊗ diag(1, …, t)` up to the constant.
- **Villadsen algebras.** Villadsen's first-type algebras have `d_j/n_j` bounded and so `ε_B → 0`.
  Theorem B gives them elements with uniformly small atoms, while they fail strict comparison
  through Euler classes. No contradiction: Theorem B never uses comparison. The step from small
  atoms to divisibility and purity in Corollary C is where comparison is consumed.
- **Pauli tower and Moore bundle.** Both sit exactly at `d = k² − 1`, where Theorem A's hypothesis
  first fails.

# Virtual kernels of right-angled Artin groups, part 1: the homological theorem

Lane z1-19-raag-kernel, 2026-09-13. Target: Zaremsky, *Some open problems* (July 12, 2026),
Problem 1.19, root `zaremsky-1-19-raag-virtual-fn-kernel-conjecture`. Status: UNREVIEWED.

Summary. For a finite flag complex `L`, every division ring `D` containing the group
algebra `F[H]` of a finite-index subgroup `H ≤ A_L` gives the same Betti numbers,
`dim_D H_p(H; D) = [A_L : H] · b̃_{p−1}(L; F)` (Theorem 1). When `H` maps onto `Z` with a
kernel of type `FP_n(F)`, the Malcev--Neumann division ring kills `H_i(H; D)` for `i ≤ n`
(Theorem 2). Together they give Theorem 3: a virtual kernel of type `FP_n(F)` forces
`L` to be `(n−1)`-acyclic over `F`, and a virtual kernel of type `FP_n(Z)` forces
`(n−1)`-acyclicity over `Z`. Conjecture 1.19 is thereby reduced to a statement about
`π_1(L)` (Corollary 6).

## 0. Setting

- `L` is a finite nonempty flag complex with vertex set `V`; `A_L` is the right-angled
  Artin group. `𝓜` is the set of maximal simplices of `L`.
- The Salvetti complex `S_L` has one torus `T_σ = (S^1)^{|σ|}` for every simplex `σ` of
  `L` (including the empty simplex, `T_∅` = the unique vertex), glued along the
  coordinate subtori; its cells correspond to simplices of `L`, and `T_σ ∩ T_τ = T_{σ∩τ}`.
  Its vertex link is the octahedralization of `L`, which is flag because `L` is, so
  `S_L` is a nonpositively curved cube complex (Gromov's link condition) and its universal
  cover `X̃` is CAT(0), hence contractible. `π_1(T_σ) = A_σ ≅ Z^{|σ|}` injects into `A_L`.
- `H ≤ A_L` has finite index, `X̂ = X̃/H`, `p: X̂ → S_L` the covering map, and
  `p̃: X̃ → X̂` the universal cover. `C_*(X̃)` is a free resolution of `F` over `F[H]`.
- For a ring `D ⊇ F[H]` (right `F[H]`-module by right multiplication) and a subcomplex
  `Y ⊆ X̂`, put `H_*(Y; D) := H_*(D ⊗_{F[H]} C_*(p̃^{-1}Y))`, a left `D`-module. For
  `Y = X̂` this is `H_*(H; D)`.
- `b̃_j(L; F) = dim_F H̃_j(L; F)`, with `b̃_{−1}(L; F) = 0` since `L ≠ ∅`.

## 1. Theorem 1 (Betti numbers over division rings)

**Theorem 1.** Let `F` be a field, `H ≤ A_L` of finite index, and `D` any division ring
containing `F[H]` as a subring. Then for every `p ≥ 0`,
`H_p(H; D) ≅ D^{[A_L:H] · b̃_{p−1}(L; F)}` as left `D`-modules.

**Step 1 (tori are D-acyclic).** Let `Λ ≅ Z^k` with `k ≥ 1` and `D ⊇ F[Λ]` a division ring.
Then `H_*(Λ; D) = 0`. Choose a basis `w_1, …, w_k` and use the Koszul resolution of `F`
over `F[Λ]`. Then `D ⊗_{F[Λ]} K_* ` is the Koszul complex `K(x_1, …, x_k; D)`, where `x_i`
is right multiplication by `1 − w_i`; these operators commute. It is the mapping cone of
`x_1` acting on `N = K(x_2, …, x_k; D)`. Since `1 − w_1 ≠ 0` in `F[Λ] ⊆ D`, right
multiplication by `(1 − w_1)^{-1}` exists; it commutes with every `x_j` because
`1 − w_1` commutes with `1 − w_j`. So `x_1` is a chain automorphism of `N`, it induces an
isomorphism on `H_*(N)`, and the long exact sequence of the cone gives
`H_*(K(x; D)) = 0`.

**Step 2 (the cover by tori).** Let `𝒰` be the set of connected components `U` of
`p^{-1}(T_σ)` for `σ ∈ 𝓜`, and write `σ(U) = σ`. Every cell of `S_L` lies in some `T_σ`
with `σ` maximal, so the subcomplexes `U ∈ 𝒰` cover `X̂`. For distinct
`U_0, …, U_q ∈ 𝒰`, put `τ = σ(U_0) ∩ … ∩ σ(U_q)`. Then `U_0 ∩ … ∩ U_q` is a disjoint union of
components of `p^{-1}(T_τ)`: it lies in `p^{-1}(T_τ)`, and a component `C` of
`p^{-1}(T_τ)` is connected and lies in each `p^{-1}(T_{σ(U_j)})`, so if it meets `U_j` it is
contained in `U_j`.
- If `τ ≠ ∅`, a component `C` of `p^{-1}(T_τ)` is a finite cover of the torus `T_τ`; its
  preimage in `X̃` is a disjoint union of universal covers of `C` (as `A_τ → A_L` is
  injective), freely permuted by `H` with stabilizer `Λ_C ≅ Z^{|τ|}`. Therefore
  `D ⊗_{F[H]} C_*(p̃^{-1}C) = D ⊗_{F[Λ_C]} C_*(C̃)` computes `H_*(Λ_C; D)`, which vanishes by
  Step 1. So `H_*(U_0 ∩ … ∩ U_q; D) = 0`.
- If `τ = ∅`, the components are single vertices of `X̂`; each contributes `D` in degree 0.
- Two distinct components of the same `p^{-1}(T_σ)` are disjoint.

**Step 3 (Mayer--Vietoris spectral sequence).** Order `𝒰`. For each chain degree, the
augmented Čech sequence
`⋯ → ⊕_{U_0<U_1} C_*(p̃^{-1}(U_0∩U_1)) → ⊕_{U} C_*(p̃^{-1}U) → C_*(X̃) → 0`
is exact: it is spanned by cells, and the part spanned by one cell `e` is the augmented
chain complex of the full simplex on `{U : p̃(e) ⊆ U} ≠ ∅`. All terms are free
`F[H]`-modules on `H`-orbits of cells, so the sequence is `F[H] ⊗_F` (an exact complex of
`F`-vector spaces) in each degree, and it stays exact after `D ⊗_{F[H]} −`. The double
complex gives a spectral sequence
`E^1_{q,j} = ⊕_{U_0<⋯<U_q} H_j(U_0 ∩ ⋯ ∩ U_q; D) ⟹ H_{q+j}(H; D)`.

**Step 4 (the E^1 page).** By Step 2, `E^1_{q,j} = 0` for `j > 0`. In `E^1_{q,0}` the only
contributions come from tuples with `σ(U_0) ∩ ⋯ ∩ σ(U_q) = ∅`, one copy of `D` for each
vertex `x̂ ∈ U_0 ∩ ⋯ ∩ U_q`. Fix a vertex `x̂` of `X̂`. The members of `𝒰` containing `x̂` are
exactly one component for each `σ ∈ 𝓜`, so the tuples through `x̂` are the subsets of `𝓜`.
Let `Δ` be the full simplex with vertex set `𝓜` and `N ⊆ Δ` the subcomplex of subsets
with nonempty common intersection. Then
`E^1_{*,0} ≅ ⊕_{x̂ ∈ X̂^{(0)}} D ⊗_F C_*(Δ, N; F)`. The differential `d^1` is the alternating
sum of restrictions: the summand of `x̂` on a tuple maps identically to the summand of `x̂`
on a face when the face still has empty `σ`-intersection, and to `H_0` of a torus
component, which is `0`, otherwise. That is the relative simplicial boundary. The order
of `𝒰` induces an order on `𝓜` that may depend on `x̂`; reordering vertices changes the
relative chain complex only by a sign isomorphism.

**Step 5 (E^2 and collapse).** `Δ` is contractible, so `H_q(Δ, N; F) ≅ H̃_{q−1}(N; F)` for
`q ≥ 1`, and `H_0(Δ, N; F) = 0` because `N ≠ ∅`. `N` is the nerve of the cover of `L` by its
maximal simplices; all nonempty intersections are simplices, so `N ≃ L` by the nerve
lemma. Hence `E^2_{q,0} ≅ D^{|X̂^{(0)}| · b̃_{q−1}(L; F)}` and `E^2_{q,j} = 0` for `j > 0`. The
sequence has one row, so it collapses: `H_q(H; D) ≅ E^2_{q,0}`. Finally `S_L` has one
vertex, so `|X̂^{(0)}| = [A_L : H]`. ∎

**Checks.** `L` = a point: `A_L = Z`, all `b̃ = 0`, and `H_*(mZ; D) = 0` since `1 − t^m` is
invertible. `L` = two points: `A_L = F_2`, `b̃_0 = 1`, so `dim_D H_1(H; D) = [F_2 : H]` and
`H_0 = H_2 = 0`, matching `χ(H) = −[F_2 : H]`. `L` = a simplex: `A_L = Z^k`, everything
vanishes. With `F = Q`, `H = A_L` and `D` the Linnell division ring, Theorem 1 gives the
Davis--Leary formula `b^{(2)}_p(A_L) = b̃_{p−1}(L; Q)` (M. W. Davis and I. J. Leary,
J. London Math. Soc. (2) 68 (2003); recalled, not re-read).

## 2. Theorem 2 (fibres of type FP_n kill Malcev--Neumann homology)

Let `H` carry a bi-invariant total order `<` and let `F` be a field. The Malcev--Neumann
ring `D = F((H, <))` of formal series `Σ a_h h` with well-ordered support is a division
ring containing `F[H]` (A. I. Malcev, Doklady Akad. Nauk SSSR 60 (1948); B. H. Neumann,
Trans. Amer. Math. Soc. 66 (1949); bibliographic data recalled).

**Theorem 2.** If `ψ: H → Z` is an epimorphism whose kernel `K` is of type `FP_n(F)`, then
`H_i(H; D) = 0` for `0 ≤ i ≤ n`.

**Proof.** (a) Let `D_K ⊆ D` be the series supported in `K`. This is `F((K, <|_K))`, a
division ring (Malcev--Neumann for `K`), and the inclusion is a ring homomorphism since
products are computed by the same finite sums. It contains `F[K]`.
(b) Pick `t ∈ H` with `ψ(t) = 1`. Conjugation by `t` preserves `K` and the order
(bi-invariance), so `α(d) = t d t^{-1}` is an automorphism of `D_K`.
(c) The powers `t^j` are left linearly independent over `D_K`: `supp(d t^j) ⊆ K t^j`, and the
cosets `K t^j` are pairwise disjoint, so `Σ_j d_j t^j = 0` forces every `d_j = 0`. Hence
the subring `R` generated by `D_K` and `t^{±1}` is the twisted Laurent polynomial ring
`D_K[t^{±1}; α]`.
(d) `R` is a left and right principal ideal domain (division algorithm on degree, as all
leading coefficients are invertible), so it is a left and right Ore domain. Its nonzero
elements are invertible in `D`, so its classical ring of fractions `Q` embeds in `D`.
(e) As `(D_K, F[H])`-bimodules, `R ≅ D_K ⊗_{F[K]} F[H]` via `d ⊗ h ↦ d h`: `F[H]` is free as a
left `F[K]`-module on `{t^j}`, and the map is bijective by (c).
(f) Let `P_* → F` be a projective resolution over `F[H]`; it is also projective over
`F[K]`. By (e), `R ⊗_{F[H]} P_* ≅ D_K ⊗_{F[K]} P_*`, so `M_i := H_i(R ⊗_{F[H]} P_*)` is
`H_i(K; D_K)` with a compatible left `R`-module structure.
(g) Since `K` is of type `FP_n(F)`, `H_i(K; D_K)` can be computed from a resolution that is
finitely generated in degrees `≤ n`, so `dim_{D_K} M_i < ∞` for `i ≤ n`.
(h) A left `R`-module `M` with `dim_{D_K} M = m < ∞` is torsion: for `x ∈ M`, the vectors
`x, t x, …, t^m x` are dependent over `D_K`, so `r x = 0` for some `0 ≠ r ∈ R`. Then
`Q ⊗_R M = 0`, because `q ⊗ x = q r^{-1} ⊗ r x = 0`.
(i) `D ⊗_{F[H]} P_* = D ⊗_Q (Q ⊗_R (R ⊗_{F[H]} P_*))`. `Q` is flat over `R` (Ore localization)
and `D` is free as a right `Q`-module, so homology commutes with both tensor products:
`H_i(H; D) ≅ D ⊗_Q (Q ⊗_R M_i) = 0` for `i ≤ n`. ∎

## 3. Theorem 3 and corollaries

**Theorem 3.** Let `L` be a finite flag complex, `H ≤ A_L` of finite index, `F` a field,
`n ≥ 1`. If some epimorphism `ψ: H → Z` has kernel of type `FP_n(F)`, then `H̃_j(L; F) = 0`
for all `j ≤ n − 1`. If the kernel is of type `FP_n(Z)`, then `H̃_j(L; Z) = 0` for all
`j ≤ n − 1`.

**Proof.** `L ≠ ∅`, since the trivial group has no epimorphism onto `Z`. Right-angled Artin
groups are bi-orderable (G. Duchamp and D. Krob, Semigroup Forum 45 (1992); G. Duchamp and
J.-Y. Thibon, Internat. J. Algebra Comput. 2 (1992); recalled), so `H` is. Let
`D = F((H, <))`. Theorem 2 gives `H_i(H; D) = 0` for `i ≤ n`, and Theorem 1 gives
`dim_D H_i(H; D) = [A_L : H] · b̃_{i−1}(L; F)`. So `b̃_j(L; F) = 0` for `j ≤ n − 1`.
Over `Z`: a kernel of type `FP_n(Z)` is of type `FP_n(F)` for every field `F` (tensor a
partial resolution), so `H̃_j(L; F) = 0` for all fields and `j ≤ n − 1`. By universal
coefficients `H̃_j(L; Z) ⊗ F ⊆ H̃_j(L; F) = 0`, and `H̃_j(L; Z)` is finitely generated, so
`⊗ Q = 0` and `⊗ F_p = 0` for all `p` force `H̃_j(L; Z) = 0`. ∎

**Corollary 4 (homological Conjecture 1.19).** Under the hypotheses of Theorem 3 the
Bestvina--Brady kernel `BB_L` is of type `FP_n(F)`, respectively `FP_n(Z)`. So `A_L` itself
maps onto `Z` with a kernel of type `FP_n(F)`, respectively `FP_n(Z)`. This uses the
Bestvina--Brady theorem: `BB_L` is of type `FP_n(R)` iff `L` is `(n−1)`-acyclic over `R`
(M. Bestvina and N. Brady, Invent. Math. 129 (1997); statement recalled, to be checked).

**Corollary 5 (n = 1).** Conjecture 1.19 holds for `n = 1`. A finitely generated kernel is
of type `FP_1(Z)`, so `L` is connected by Theorem 3, and `BB_L` is finitely generated when
`L` is connected (Bestvina--Brady, same caveat).

**Corollary 6 (reduction to π_1).** Consider the statement

(π) if some finite-index subgroup of `A_L` maps onto `Z` with finitely presented kernel,
then `L` is simply connected.

If (π) holds for every finite flag complex `L`, then Conjecture 1.19 holds for every `n`.
Indeed a kernel of type `F_n` (`n ≥ 2`) is finitely presented and of type `FP_n(Z)`; (π)
makes `L` simply connected, Theorem 3 makes `H̃_j(L; Z) = 0` for `j ≤ n − 1`, Hurewicz makes
`L` `(n−1)`-connected, and Bestvina--Brady makes `BB_L` of type `F_n`. Conversely (π)
follows from Conjecture 1.19 for `n = 2` once a finitely presented kernel on `A_L` itself
forces `L` to be simply connected, which is the remark printed under Problem 1.23
(Meier--Meinert--VanWyk). A counterexample to Conjecture 1.19 therefore needs `n ≥ 2` and a
flag complex `L` with `H_1(L; Z) = 0` and `π_1(L) ≠ 1`: a nontrivial perfect fundamental
group.

## 4. Model tests

- `L` a flag triangulation of `RP^2`: `H̃_1(L; F_2) ≠ 0`, so no finite-index subgroup of
  `A_L` has a kernel of type `FP_2(F_2)`; over `Q`, `L` is acyclic and Theorem 3 allows
  kernels of type `FP_∞(Q)`, consistent with `BB_L` being of type `FP(Q)`.
- `L` a flag triangulation of an acyclic 2-complex with nontrivial perfect `π_1` (a spine
  of the Poincaré homology sphere minus a ball): Theorem 3 gives no obstruction. `BB_L` is
  of type `FP(Z)` but not finitely presented. This is exactly where (π) is open.

## 5. Credits and scope

Theorem 1 generalizes the Davis--Leary computation from ℓ²-Betti numbers to every division
ring containing the group algebra of a finite-index subgroup. Theorem 2 is a
Malcev--Neumann form of the vanishing half of the fibring theorems of D. Kielak (RFRS groups,
first ℓ²-Betti number) and S. Fisher (higher finiteness over arbitrary fields through
Hughes-free division rings). Over fields, Corollary 4 is probably a known consequence of
Fisher's theorem combined with a Davis--Leary computation in positive characteristic; the
proof here needs no Hughes-free division rings. Novelty and exact references are
unchecked: on 2026-09-13 the lane had no web search budget and the arXiv API returned 429.

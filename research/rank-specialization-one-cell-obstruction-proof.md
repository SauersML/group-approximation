---
rg: 2
id: rank-specialization-one-cell-obstruction-proof
kind: route
title: Fox relations of a subgroup with finite abelianization are killed by the L²-rank but not by a rank function that is trivial on the subgroup
target: rank-specialization-one-cell-asphericity-only-locally-indicable
requires:
  - finite-2-complex-with-zero-second-l2-betti-is-aspherical
  - contractible-complex-minus-cell-has-cyclic-homology
---

Conventions: vectors in `ℓ²G^m` are rows. `A ∈ M_{m×n}(Z[G])` acts by `v ↦ vA`, with entries acting
by right multiplication. This commutes with the left `NG`-action, and `(vA)B = v(AB)`.

`rk_G(A) = dim_G \overline{ℓ²G^m A} = m − dim_G ker A`. It is a Sylvester rank function. Every
Sylvester rank function `rk` has the following properties:
- **Unit invariance.** `rk(UA) = rk(A)` for invertible `U`, since `rk(UA) ≤ rk(A) = rk(U⁻¹UA) ≤ rk(UA)`.
- **Subadditivity.** `rk(A + B) ≤ rk(A) + rk(B)`.

## Step 0. The trivial kernel is a subgroup, and a rank function is trivial on it

Let `N' = {g ∈ G : rk'(1 − g) = 0}`.
- **Subgroup.** `1 − gh = (1 − g) + g(1 − h)`, and `rk'(g(1 − h)) = rk'(1 − h)` since `g` is a unit.
  So `N'` is closed under products. Since `1 − g⁻¹ = −g⁻¹(1 − g)`, it is closed under inverses.
- **Normal.** Conjugating by a unit preserves `rk'`.

Let `H ≤ N'` and `A` a matrix over `Z[H]`. Write each entry `a = Σ n_h h` as
`a = ε(a) + Σ n_h (h − 1)`. So `A − ε(A)` is a finite sum of matrices `n E_{ij}(h − 1)` with
`h ∈ H`, each of `rk'`-rank `≤ rk'(h − 1) = 0`. By subadditivity `rk'(A) = rk'(ε(A))`.

## Step 1. The rank function restricted to integer matrices

Suppose `rk'` has characteristic zero. For an integer matrix `B` take the Smith form `B = U D V`
with `U, V` unimodular and `D` diagonal. Then `rk'(B) = rk'(D)`, which is the sum of `rk'(d_i)`, and
equals the number of nonzero `d_i`. So `rk'(B) = rank_Q(B)`.

In characteristic `p`, `rk'(p) = 0`. If `p ∤ d`, write `ap + bd = 1`, which gives `rk'(d) = 1`. If
`p | d`, `rk'(d) ≤ rk'(p) = 0`. So `rk'(B) = rank_{F_p}(B)`.

## Step 2. The L²-rank of a relation matrix

Let `H = ⟨x₁, …, x_g⟩ ≤ G` be finitely generated and nontrivial, `F` the free group on `x₁, …, x_g`,
and `k = Q` (or `F_p`).
- The image of the relation module in `H₁(F; k) = k^g` is spanned by the abelianized Fox vectors
  `ε(∂R/∂x_j)_j` of relators `R` of `H`.
- Choose finitely many relators `R₁, …, R_m` whose vectors span this image.
- Let `A ∈ M_{m×g}(Z[H])` be their Fox matrix, and `∂₁ ∈ M_{g×1}(Z[H])` the column `(x_j − 1)`.

Then `rank_k ε(A) = g − dim_k H₁(H; k)`.

The fundamental formula `Σ_j (∂R/∂x_j)(x_j − 1) = R − 1` holds in `Z[F]`, and `R − 1 = 0` in `Z[H]`.
So `A∂₁ = 0`, hence `\overline{im A} ⊆ ker ∂₁` and `rk_G(A) ≤ g − rk_G(∂₁)`.

The orthogonal complement of `\overline{im ∂₁}` is the kernel of the adjoint
`w ↦ (w(x_j⁻¹ − 1))_j`. That is the space of vectors fixed by right multiplication by `H`.
- If `H` is infinite, that space is 0.
- If `H` is finite, it is the image of the projection `v ↦ v·(1/|H|)Σ_{h∈H} h`, whose `NG`-trace is
  `1/|H|`.

So `rk_G(∂₁) = 1 − 1/|H|`, with `1/∞ = 0`.

## Step 3. Theorem A

Assume `rk_G ≥ rk'` on all matrices and `H ≤ N'` nontrivial and finitely generated. Steps 0–2 give

`g − dim_k H₁(H; k) = rank_k ε(A) = rk'(ε(A)) = rk'(A) ≤ rk_G(A) ≤ g − 1 + 1/|H|`.

So `dim_k H₁(H; k) ≥ 1 − 1/|H| > 0`, hence `H₁(H; k) ≠ 0`.
- **`k = Q`.** `H` maps onto `Z`, so `N'` is locally indicable. A nontrivial finite `H` has
  `H₁(H; Q) = 0`, so `N'` is torsion-free.
- **`k = F_p`.** `H` maps onto `Z/p`.

**Special cases.**
- For the augmentation `rk' = rank_Q ∘ ε`, `N' = G`.
- If `rk'` factors through `π : G → G/N`, then `1 − n ↦ 0` for `n ∈ N`, so `N ≤ N'` is locally
  indicable. An extension of a locally indicable group by a locally indicable group is locally
  indicable: a f.g. `H` either maps nontrivially into `G/N`, whose f.g. image maps onto `Z`, or lies
  in `N`.
- For a universal division ring of fractions `D ⊇ Q[G]` with `rk_D = rk_G`, universality gives
  `rk_D ≥ rk_E` for every division ring `E` receiving `Q[G]`. Apply this to `E = Q` via `ε`.
- For `rk' = rank ρ/d`, `ker ρ ≤ N'`.

## Step 4. Theorem B

We may assume `L` has one vertex. The subcomplex `K` contains the 1-skeleton of `L`. Contracting a
maximal tree of that 1-skeleton gives homotopy equivalences `K → K/T` and `L → L/T`, with `K/T` still
equal to `L/T` minus `e`.

**Item 1.**
- By `contractible-complex-minus-cell-has-cyclic-homology`, `L` has `g` generators and `g` relators.
- `ε(M)` is the cellular boundary `C₂(L) → C₁(L) = Z^g`. Here `∂₁ = 0` on the one-vertex complex.
- `H₁(L) = 0` makes `ε(M)` surjective, and `H₂(L) = 0` makes it injective.
- A square integer matrix that is bijective on `Z^g` lies in `GL_g(Z)`.

**Item 2.** Write `∂₂ ∈ M_{(g−1)×g}(Z[G])` for the relator rows. Then
`b₂^(2)(K) = (g − 1) − rk_G(∂₂)`.

- **(⇒).** If `rk_G(M) = g`, then `ker M = 0`. If `v∂₂ = 0`, then `(v, 0)M = 0`, so `v = 0`. Hence
  `b₂^(2)(K) = 0`.
- **(⇐).** Suppose `ker ∂₂ = 0` and `(v, c)M = 0` with `c ∈ ℓ²G`. Right-multiplying by `∂₁` gives
  `v∂₂∂₁ + c(r − 1) = 0`. Since `∂₂∂₁ = 0`, this is `c(r − 1) = 0`.
  - The image of `r` generates `H₁(G) ≅ Z`, because `r` normally generates `G`. So `r` has infinite
    order.
  - Right multiplication by `r − 1` is therefore injective on `ℓ²G`: an `r`-invariant `ℓ²` vector
    vanishes on every coset of `⟨r⟩`.
  - So `c = 0`, then `v∂₂ = 0`, then `v = 0`.

`G` is infinite, so `b₀^(2) = 0`. By `contractible-complex-minus-cell-has-cyclic-homology`,
`χ(K) = 0`, so `b₁^(2)(G) = b₁^(2)(K) = b₂^(2)(K)`. When these vanish, `K` is aspherical by
`finite-2-complex-with-zero-second-l2-betti-is-aspherical`.

**Item 3.** This is Theorem A applied to `rk'`. The locally indicable quotients listed are
torsion-free abelian, or torsion-free-abelian-by-infinite-cyclic. The latter are locally indicable:
a nontrivial f.g. subgroup either maps nontrivially, hence onto an infinite cyclic group, into the
quotient `Z`, or lies in a torsion-free abelian group and so maps onto `Z`. Torsion-free metabelian
is not enough: the Hantzsche--Wendt group of Step 5 is torsion-free metabelian with finite
abelianization. The final sentence cites
`locally-indicable-2-complex-with-h2-zero-is-aspherical`. `H₂(K) = 0` holds because `K ⊂ L` and
`H₂(L) = 0` on 2-complexes.

## Step 5. Calibration checks

**Hantzsche--Wendt group.** For `P = ⟨x, y | x⁻¹y²xy², y⁻¹x²yx²⟩`:
- the abelianized Fox rows are `(0, 4)` and `(4, 0)`;
- `χ = 1 − 2 + 2 = 1`;
- `P` is infinite amenable, so `b₀^(2) = b₁^(2) = 0` and `b₂^(2) = 1`;
- hence `rk_P(∂₂) = 1 < 2 = rank_Q ε(∂₂)`.

This is Step 3 with `H = P`: `H₁(P; Q) = 0`.

**Finite groups.** For `x` of order `n`, `rk_G(Σ xⁱ) = 1/n < 1`.

## Step 6. Rank functions that factor faithfully through a quotient reduce to Howie on a cover

**Factoring.** Let `rk'` be any Sylvester rank function on `Z[G]` with trivial kernel `N'`, and let
`π : Z[G] → Z[Q]` be the quotient map, `Q = G/N'`. Every entry of `A − A'` for two lifts `A, A'` of
`πA` lies in the ideal generated by the `n − 1` with `n ∈ N'`. So it is a finite sum of terms
`m·u(n − 1)w` with `u, w ∈ G` and `m ∈ Z`, each of rank `≤ rk'(n − 1) = 0` by unit invariance.
Subadditivity gives `rk'(A) = rk'(A')`. So `rk'` induces a rank function `rk'_Q` on `Z[Q]` with
`rk' = rk'_Q ∘ π`.

**Faithful rank functions.** Call `rk'_Q` *faithful* when `x·B = 0` for a nonzero row `x` over
`Z[Q]` forces `rk'_Q(B) < m`, for every `m×n` matrix `B`. The von Neumann rank `rk_Q` is faithful,
since `Z[Q]^m ⊆ ℓ²Q^m`. So is the rank over any division ring containing `Z[Q]`.

**Proposition.** In the setting of Theorem B, let `N ⊴ G` be locally indicable, `Q = G/N`, and let
`rk''` be a faithful rank function on `Z[Q]` with `rk''(πM) = g`. Then `K` is aspherical. No rank
comparison with `rk_G` is used.

*Proof.* Let `K_N → K` be the regular cover with group `Q`, so `π₁(K_N) = N`. Its cellular
2-chains are `Z[Q]^{g−1}` and it has no 3-cells, so `H₂(K_N; Z) = {v ∈ Z[Q]^{g−1} : v·π∂₂ = 0}`. If
`v·π∂₂ = 0`, then `(v, 0)·πM = 0`. Faithfulness and `rk''(πM) = g` give `v = 0`. So
`H₂(K_N) = 0`. `K_N` is a connected 2-complex with locally indicable fundamental group, so it is
aspherical by `locally-indicable-2-complex-with-h2-zero-is-aspherical` (stated there for arbitrary
connected 2-complexes). A covering space of `K` is aspherical exactly when `K` is. ∎

**Consequence for the surviving route.** The transfer inequality `rk_G ≥ rk_Q ∘ π` across a locally
indicable `N`, whether or not it holds, proves nothing new for the one-cell case. Its conclusion
`rk_G(M) = g` would be drawn from `rk_Q(πM) = g`, and the Proposition already gives asphericity from
that hypothesis. The same holds for any dominated `rk'` whose induced `rk'_Q` on `Z[G/N']` is
faithful: by Theorem A, `N'` is locally indicable, so the Proposition applies with `N = N'`.

What remains of single-comparison routes is dominated rank functions whose induced rank function on
`Z[G/N']` is **not** faithful, for example `rank ρ / d` for a finite-dimensional representation `ρ` of
`G/N'` that is not injective on `Z[G/N']`. Approximation arguments, where `rk_G(M) = lim rk'_i(M)` and no single `rk'_i` has full rank on
`M`, are not touched.

**Calibration.** For `N = G` locally indicable, `Q = 1` and `rk'' = rank_Q`, this is exactly Howie's
theorem applied to `K`. For finite `Q` it is Howie applied to a finite cover.

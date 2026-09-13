# Pauli towers: a hyperfinite W*-bundle in which every self-adjoint element is somewhere scalar (2026-09-13)

Lane `ex2-tw-unsplittable-tails`. **Review PASS** for Theorems A and B, Consequences C1–C3 and Proposition D
(lane `ex-verify2-analysis`, `research/artifacts/ex-review2-analysis-2026-09-13-part9.md`). Continues
`research/artifacts/tw-projection-starved-bundle-faces-part2-2026-09-12.md` (tensor towers).

**Outcome.**
1. **Theorem A (topology).** There is a tower of flat `M_2`-bundles `B_k → Y_k`, with
   `Y_k = RP^{4^{k−1}} × RP^{2·4^{k−1}}` and Pauli holonomy, such that for all `n < m` every
   self-adjoint section of `⊠_{n<k≤m} B_k` is a scalar at some point. The obstruction is the top
   Stiefel–Whitney class of the traceless self-adjoint bundle, which is the Moore determinant
   (the product of all nonzero `F_2`-linear forms) and survives on the base.
2. **Theorem B (bundle).** The uniform tracial completion `M` of `A = lim C(Π_{k≤m} Y_k, ⊠_{k≤m} B_k)`
   is a strictly separable continuous W*-bundle over the compact metrizable space `X̂ = Π_k Y_k`,
   all fibres `R`, with the **scalar point property**: every self-adjoint `x ∈ M` has a point
   `λ ∈ X̂` with `π_λ(x) ∈ C·1`. In particular `M ≇ C_σ(X̂, R)`.
3. **Consequences.** BBSTWW Question 3.14 has a positive answer (a nontrivial R-fibre W*-bundle
   exists). `r-fibre-w-star-bundles-divide-the-unit-uniformly` is false (no c.p.c. order zero
   `φ: M_2 → M` has `‖E(1 − φ(1))‖ < 1/4`). Every tail of the tower fails soft half splitting.
   `A` is not Z-stable and has no nontrivial projections.
4. **Proposition D.** For towers of genuine vector bundles (`End(W_k)`) this primary obstruction
   vanishes identically. The twist (nonzero Dixmier–Douady class) is essential to the mechanism.

## 1. Pauli characters

`σ_0 = 1`, `σ_1 = X = [[0,1],[1,0]]`, `σ_3 = Z = diag(1,−1)`, `σ_2 = Y = iXZ`. Let
`V = ⟨g, g'⟩ ≅ (Z/2)²` act on `M_2` by `g ↦ Ad X`, `g' ↦ Ad Z` (these commute and are involutions,
since `XZ = −ZX`). The real space `Herm(C²) = R1 ⊕ RX ⊕ RY ⊕ RZ` consists of eigenlines:
`Ad X` negates `Y, Z`; `Ad Z` negates `X, Y`. Write the character of `σ_a` as
`χ_{σ_a}(ε g + ε' g') = ε·[a ∈ {2,3}] + ε'·[a ∈ {1,2}] ∈ F_2`. So
`χ_1 = (0,1)`, `χ_2 = (1,1)`, `χ_3 = (1,0)`, `χ_0 = 0`: a bijection `{0,1,2,3} → F_2²`.

For `G_r = V^r` acting factorwise on `M_2^{⊗r} = M_{2^r}`, the Pauli strings
`σ_a = σ_{a_1} ⊗ ··· ⊗ σ_{a_r}` (`a ∈ {0,1,2,3}^r`) form an `R`-basis of `Herm(C^{2^r})`; each is an
eigenvector with character `χ_a = (χ_{a_1}, ..., χ_{a_r}) ∈ F_2^{2r} = Hom(G_r, F_2)`.

**Lemma 1.** `a ↦ χ_a` is a bijection `{0,1,2,3}^r → Hom(G_r, F_2)` with `χ_a = 0` iff `a = 0`.
So `Herm_0(C^{2^r}) = ⊕_{χ ≠ 0} R_χ`, each nonzero character of `G_r` occurring exactly once.
In particular the commutant of the `G_r`-action on `M_{2^r}` is `C·1`. ∎

## 2. The tower

- `d_j = 2^{j−1}` for `j ≥ 1`; `Y_k = RP^{d_{2k−1}} × RP^{d_{2k}}`; `P_k = S^{d_{2k−1}} × S^{d_{2k}} → Y_k`,
  the product of the antipodal double covers, a principal `V`-bundle (`g`, `g'` act antipodally on
  the first, second sphere).
- `B_k = P_k ×_V M_2`, a flat `M_2`-bundle (locally trivial, fibre `M_2`, structure group `PU(2)`).
- `Z_m = Π_{k≤m} Y_k`, `Z_{n,m} = Π_{n<k≤m} Y_k`, and `B_{n,m} = ⊠_{n<k≤m} B_k`, a flat
  `M_{2^{m−n}}`-bundle over `Z_{n,m}` associated to `P_{n,m} = Π_{n<k≤m} P_k` and `G_{m−n}`.
- `A_m = C(Z_m, B_{0,m})`, connecting maps `a ↦ a ⊗ 1` (unital, injective), `A = lim A_m`.
- `A` is a unital separable nuclear `C(X̂)`-algebra, `X̂ = Π_k Y_k` compact metrizable, all fibres
  `M_{2^∞}`, no finite-dimensional representation.

## 3. Theorem A

**Theorem A.** For all `0 ≤ n < m` and every self-adjoint continuous section `h` of `B_{n,m}`
over `Z_{n,m}` (equivalently, of its pullback over `Z_m`), there is a point `z` with `h(z) ∈ R·1`.

*Proof.* Put `r = m − n`, `E = P_{n,m} ×_{G_r} Herm_0(C^{2^r})`, a real vector bundle of rank `4^r − 1`
(the traceless self-adjoint part of `B_{n,m}`). The section `h_0 = h − tr(h)·1` of `E` is continuous
and vanishes exactly where `h` is scalar.

1. **Splitting.** By Lemma 1, `E = ⊕_{χ ≠ 0} λ_χ` with `λ_χ = P_{n,m} ×_{G_r} R_χ`.
2. **First classes.** Index the coordinates of `Z_{n,m}` by `j ∈ J = {2n+1, ..., 2m}`, and let
   `t_j ∈ H¹(RP^{d_j}; F_2)` be the generator. The line bundle associated to the antipodal cover of
   `RP^d` and the sign character is the tautological bundle `γ`, with `w_1(γ) = t`. The line bundle
   `λ_χ` for `χ = (c_j)_{j∈J}` is the external tensor product `⊠_j γ_j^{c_j}`, so
   `w_1(λ_χ) = Σ_j c_j t_j`.
3. **Top class.** By the Whitney product formula,
   `w_{4^r−1}(E) = Π_{0 ≠ c ∈ F_2^J} (Σ_j c_j t_j)`.
4. **Moore identity (Lemma 2 below).** This product equals `det[t_j^{2^i}]_{0≤i<2r, j∈J}`, which over
   `F_2` is `Σ_σ Π_{j∈J} t_j^{2^{σ(j)}}` over bijections `σ: J → {0, ..., 2r−1}`. Distinct `σ` give
   distinct monomials, since the exponents are distinct powers of 2.
5. **Survival.** By Künneth, `H*(Z_{n,m}; F_2) = F_2[t_j : j ∈ J]/(t_j^{d_j+1})`, and its monomials
   with all exponents `≤ d_j` are linearly independent. The bijection `σ(j) = j − 2n − 1` has
   exponents `2^{j−2n−1} ≤ 2^{j−1} = d_j`. So `w_{4^r−1}(E) ≠ 0`.
6. **Conclusion.** A nowhere-vanishing section splits off a trivial line, `E = E' ⊕ R`, forcing
   `w_{4^r−1}(E) = w_{4^r−1}(E') = 0`. So `h_0` vanishes somewhere. ∎

**Lemma 2 (Moore).** Over `F_2`, `det[t_j^{2^i}]_{0≤i<s, 1≤j≤s} = Π_{0≠c∈F_2^s} (c·t)`.

*Proof.* Frobenius is additive, so if `t_i = Σ_{j≠i} c_j t_j` the columns are dependent. Hence each
nonzero linear form divides the determinant (division by `t_i − Σ c_j t_j` in the variable `t_i`).
The forms are pairwise non-associate primes of `F_2[t]`, so their product, of degree `2^s − 1`,
divides the determinant, which has the same degree. The quotient is a constant in `F_2`, and it is
nonzero because the determinant is nonzero (step 4). ∎

**Remarks.**
- For `n = 0` the survivor is unique and is the top class of `Z_m`, whose dimension
  `Σ_{j≤2m} 2^{j−1} = 4^m − 1` equals the rank of `E`. The tower is dimension-minimal for this argument.
  The regime is quadratic: base dimension `≈ R²` for tail rank `R = 2^m`, matching the dimension
  count of the predecessor artifact (Section 3) and Toms's quadratic regime.
- Projections: a projection `p ≠ 0, 1` in `C(Z_{n,m}, B_{n,m})` is nowhere scalar. So these algebras
  have no nontrivial projections, and neither does `A` (a projection of `A` is close to, hence
  unitarily conjugate to, a projection of some `A_m`).
- **Soft half splittings** (Definition in the predecessor, part 2). If `h` is a positive contraction
  with `|tr h − 1/2| ≤ ε` everywhere, then at its scalar point `h = μ1` and
  `tr(h − h²) = μ − μ² ≥ 1/4 − ε²`, which exceeds `ε` for `ε ≤ 1/5`. So no tail `B_{n,m}` admits a
  `1/5`-soft half splitting: the Azumaya form of `some-tensor-tower-has-unsplittable-tails` holds.

## 4. Theorem B

**Theorem B.** Let `M` be the uniform tracial completion of `A`.
1. `T(A) = Prob(X̂)`, `∂_e T(A) = {τ_λ : λ ∈ X̂}` is closed, and `M` is a strictly separable
   continuous W*-bundle over `X̂` with `E(x)(λ) = τ_λ(x)` and every fibre `R`.
2. **Scalar point property.** Every self-adjoint `x ∈ M` has `λ ∈ X̂` with `π_λ(x) ∈ C·1`.
3. `M` is not isomorphic to `C_σ(X̂, R)` as a W*-bundle.

*Proof of 1.* On `A_m`, a trace `τ` restricts to a probability measure `μ` on `Z_m`. With local
matrix units `e_{ij}` on trivializing open sets and a subordinate partition of unity `f_α`,
traciality gives `τ(f e_{ij}) = δ_{ij} τ(f e_{11})` for `f ∈ C_c(V_α)`, so `τ(a) = ∫ tr(a(z)) dμ(z)`.
Hence `T(A_m) = Prob(Z_m)`, and `T(A) = lim T(A_m) = Prob(X̂)`, a Bauer simplex with extreme points
the point traces `τ_λ = tr ∘ π_λ`, where `π_λ: A → A_λ = M_{2^∞}` is the fibre map. Then
`closed-extreme-trace-sets-give-r-fibre-w-star-bundles` (with `K = X̂`) gives the bundle, with fibres
`π_{τ_λ}(A)'' = R` (nuclear, no finite-dimensional representation). ∎

*Proof of 2.* For self-adjoint `y ∈ M` put `Var_λ(y) = E(y²)(λ) − E(y)(λ)²`, continuous on `X̂`.
- **Vanishing locus.** `Var_λ(y) = ‖π_λ(y) − τ_λ(y)1‖²_{2,λ}`, and the fibre trace is faithful on
  `π_λ(M) = R`. So `Var_λ(y) = 0` iff `π_λ(y) ∈ C·1`.
- **Lipschitz bound.** For self-adjoint `y, y'` with norms `≤ C`,
  `|τ(y²) − τ(y'²)| ≤ |τ((y − y')y)| + |τ(y'(y − y'))| ≤ 2C‖y − y'‖_{2,u}` and
  `|τ(y)² − τ(y')²| ≤ 2C‖y − y'‖_{2,u}`. So `V(y) = min_λ Var_λ(y)` satisfies
  `|V(y) − V(y')| ≤ 4C‖y − y'‖_{2,u}`.
- **Finite stages.** For self-adjoint `a ∈ A_m`, Theorem A (with `n = 0`) gives `z ∈ Z_m` with
  `a(z) ∈ R1`. Any `λ ∈ X̂` over `z` has `π_λ(a) = a(z) ⊗ 1 ∈ R1`. So `V(a) = 0`.
- **Density.** `M` is the set of norm-bounded `‖·‖_{2,u}`-Cauchy sequences from `A` modulo null
  sequences (Lemma 3 of the predecessor, part 1). For self-adjoint `x ∈ M` take such a sequence,
  replace each term by its real part (`‖w*‖_{2,u} = ‖w‖_{2,u}` by traciality), then by a norm-close
  self-adjoint element of `∪_m A_m` with the same bound. The Lipschitz bound gives `V(x) = 0`, and
  the minimum is attained by compactness of `X̂`. ∎

*Proof of 3.* A W*-bundle isomorphism intertwines the conditional expectations, so preserves
`Var_λ`. In `C_σ(X̂, R)` the constant section `e`, a projection of trace `1/2`, has `Var_λ = 1/4`
everywhere, contradicting 2. ∎

## 5. Consequences

- **C1. BBSTWW Question 3.14.** `M` is a nontrivial strictly separable continuous W*-bundle over a
  compact metrizable space with all fibres `R`: route into `nontrivial-w-star-bundle-with-r-fibres-exists`.
- **C2. No uniform order zero `M_2`.** Let `φ: M_2 → M` be c.p.c. order zero with
  `‖E(1 − φ(1))‖ < 1/4`. Write `φ = c·π(·)` (Winter–Zacharias), with `c = φ(1)` commuting with the
  supporting homomorphism `π` into each fibre von Neumann algebra `R`. Put `y = φ(e_{11})`.
  Traciality in the fibre with the partial isometries `π(e_{12})` gives `τ_λ(y) = τ_λ(c)/2 ≤ 1/2` and
  `τ_λ(y²) = τ_λ(c²)/2`. Put `ε_λ = τ_λ(1 − c) < 1/4`. From `c − c² ≤ 1 − c`,
  `τ_λ(c²) ≥ τ_λ(c) − τ_λ(1 − c) = 1 − 2ε_λ`. So
  `Var_λ(y) ≥ (1 − 2ε_λ)/2 − 1/4 = 1/4 − ε_λ > 0` at every `λ`. So `y` is nowhere scalar,
  contradicting Theorem B(2). This refutes
  `r-fibre-w-star-bundles-divide-the-unit-uniformly` at `N = 2`. The reduced power `M^U` contains no
  unital copy of `M_2`.
- **C3. `A` is not Z-stable.** `A ≅ A ⊗ Z` would give c.p.c. order zero `M_2 → A ⊂ M` with trace of
  the unit near 1 uniformly (from the unique trace of `Z`), contradicting C2.
- **C4. Where the witness lives.** `X̂` contains a Hilbert cube, and every point has only
  infinite-dimensional neighbourhoods. This is consistent with Ozawa's Corollary 16, with
  `r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`, with
  `bauer-gamma-failure-localizes-to-infinite-dim-point`, and with the local-triviality theorem
  (the bundle is not locally trivial: every neighbourhood contains full tail factors).
- **C5. Amplification destroys it.** In `M_2(M)` the section `e_{11} ⊗ 1` is a projection of constant
  trace `1/2`. The gap sits at the unit of `A`, not at `2[1_A]`.

## 6. Proposition D: genuine vector bundles carry no primary obstruction

**Proposition D.** For a complex vector bundle `W` of rank `w ≥ 2`, the real bundle `Herm_0(End W)`
(rank `w² − 1`) has vanishing Euler class and vanishing top Stiefel–Whitney class.

*Proof.* It is associated to the adjoint representation of the connected group `U(w)`, so it is
oriented and its Euler class is pulled back from `e ∈ H^{w²−1}(BU(w); Z)`. If `w` is even the degree
is odd and `H^{odd}(BU(w); Z) = 0`. If `w` is odd, `H*(BU(w); Z) → H*(BT; Z)` is injective, and over
`BT` the bundle contains the trivial summand `Lie(T) ∩ su(w)` of rank `w − 1 ≥ 1`, so `e|_{BT} = 0`.
The top Stiefel–Whitney class is the mod-2 reduction of `e`. ∎

**Consequences.**
- Each `B_{n,m}` has `w_top ≠ 0` (Theorem A), so it is not `End` of any vector bundle: its
  Dixmier–Douady class is nonzero. The building blocks are homogeneous (hence recursive
  subhomogeneous) but are not corners of trivial matrix bundles.
- `some-tensor-tower-has-unsplittable-tails`, as stated for vector bundles, is not settled by this
  mechanism. Vector-bundle towers with non-abelian irreducible holonomy (e.g. `Q_8 ⊂ SU(2)`) have no
  fixed points on the space of soft half projections, so Smith-theory obstructions exist over the
  whole classifying space, but they are not primary. Not attempted.
- `ah-face-bundles-are-trivial` is not settled. Whether `A` admits an AH presentation was not examined.

## 7. Trust surfaces and credit

- Theorem A uses only the Whitney product formula, Künneth for products of real projective spaces,
  `w_1` of tautological line bundles, and the Moore determinant. All proofs above are mine and
  unreviewed.
- Theorem B(1) uses `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` (Ozawa arXiv:1304.3523,
  Section 5 and Theorem 3, quoted on its route). Theorem B(2)–(3) are elementary.
- C2 uses the Winter–Zacharias structure theorem for order zero maps (standard, not re-read).
- **Novelty.** Bounded check only: Mommaerts (arXiv:2606.12134, Remark 4.7, as recorded on
  `nontrivial-w-star-bundle-with-r-fibres-exists`) records existence as unknown. No claim of novelty
  beyond that check.
- The Pauli characters and the Moore determinant are classical. The idea of using irreducible
  projective holonomy with a nonvanishing adjoint top class to force scalar points is, as far as this
  lane knows, the new ingredient.

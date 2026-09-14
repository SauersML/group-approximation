# oa-ozawa71: "So L(G) embeds in R^ω [Ozawa, Proposition 7.1]" (simple_kazhdan_sofic_group.tex l.168 at e80dcf20a)

Lane oa-ozawa71, launched ~20:15 by main. Brief: `ct/ROSTER-sk.md`, "OA LANES 20:15". No literature input.
Census key: `b55725a40939` (census 09e580c38, tip md5 4ad4921253626a4f858866c716a13385).

## CLAIM
CLAIM trace-vanishing hyperlinear models from separated ones GroupApproximation/Analysis/HyperlinearTraceVanishingModels.lean
CLAIM unit-ball 2-norm completeness of the tracial matrix ultraproduct GroupApproximation/Analysis/TracialMatrixQuotientUnitBall.lean
CLAIM trace-preserving unital ⋆-hom ℂ[G] → tracial matrix ultraproduct GroupApproximation/Analysis/GroupAlgebraTracialUltraproduct.lean
CLAIM resolvent map f(x) = 2x(1+x²)⁻¹: norm bounds and 2-norm Lipschitz bound in tracial C*-algebras GroupApproximation/Analysis/TracialResolventLipschitz.lean
CLAIM extension ℂ[G] → L(G) (moment transfer), trace-preserving and injective GroupApproximation/Analysis/GroupVonNeumannUltraproductEmbedding.lean
CLAIM printed endpoint l.168 GroupApproximation/Manuscript/SimpleKazhdanSofic/OzawaEmbedding.lean

## Printed sentence and definitions
- Tex l.165–168: "LEF groups are sofic, and sofic groups are hyperlinear [Pestov, Example 4.5 and Theorem 3.3]. So L(G)
  embeds in R^ω [Ozawa, Proposition 7.1]."
- Hyperlinear is the repository's `IsHyperlinear` (`Sofic/Hyperlinear`): unitary models on every finite set, approximately
  multiplicative, with pairwise normalized Hilbert–Schmidt distance² ≥ 2 − ε.
- L(G) is `GroupVonNeumann.groupVonNeumannAlgebra G = λ(G)''` with trace ⟪δ₁, · δ₁⟫, faithful (`GroupVonNeumannTrace`).
- R^ω is oa-hyperfinite's `HyperfiniteUltrapower ω` with `hyperfiniteUltratrace ω`.
- "Embeds" is spelled as a unital, trace-preserving, injective ⋆-homomorphism L(G) → R^ω. A trace-preserving ⋆-hom out of a
  tracial von Neumann algebra with faithful trace is automatically injective; normality is not stated.

## Route (the cited proposition is proved, not assumed)
1. Trace vanishing. The repository's separated models need not have small traces: the character j ↦ i^j of Z/4 is an exact
   model with |tr| = 1. Amplify u to V = (1 ⊕ u)^{⊗a} ⊗ (1 ⊕ ū)^{⊗a}. Then tr V_g = |(1 + tr u_g)/2|^{2a}, and
   Re tr u_g ≤ ε/2 for g ≠ 1 gives tr V_g ≤ ((2 + ε)/4)^a. Tensor factors add defects: ‖V_{gh} − V_g V_h‖₂ ≤ 2a·(defect of u).
2. For countable G, a sequence of such models induces a unital ⋆-hom π : ℂ[G] → TracialMatrixQuotient X ω with
   ultratrace ∘ π = coefficient at 1.
3. Extension without Kaplansky density.
   - For self-adjoint S ∈ L(G) with ‖S‖ ≤ 1, S = f(T₀), where f(t) = 2t/(1+t²) and T₀ = cfc g S ∈ L(G), g = f⁻¹ on [−1, 1].
   - Truncations b_n ∈ ℂ[G] of T₀ converge to T₀ in the 2-norm.
   - f satisfies ‖f(x) − f(y)‖₂ ≤ (5/2)‖x − y‖₂ in any tracial C*-algebra, by
     f(x) − f(y) = 2(1+x²)⁻¹[(x − y) + x(y − x)y](1+y²)⁻¹.
   - So f(π(b_n)) is bounded by 1 and 2-Cauchy, and converges by unit-ball completeness.
   - Joint moments match: on [−R, R], R ≥ ‖b‖₁, f is uniformly approximated by polynomials, and π, λ are ⋆-homs on ℂ[G]
     that agree on traces.
   - Moment matching plus faithfulness of the ultratrace extends Φ to a unital ⋆-hom L(G) → TracialMatrixQuotient X ω.
     It is trace-preserving, and injective because τ is faithful on L(G).
4. Compose with oa-hyperfinite's `matrixUltraproductToHyperfiniteUltrapower X ω` (unital, trace-preserving) into R^ω.

## Ownership check (20:4x)
- origin, the shared tree, `lanes/*.files` and landed.log have no module at these paths and no trace-vanishing amplification,
  ℂ[G] → tracial ultraproduct map, or L(G) extension.
- Consumed carriers:
  - `Sofic/Hyperlinear` (`IsHyperlinear`) and `Sofic/HyperlinearUltraproduct` (`HyperlinearApproximation`,
    `exists_hyperlinearApproximation_of_isHyperlinear`);
  - `Analysis/TracialMatrixUltraproduct`, `TracialQuotientCStar` and `TracialUltraproductCStar` (∏_ω M_n, its C*-algebra
    instance, `ultratraceCLM`);
  - `Analysis/GroupVonNeumannAlgebra` and `GroupVonNeumannTrace`;
  - oa-hyperfinite's θ (interface agreed by message, 20:4x).

## Ledger
| key | tex | status | carrier |
|---|---|---|---|
| `b55725a40939` | 168 | open | planned `SimpleKazhdanSofic.printedGroupVonNeumannEmbedsInUltrapower` |

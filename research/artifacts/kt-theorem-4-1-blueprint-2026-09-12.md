# Blueprint: Kun–Thom Theorem 4.1 in Lean

Lane `kt-norm-paper`, 2026-09-12. Campaign: the negative answer to
Bowen–Chapman arXiv:2511.06586 Problem 1.1, unconditional, no literature
inputs.

## Sources read

* Kun–Thom, *Nonsofic wreath products of residually finite groups*,
  arXiv:2608.06222v3 (20 Aug 2026), e-print source `secondpaper.tex`.
  Section 2 is lines 305–463, Section 3 is 464–695, Section 4 is 696–1367
  and Section 5 is 1368–1488.
* Alekseev–Thom, *Centralizers of sofic approximations of Kazhdan groups*,
  arXiv:2608.05362v1 (5 Aug 2026), e-print source `main_final.tex`.
  Section 2 is lines 143–414, Section 3 is 415–907 and Section 4 is 908–1312.

Both sources are on MSI under `/projects/standard/hsiehph/sauer354/bc-kt-norm-paper/`.

## The statement

Kun–Thom Definition 2.1: a homomorphism `σ : G → 𝒮_𝒰` is a *sofic
representation* if `tr σ(g) = 0` for `g ≠ 1`, along a fixed nonprincipal
ultrafilter. Theorem 4.1: if `Γ` is infranormal in `G` and both groups have
property (T), then `C_{𝒮_𝒰}(σ(Γ))` is normalized by `σ(G)`.

The theorem is stated only for free representations. The landed
`HasSoficCentralizerNormalization` quantifies over every injective `ρ` and
every ultrafilter, which is stronger than the paper's theorem.

The four Theorem 4.1 lanes agreed on a sequential free Prop instead:
`HasSequentialCentralizerNormalization Γ`. It quantifies over
`SoficApproximation G`, which is free by `asymptoticallyFaithful`, and over
sequences `v n` whose Hamming commutators with `σ n γ`, `γ ∈ Γ`, vanish. Its
conclusion is that the commutators of `σ n g * v n * (σ n g)⁻¹` with
`σ n γ` vanish. The consumer builds `v n` from a sofic approximation of the
free-lamp amalgam and needs no ultraproduct. `kt-norm-repo` owns the
definition, the generation step and the double bridge.

## Algebraic reduction

1. For `t ∈ P_Γ` and `c` commuting with `σ(Γ)`, `σ(t)⁻¹ c σ(t)` commutes with
   `σ(Γ)`, because `tγt⁻¹ ∈ Γ`.
2. The set of `g` with `σ(g) C σ(g)⁻¹ = C` is a subgroup containing `Γ`.
3. Hence Theorem 4.1 follows from the forward inclusion
   `σ(t) C σ(t)⁻¹ ⊆ C` for `t` in a finite `T ⊆ P_Γ` with
   `G = ⟨Γ, T⟩`. Kazhdan groups are finitely generated
   (`KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`).

## Proof of the forward inclusion (Kun–Thom §4)

Each step names the repository declarations it uses, or says what is missing.

1. **Expander decompositions** for `σ|_Γ` and for `σ`.
   Repo: `KunDecomposition.exists_expanderDecomposition`,
   `KunFixedDecomposition.expanderDecomposition`, `ExpanderDecomposition`,
   `SoficApproximation.restrict`. Finite `Γ` or finite `G` is the normal case
   (`isInfranormal_iff_normal_of_finite`).
2. **Completed component actions** on every block.
   Repo: `ExpanderDecomposition.componentCompletedAction`,
   `componentCompletedAction_taggedExpansion`, `IsClusterGood`,
   `badClusterComponentMass_negligible`, `ComponentCompletedMultiplicativity`.
3. **Dominant cell and median lemma** (Kun–Thom Lemmas 2.2, 2.3).
   Repo: `FiniteMultiGraph.coarea_mul`, `median_pinning_mul`,
   `DecompositionRefinement.cheeger_mul_totalLeakage_le_globalCrossing`.
4. **Component matching** under a compressor (quantitative part of Kun–Thom
   Proposition 3.1). Repo: `Criterion.onesided_drop`, `card_ratio_of_pinned`,
   `symmDiff_le_of_pinned`, `matching_injective`, `MatchingPreparation`,
   `CompressionRefinement.compressorLeakage_negligible`.
   Owner: `kt-norm-repo`.
5. **Cluster groupoid** (Kun–Thom Lemma 4.2 = Alekseev–Thom Lemma 3.4,
   Definition 4.1, Lemma 4.2).
   * Allowed partial bijections, the distance gap and groupoid presentation.
     Repo: `FinitePartialBijection`, `IsClusterCandidate`,
     `IsClusterCandidate.gap`, `PartialClusterSystem`, `.presentation`.
   * **Improvement of composites** (`PartialClusterSystem.improveExists`).
     Repo: only for exact transitive actions (`ofExactTransitiveKazhdanActions`).
     For the approximate component actions of step 2 this is **gap 1**,
     owner `kt-norm-paper`; design below.
   * Centralizer elements represented by patched bisections (Kun–Thom Lemma
     4.2(4)). Repo, for involutions: `Sofic/InvolutiveCentralizerComponents`,
     `RepairedComponentBisection`, `FiniteGroupoidBisection`.
6. **Relative functor** for a compressor (Kun–Thom Lemma 4.3): a faithful
   functor `F_n : 𝒞_n|_{R_n} → 𝒫_n|_{D_n}` with `F_n(π_n i) = i` and
   estimate (7). Repo: `PartialBijectionSandwich`. Missing (gap 2).
7. **One-sided median** (Kun–Thom Lemma 4.4) for orbit sizes and isotropy
   orders. Missing (gap 3), owner `kt-norm-counting`.
8. **Counting** (Kun–Thom proof of Theorem 4.1, tex lines 1110–1344): clean
   components, `Ω₁ = Ω₂`, isotropy index `< 2` gives a bijective hom-set
   injection, completion on negligible weight.
   Repo: `FiniteGroupoidCounting.fullOfFaithfulOfCardinalPreserving`.
   Owner `kt-norm-counting`.
9. **Hamming estimate** `d_H(b̂_n, u_n â_n u_n⁻¹) ≤ χ + r_n + 2q_n + O(δ_n + ε_n)`.
   Missing (gap 4), owner `kt-norm-fixedpoint`.

## Gap 1: improvement for approximate component actions

Alekseev–Thom Proposition 3.3 (two-component repair) proves improvement
through Kun–Thom 2019 Proposition 3.3, which is not in the repository. The
repository already proves the approximate relation-improvement layer of
Kun–Thom 2019 in sequence form, uniformly over permutations at each index:

* `KunThomRounding.exists_pairProduct_relation_eventually`: for a
  `MultiplicativeApproximation (K × J)` and products of two `η`-good
  permutations, eventually there is a relation close to the product graph
  with small diagonal boundary;
* `KazhdanImprovement.repairRelation_isEpsilonGood_of_close_relation` and
  `hammingDistance_repairRelation_lt`: rounding back to a good permutation;
* `KunThomParameters.exists_improvementParameters`: the numerical parameters.

The route for gap 1 packages two components as one model.

* **G1a. Swap encoding.** A composite `f.trans g : X ⇢ Z` becomes
  `c = (f.trans g).swapPerm` on `X ⊕ Z` with labels `sumAction`. Its bad arcs
  are bounded by the forward and backward equivariance defects
  (`card_swapEquivarianceDefect_le`,
  `PartialEquivarianceComposition.card_equivarianceDefect_trans_le`).
* **G1b. Two-summand rounding.** `HasL1PoincareAtOne` fails on a disjoint
  union. Row and column degrees of a relation close to the swap graph have
  the majority property on each summand separately, and label variation is
  additive over summands. A variant of `repairRelation_isEpsilonGood_of_boundary`
  with a per-summand Poincaré hypothesis gives an `ε`-good permutation.
* **G1c. Extraction.** `extractCrossing` of the rounded permutation, with
  `isClusterCandidate_extractCrossing_of_bounds` and
  `twoSidedDisagreement_extractCrossing_le`, gives the improving candidate.
* **G1d. Parameters.** The candidate threshold `h' m / 2` at scale
  `m = |C|/18` must dominate the output goodness. Use a variant of
  `exists_improvementParameters` with `(h + 7s) β < h η / 8` and
  `108 k² η / s < 1/40`, and a cluster expansion constant `h'` below the
  true Cheeger constant so that candidate defects are at most `η |X ⊕ Z| / 8`.
* **G1e. Uniformity by contradiction.** If for infinitely many `n` some good
  triple of components carries a pair of candidates with no improvement,
  choose one triple per such `n`. The completed sum actions on `X_n ⊕ Z_n`
  form a `MultiplicativeApproximation (K × Unit)`: good components have
  relative multiplication error tending to zero for each fixed pair, sizes
  tending to infinity, and injective labels. Applying
  `exists_pairProduct_relation_eventually` with `b = 1` contradicts the choice.
* **G1f. Good components.** Diagonal tolerance for the first `j(n)` pairs of
  group elements, by Markov's inequality from
  `componentMultiplicationError_sum_negligible` and
  `badClusterComponentMass_negligible`.

Freeness enters only through label injectivity and component sizes; the
correct-ball hypothesis of Alekseev–Thom is replaced by relative
multiplicativity on good components.

## Status

### Landed on main

* `2458bbc45`: G1a–G1e at source scale, in six modules
  `KunThom/CentralizerNormalization{FiberCoarea,SumPoincare,Parameters,
  CrossingRepair,SumApproximation,Improve}`. They contain `ComponentFamily`,
  `ImproveCloseAt`, `eventually_improveCloseAt` and `exists_joint_improvement`.
  G1b is split into coarea hypotheses (`FiberCoarea`) and a two-summand
  Poincaré inequality (`SumPoincare`). G1c is
  `repairRelation_extractCrossing_candidate_and_close`. G1d is
  `exists_repairParameters`. G1e packs counterexamples into
  `sumApproximation` and applies `exists_pairProduct_relation_eventually`
  with `b = 1`.
* `fb4a81460` (kt41-g1-build): `Matching/ScaledPartialClusterGroupoid`, the
  per-pair-radius version of `FinitePartialClusterData` and its presentation.
* `87c53ad0c`:
  * `KunThom/CentralizerNormalizationPairImprove`: `PairRepairAt`,
    `PairImproveCloseAt`, `eventually_pairRepairAt`,
    `pairImproveCloseAt_of_pairRepairAt`, `exists_joint_pairRepair` and
    `hasTaggedExpansionAtScale_of_cheeger`.
  * `KunThom/CentralizerNormalizationClusterSystem`:
    `ScaledPartialClusterSystem`, `clusterData`, `presentation`,
    `presentation_rel` and `ComponentFamily.clusterSystem`.

### Changes to the plan

* **Scales.** Objects of different sizes need their own scale, so
  `scale X = |model X| / 18`. Arrows use the pair scale
  `min (scale X) (scale Y)`, which is symmetric, so inverses need no repair.
  The crossing repair runs at threshold `h/2`, and the spare factor converts
  the source scale to the pair scale. A candidate forces
  `10 · scale X ≤ 11 · scale Y` (`scale_comparable`), which keeps every
  groupoid law below the eight-radius gap.
* **Lemma 4.2(2).** The raw arrow of the relative functor has defects up to
  `K₀` times the threshold, where `K₀` depends on the word lengths of the
  conjugated generators. `PairRepairAt K₀` repairs single arrows; improvement
  of composites is the case `K₀ = 4`.
* **Objects.** `ComponentFamily.expands` is an exact directed Cheeger bound,
  and `componentCompletedAction` only gives tagged expansion above a scale.
  So the objects are pruned cores, i.e. `MaximalCutRepair.retained` of the
  completed generator graph with completed actions on the core, following
  `Matching/EssentialExpanderRepair`.
* **Tagged expansion.** `taggedBoundary` maps onto `directedBoundary`, so the
  constant is `1` and label injectivity is not needed for expansion.

### Open leaves and owners

* ComponentFamily producer:
  * pruned cores with an exact Cheeger bound (kt41-g1-alt,
    `KunThom/CentralizerNormalizationPrunedCore`);
  * good components and the constructor (kt41-g1-uniform);
  * per-index decompositions and the `BlockEmbedding` companion
    (kt41-seq-decomp).
* Relative functor (kt41-functor), estimate (7) (kt41-functor-estimate),
  Lemma 4.4 instance (kt41-median-vertex), endgame (kt41-counting-endgame),
  and the transfer of the compressor matching to retained objects
  (kt-norm-counting).
* Gap 4, Hamming summation (kt-norm-fixedpoint).
* Assembly: `seqNormalizes_distinguished_of_kazhdan` in
  `KunThom/CompressorNormalizationCore`, which gives
  `hasSequentialCentralizerNormalization_of_kazhdan_infranormal`.

# Kun–Thom Theorem 4.1 chain: mathematical review

Lane `kt41-review`, 2026-09-12. This is a living file, updated after each finding.

bc-review audits evidence: probe tags, md5 sums and import closures. This file
audits the mathematics:
- statement fidelity against the fetched source;
- quantifier order;
- where each hypothesis is consumed;
- model tests at cases other than the calibration case;
- whether the landed pieces compose into `SeqNormalizes Γ t`.

**Sources.**
- Kun–Thom, arXiv:2608.06222v3, HTML fetched 2026-09-12 and converted to text.
  Section 4 was read in full: Theorem 4.1, Lemmas 4.2–4.4 and the proof of 4.1.
  Definition 2.1 was also read.
- Landed files, read at origin `2458bbc45`. The tip at `977b479e2` has no
  `KunThom/` change.

## Status

| # | Item | Verdict |
|---|------|---------|
| R1 | `SeqNormalizes`, `HasSequentialCentralizerNormalization` vs Theorem 4.1 | faithful: implied by 4.1 at the pair |
| R2 | producer skeleton `0365e49a5` | correct reduction; `hcore` asks no more than 4.1; pinned core file absent |
| R3 | step-9 summation `462e29bd5` | sound; fits the intended instance |
| R4 | gap-1 improvement `2458bbc45` | statement shape right; F2: no threshold lowering; F1 known (L2). Both fixes in flight on disk (R8) |
| R5 | counting modules `b30597455` | match the counting and Lemma 4.4; a fixed clamp level suffices |
| R6 | relative-functor finite lemmas | match the sentences of the proof of Lemma 4.3 |
| R7 | scale-defect fix | real on both halves, conditional on L1, F1 and F2 |
| R8 | in-flight modules on disk, 13:00–13:17, now landed | pre-landing review: no defect; they resolve F1 and F2 |
| R9 | landings 13:08–13:26 | per-pair groupoid: laws check out and compose with the cluster system; (A) no `ClusterMetric` for the per-pair presentation, **resolved by `514dba1a6`** (R11); **(B) the assembly's `Rel F` must cover every compressor** |
| R10 | landings 13:29–13:32 | no defect |
| R11 | `514dba1a6`, `08e96b025` | pair-radius metric resolves (A); single median application correct |
| R12 | `563dcd0dc`, `13382096b`, `cd55e0d7d` | **(C) the Lemma 4.2(4) forward half is at the global-scale `PartialClusterSystem`: no composition, no mass bound**; the rest no defect |

## R1. The sequential Prop against Theorem 4.1

**Source.** Definition 2.1: a sofic representation is a homomorphism
`σ : G → 𝒮_𝒰 = ∏_𝒰 Sym(Y_n)` with `tr σ(g) = 0` for `g ≠ 1`.

Theorem 4.1: if `Γ` is infranormal in `G` and both groups have property (T), then
`C_{𝒮_𝒰}(σ(Γ))` is normalized by `σ(G)`.

**Repo.**
- `SeqNormalizes Γ g` says: for every `A : SoficApproximation G` and every `v`, if
  `∀ γ ∈ Γ, A.AlmostCommutes v γ`, then `∀ γ ∈ Γ, A.AlmostCommutes (A.conjSeq g v) γ`.
- `HasSequentialCentralizerNormalization Γ` is `SeqNormalizes Γ g` for every `g`
  (`hasSequentialCentralizerNormalization_iff`).

**Theorem 4.1 implies the sequential Prop.**
1. Suppose the conclusion fails for some `A, v, g, γ`. Then there are `ε > 0` and
   an infinite index set `N'` on which the commutator distance is at least `ε`.
2. The subsequence along `N'` is again a sofic approximation. Take any
   nonprincipal ultrafilter on it.
3. `[A_n(·)]_𝒰` is a homomorphism by `asymptoticallyMultiplicative`.
4. It has trace zero off `1` by `asymptoticallyFaithful`: the fixed-point density is
   `1 − d_H(A_n g, 1) → 0`. So it is a sofic representation in the sense of
   Definition 2.1.
5. `[v_n]_𝒰` commutes with `σ(γ)` for every `γ ∈ Γ`.
6. Theorem 4.1 sends the ultralimit of the conjugated commutator distance to `0`.
   That contradicts step 1.

**Quantifier order.**
- The hypothesis is pointwise in `γ`, as membership in the centralizer is.
- The conclusion is pointwise in `g` and `γ`.
- Freeness enters through `asymptoticallyFaithful` and `card_tendsToInfinity`,
  which is exactly `tr σ(g) = 0`.
- The converse direction is not needed.

**Model tests.**
- **`Γ` normal, any `G`.** Every `g⁻¹` compresses, so
  `seqNormalizes_inv_of_mem_compressionSubmonoid` gives `SeqNormalizes Γ g`. It is
  true, as it must be.
- **`Γ = ⟨a⟩ ≤ BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩`.**
  - `Γ` is infranormal: `t` compresses and `Γ ∪ {t}` generates.
  - `Γ` is not normal: `t⁻¹ a t ∉ Γ`.
  - Neither group has (T).
  - `not_isSofic_freeLamp_of_sequentialNormalization` would make
    `BS(1,2) *_ℤ (ℤ × ℤ/2)` nonsofic. That group is sofic: it is an amalgam of
    amenable groups over an amenable subgroup. This literature fact is used only
    for the model test.
  - So `SeqNormalizes Γ t` fails there. The Prop has content, and the (T)
    hypotheses must actually be consumed.

## R2. Producer skeleton `0365e49a5`

`hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core` is a
correct reduction.

- **Finite `Γ`.** `normal_of_isInfranormal_of_finite` makes `Γ` normal. Every `g⁻¹`
  compresses, and the inverse direction gives `SeqNormalizes Γ g`. No (T) is used.
- **Infinite `Γ`.**
  - (T) gives `Group.FG G` and a symmetric generating finset of `Γ`.
  - `exists_finset_compressors_generate` gives finitely many compressors `T₀`.
  - `ofCompressor … (insert t T₀) … t` has distinguished compressor `t`.
- **`hcore` asks no more than Theorem 4.1 at the pair.**
  - `compressedEnd_spec`, with `embedΓ` the inclusion, forces `t Γ t⁻¹ ⊆ Γ`.
  - R1 gives `SeqNormalizes Γ g` for every `g`.
  - bc-review (aa) records the same conclusion.
- **Model tests of `hcore`.**
  - `CompressionSetup.infiniteΓ` makes `hcore` vacuous at finite `Γ`.
  - `CompressionSetup.generates` forces `Γ` to be infranormal. So `hcore` is vacuous
    at every non-infranormal `Γ`.
  - Neither degenerate case yields a false instance.
- **Where the core consumes the setup.** The proof of 4.1 applies Lemma 4.4 "for
  every ℓ", i.e. to every compressor of a generating family at once. The setup
  carries `compressors` and `generates`, so a core proof for `C.distinguished` has
  the whole family.
- **Fit with the pair.** Each producer matches the skeleton's binders:
  - `ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Ambient`;
  - `peripheral_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} ↥Peripheral`;
  - `peripheral_isInfranormal`;
  - `instance ambient_countable`.
- **Open pin.** The commit message names `seqNormalizes_distinguished_of_kazhdan`
  in `KunThom/CompressorNormalizationCore.lean`. That file exists neither on origin
  nor on disk, so its binders cannot be intent-diffed yet. When it lands it should
  take no more than:
  - `[Countable G]`;
  - (T) for `G` and for `↥Γ` at `.{0, 0}`;
  - `IsInfranormal Γ`;
  - a setup `C` whose `embedΓ` is the inclusion.

  Its conclusion should be `SeqNormalizes Γ C.distinguished`.

## R3. Step-9 summation `462e29bd5`

**Paper.** `d_H(b̂_n, u_n â_n u_n⁻¹) ≤ χ_{ℓ,n} + r_n + 2q_n + O(δ_n + ε_n)`, where the
distance gap gives `q_n = 2ε_n / h_Γ`.

**Repo.**
- `card_hammingDisagreement_patch_le_reseparation` bounds the disagreement by
  `offDomain + Σ_good x C + Σ_exceptional |C|`.
- Checked: `agreement_or_disagreement_small` bounds the tagged boundary of the
  agreement set by the two forward defects. Tagged expansion at scale `m′` then
  excludes both sets being `≥ m′`.
- The room hypothesis forces agreement `≥ m′`. So disagreement `< ⌊x⌋₊ + 1`, hence
  `≤ x`.
- On its source a retained arrow disagrees with `w` only where it disagrees with a
  reference arrow that realizes `w`.

**Why the reseparation is needed.**
- `IsClusterCandidate.gap` is stated at the candidate scale `m = |C|/18`.
- So "same cluster" gives disagreement `< 2m = |C|/9`, a fixed fraction that does
  not sum to `o(|Y|)`.
- The reseparation replaces `q_n` by `x C = (2·editBudget + 4·defects) / cheeger`.
  That sums to `O((h_n + δ_n + ξ_n)|Y|)/h_Γ` when the arrows are `h_n`-candidates.

**Intended instance, a non-calibration check.**
- The blocks are `Q_{π i}`. The retained arrow is `b_{π i}`. The reference is
  `a_{n,i}` sandwiched through the two `u`-bridges; `realizesOn_sandwich_bridge`
  gives `RealizesOn` exactly.
- With blocks `Q_{π i}`, both arrows are almost equivariant for the word labels
  `α(w_s)` of `t s t⁻¹`, not for `α(s)`. The reference comes from `u a u⁻¹`, and
  `u a u⁻¹` is equivariant for the transported labels.
- On that block choice `actY C` must be the word labels, and `hexp` is tagged
  expansion of the word-labelled graph on `Q_{π i}`. It follows from the Cheeger bound
  of `P_i = u Q_i` minus the edit budget `δ + ξ`, at scales above a multiple of
  budget/`h_Γ`.
- **Correction, 13:20.** The block choice is not forced. The in-flight
  `StepNineHammingReference` pulls back through `u` using
  `card_hammingDisagreement_conj_swap`, i.e. `#{b̂ ≠ u â u⁻¹} = #{â ≠ u⁻¹ b̂ u}`.
  - It then compares `a_i` with `transportArrow u β (π i) i` on `Q_i`, with the
    S-labels.
  - `hexp` there is tagged expansion of the S-labelled block action at constant
    cheeger/4 above the edit budget. That is the shape of the landed
    `componentCompletedAction_taggedExpansion`.
  - The word length enters only the defect budget, through
    `card_equivarianceDefect_transportArrow_le`.
  - That route is cleaner. The exact Cheeger input is still kt41-g1-alt's L1.

**Verdict.** Sound. The conclusion feeds `vanishing_hammingDistance_of_card_le`.

## R4. Gap-1 improvement `2458bbc45`

**Statement shape.**
- `eventually_improveCloseAt`, at fixed parameters, gives
  `∃ N, ∀ n ≥ N, ∀ i j l`: every pair of candidates `f : i ⇢ j` (scale of `i`) and
  `g : j ⇢ l` (scale of `j`) has an improving candidate `r : i ⇢ l` at the scale of
  `i`. It satisfies `twoSided(r, f.trans g) < 2·scale i` and
  `≤ 20000 ζ |model i|`.
- It is uniform over components at each index, by contradiction: one bad triple per
  index is packed into `sumApproximation`.
- `exists_joint_improvement` gives `h_n → 0` and `d_n → 0`, with `ρ ≤ h_n`
  eventually for a prescribed `ρ → 0`.
- This matches Lemma 4.2's diagonal choice. To get `ρ = o(h_n)`, pass `√ρ`.

**`ComponentFamily` model tests.**
- **Empty index at every `n`.** Every field holds and `ImproveCloseAt` is vacuous.
  Consistent: nothing false is produced.
- **No Kazhdan pair.** `hQ` fails.
- **Intended instance.** It needs L1 of `kt41-g1-alt-route-2026-09-12.md`: an exact
  Cheeger bound, uniform sizes, uniform multiplicativity and injective labels on the
  retained components.

### F1 (known: kt41-g1-alt L2). One global scale in the cluster groupoid

`PartialClusterSystem` and `FinitePartialClusterData` carry a single `scale` and
`radius`. `ImproveCloseAt` works at `|X|/18` per object.

Two supplements:
- **No single scale can serve.**
  - A free approximation can spread its mass evenly over components of sizes `2^k`,
    for `k₀(n) ≤ k ≤ log |Y_n|`. Then no bounded size window carries most of the mass.
  - With `scale ≤ min |X| / 17`, the absolute threshold `h·scale/2` is too small on
    the large components. There the restriction of an almost-commuting `v` is not a
    candidate, so Lemma 4.2(4) representation fails on most of the mass.
- **Source scale breaks `symm_mem`** when `|target| < |source|`.
  - A symmetric scale `min(|X|, |Y|)/18` repairs inverses.
  - `ImproveCloseAt` outputs at the source scale.
  - Both need a small slack, which F2's fix provides.

### F2 (new). `ImproveCloseAt` cannot lower the threshold, and Lemma 4.3 needs it to

**Source.** Lemma 4.2(2): "every partial bijection whose source defect, range
defect and equivariance defect are at most `K₀ε_n` can be changed within `r_n` to an
allowed partial bijection."

The proof of Lemma 4.3 uses it: "By the joint choice of scales, the right-hand side
is at most `K₀ε_n`. Improve `c` as in Lemma 4.2(2)."

**Repo.** In `ImproveCloseAt h′`, both inputs and the output are `h′`-candidates at
the same threshold.

**Why that is not enough.**
1. Take an `h`-candidate `b : Q_{π i} ⇢ Q_{π j}` for the tags `S`. The raw functor map
   `c = sandwich(bridge_i, bridge_j, b)` must be a candidate for the transported tags
   `u α(s) u⁻¹`. Off the label discrepancy, those tags agree with `α(w_s)`.
2. The landed bounds give
   ```
   defect(c) ≤ bridge defects
             + |S| · (sourceDefect b + k · defect_S b)
             + label discrepancies
            < (1 + |S|·k) · h · scale / 2 + o(h · scale),   k = max |w_s|.
   ```
   The inputs are:
   - `card_equivarianceDefect_sandwich_le`;
   - `card_equivarianceDefect_wordAct_le`;
   - `card_equivarianceDefect_congr_le`;
   - `card_mul_sourceDefect_le_card_equivarianceDefect`.
3. So `c` is a `K₀h`-candidate with `K₀ = 1 + |S|·k > 1`, not an `h`-candidate, and
   `ImproveCloseAt h` does not apply to it.
4. Different thresholds for `𝒞_n` and `𝒫_n` would break the isomorphism
   `U_n : 𝒞_n ≅ 𝒫_n`. Both `k_n(π i) ≤ k_n(i)` and the Hom-set bijection use it.
5. Adding `t S t⁻¹` to the tags only moves the problem: `𝒫_n` then needs
   `t² S t⁻²`, and so on.

**Proposed fix (owner kt-norm-paper): a slack variant.**

```
ImproveFromAt (K h′ d : ℝ) (n : ℕ) : Prop :=
  ∀ i l (c : FinitePartialBijection (model n i) (model n l)),
    c.sourceDefect + c.targetDefect < 2 * scale n i →
    (c.equivarianceDefect (tags n i) (tags n l)).card < K * h′ * scale n i / 2 →
    (c.symm.equivarianceDefect (tags n l) (tags n i)).card < K * h′ * scale n i / 2 →
    ∃ r, r.IsClusterCandidate (tags n i) (tags n l) h′ (scale n i) ∧
      r.twoSidedDisagreement c < 2 * scale n i ∧
      (r.twoSidedDisagreement c : ℝ) ≤ d * Fintype.card (model n i)
```

The contradiction proof of `eventually_improveCloseAt` should transfer:
- run it on the swap encoding of `c` itself, whose bad arcs are at most the forward
  plus backward defect of `c`, i.e. `< K·η·scale`;
- use goodness level `K·η` in `exists_pairProduct_relation_eventually`, keeping the
  boundary level `repairFactor·η`;
- choose `k` so that `q^{2k}·K` is absorbed by the numerical condition;
- require `ζ > k²·K·η` in the edit bound.

Special cases:
- composites are the case `K = 3` (`arith_four_defects`);
- inverses at the target scale are about `K = 2`, since
  `hundred_mul_defects_le_of_candidate` makes sizes agree within 1%.

So one theorem also covers the inverse half of F1.

**Consumers.** kt41-functor (the Lemma 4.3 functor on representatives), and
`symm_mem` at per-object scale.

**Status, 13:20: fix in flight, matching the proposal.** The on-disk
`CentralizerNormalizationPairImprove` proves:
- `PairRepairAt K₀ h' d n`, repair of single arrows whose defects are below
  `K₀·h'·min(scale i, scale l)/2`;
- `eventually_pairRepairAt`, with `K₀·η < ζ`, `k²·K₀·η < ζ`, and `K₀·η` in the
  linear term of the numerical condition;
- `pairImproveCloseAt_of_pairRepairAt` at `K₀ ≥ 4`;
- `exists_joint_pairRepair`, which gives both statements along one diagonal.

The functor lane chooses `K₀ ≥ 1.21·(1 + |S|·k)` plus bridge and label slack. Review
continues when it lands.

## R5. Counting modules `b30597455`

**`ComponentCountingNormalizationGroupoid` against the proof of Theorem 4.1.**
- `mul_card_orbit_le_of_clean` is `(1 − ζ_n) o_n(π i) ≤ o_n(i)`. The object map is
  `π⁻¹` on `R`, injective and connectedness-preserving through the faithful `F`.
- `card_dvd_of_injective` is `k_n(π i) ≤ k_n(i)`.
- `nonempty_hom_of_card_orbit_lt` is the splitting that proves `Ω₁ = Ω₂`.
- `map_bijective_of_isotropy_lt_two_mul` is "index `< 2` gives a Hom-set
  bijection". It needs a faithful `Functor` on the restricted groupoid, and
  `GroupoidPresentation.restrict` with `Morphism.toFunctor_faithful` supply that
  shape.

**`ComponentCountingNormalizationMedian` against Lemma 4.4.**
- The paper uses `H = f/(f + M_A) ∈ (0, 1)`. The repo clamps `φ − m_B` to `[−M, M]`.
- Both are bounded, and the median transfers by `isMedian_comp_monotone`.
- `deviation_negligible` holds for each fixed `M > 0`. That is enough for the endgame:
  - the index test needs `k_n(i)/k_n(π i) < 2`;
  - the splitting needs both orbit ratios `> 1/(2(1 − ζ_n))`;
  - both hold at a fixed logarithmic gap below `log 2`.
- (T) of `G` is consumed in `clamped_pinning` through `D.cheeger` of the ambient
  `ExpanderDecomposition`.
- One-sided drift is needed on every compressor label, invariance on the `Γ` labels,
  and `sum_abs_sub_negligible_of_closure` handles the rest. This matches "for
  every ℓ".

## R6. Relative-functor finite lemmas

The modules are:
- `c7f794109` Defects;
- `f4e8971f1` Words;
- `e8868748d` Bridges;
- `db7d2821e` Realization;
- `98369e474` BlockWords.

These are finite counting lemmas with no hypothesis Props. They match the proof of
Lemma 4.3: "commuting `b` past `α_n(w_s)` costs at most `|w_s|` times its generator
defect", together with the overlap maps and the label discrepancy `ξ`.

Realization supplies R3's `RealizesOn`. `card_equivarianceDefect_wordAct_le` is the
quantitative source of F2's `K₀`.

## R7. The scale-defect fix

There are two threshold terms.

**(i) The commutation term `Σ_X h·scale/2`.**
- It vanishes once `h = h_n → 0`: `sum_candidateThreshold_le`, and on disk
  `BisectionActualDefect.card_commutationDefect_patch_le_of_candidates`, per-block
  scale, `≤ 3(h/34)|Y|`.
- `exists_joint_improvement` supplies `h_n → 0`.
- The expansion constant stays at the Cheeger level for the gap
  (`hasTaggedExpansionAtScale_of_le`).

**(ii) The near radius `2·scale`.** It is handled by R3's reseparation at the true
Cheeger constant.

**Verdict.** The fix is real on both halves. Both halves still need:
- L1, for tagged expansion at small scales;
- F1 and F2, to populate the groupoid with `h_n`-candidates.

## R8. Pre-landing review of in-flight modules

These files were read on disk at 13:00–13:17. They are unlanded, and bc-review will
audit the evidence when they land.

- **`CentralizerNormalizationClusterSystem`: `ScaledPartialClusterSystem`.**
  - Per-object `scale X = |X|/18`, with the pair scale `min` on arrows.
  - `improveExists` and `repairExists`, the latter with slack `K₀`.
  - `expands` at scale 1 with constant `h ≤ cheeger`.
  - `scale_comparable : 10·scale X ≤ 11·scale Y` for any candidate `X → Y`.
  - Checks:
    - `f.symm` stays a candidate at the same `min`, so inverses work.
    - Near transitivity: `< 4m < 16m` gives `< 2m`.
    - Composition congruence: `2m_XY + 2m_YZ + O(d)` is at most
      `≈ 4.84·m_XZ + O(d) < 16·m_XZ`.
    - `repairExists` has no `selfSmall` hypothesis, but
      `|L|·sourceDefect ≤ defect < K₀·h·m/2` supplies it.
  - Model test, empty `I`: vacuous and harmless.
  - `expands` at scale 1 forces the labels to be expanders. That is the exact Cheeger
    input of L1, which the on-disk `SequentialComponentFamilyPruning` and
    `SequentialComponentFamilyCompletion` build (`completion_hasCheegerLowerBound`,
    `h/(8|T|)` after pruning).
- **`CentralizerNormalizationPairImprove`.** See F2 above. It is the Lemma 4.2(2)
  shape.
  - With `F([b]) := [repair(transportArrow u β (π i) i (ā i))]`, the functor lives in
    `𝒞_n` itself: `u⁻¹ b u` is S-equivariant up to
    `card_equivarianceDefect_transportArrow_le`.
  - So no separate transported groupoid is needed, and `U_n` is implicit.
- **`StepNineHammingReference`, `StepNineHammingDefects`, `StepNineHammingEstimate`.**
  - These give step 9 through the pull-back correction in R3.
  - The budget is the actual defect of `a_i`, the missing mass of the bridges,
    compatibility failures, localized label failures and the defects of `b_{π i}`.
    Each sums to `o(|Y|)` once the arrows are `h_n`-candidates.
  - `hnear` comes from the cluster identity plus `repair` within `d_n|Q_i|`.
  - `hroom` holds when `d_n` and `h_n` are small.
- **`BisectionActualDefect`.**
  - Per-block scale `m C` with `17·m C ≤ |C|`.
  - The commutation term is at most `3(h/34)|Y|`.
  - The sequential form needs `Vanishing h`.
  - Model test, no blocks: the uncovered mass is all of `Y`, so `huncovered` fails
    visibly.
- **`MedianVertexForm`, `MedianVertexFormLocal`.**
  - Object-to-vertex transfer for Lemma 4.4, with a log observable cut at 1.
  - `(1 − ζ)a ≤ b` becomes drift `2ζ`.
  - The hypotheses hold for every compressor over `ambientGenerators`.
  - `localRatio_negligible` is equation (4) in component-weight measure.
- **`CompressorMatching`.** The Proposition 3.1 matching is exported for every
  compressor over one pair of decompositions (`withDistinguished`). This is the
  multi-compressor use in the proof of 4.1.
- **`CentralizerNormalizationUniformMarkov`, `CentralizerNormalizationUniformGood`.**
  - Diagonal Markov selection over countably many error kinds.
  - Uniform over good objects for each fixed kind, with a negligible bad mass.
  - Freeness is consumed through the ambient collision counts, and `[Infinite K]`
    through the small components.
- **`NormalizationFromCriterionClosure`.** `almostCommutes_of_generators` carries
  generator-level commutation of `b̂_n` to all of `Γ`, as the conclusion of
  `SeqNormalizes` needs.

**Not yet seen anywhere:**
- a presentation of the per-pair-radius groupoid, i.e. `FinitePartialClusterData`
  with the radius indexed by pairs;
- the Lemma 4.2(4) forward representation of an arbitrary almost-commuting `v` by a
  patched bisection;
- the `GroupoidPresentation.Morphism` instance of the functor;
- the assembly into `seqNormalizes_distinguished_of_kazhdan`.

## R9. Landings 13:08–13:26

bc-review audits the evidence. Every `KunThom/` blob I reviewed on disk equals its
origin blob: `PairImprove` `fa9cdba96`, `ClusterSystem` `d1b14faa0`.

### `fb4a81460`: `Matching/ScaledPartialClusterGroupoid` (coordinator's request). No defect

The groupoid laws against Lemma 4.2(3), with per-pair thresholds, recomputed from
the fields. The paper's version is "`2/5 < 1 − q_n`, the gap forces `≤ q_n`".
- **Near transitivity.** `< 2r < 8r`, so the gap gives `< r`.
- **Congruence.** `< r_XZ + (r_XY + r_YZ) + r_XZ ≤ 4.2·r_XZ`. This uses
  `radius_source_le_left g X` and `radius_target_le f Z`.
- **Associativity.** `< 2 r_WZ + r_WY + r_YZ + r_WX + r_XZ ≤ 6.4·r_WZ`, with four
  comparability instances.
- **Inverse laws.** `< r_YY + 2·targetDefect < 3.2·r_YY`. The right law goes through
  `f.symm` (`radius_target_le_left`), which is the reported slip and its fix.
- **Degenerate case.** An oversized `radius` gives a legitimate but trivial groupoid.
  That is visible downstream: step 9's `hroom` needs `2·sc + x + 1 ≤ |C|`.

**Composes with `87c53ad0c`.** `ScaledPartialClusterSystem.clusterData` supplies
every field:
- `radius = 2·min(scale X, scale Y)`;
- `one_mem` from `isClusterCandidate_refl` at `min_self`;
- `symm_mem` from `min_comm` and `.symm`;
- `gap` from `IsClusterCandidate.gap` at the pair scale, with `expands` lowered from
  scale 1 and `size_min_left`/`size_min_right`;
- `radius_comparable` from `scale_comparable`.

### `0b0986179`: `RelativeFunctorMetric` and `RelativeFunctorAssembly`. Composition gap (A)

**The landed part is sound.** The functor, faithfulness, estimate (7)
(`twoSidedDisagreement_sandwich_lt_of_ofRep_eq`) and `nonempty_hom_relativeFunctor`
all match Lemma 4.3.

**Gap (A).**
- `GroupoidPresentation.ClusterMetric` has one radius per source object, with
  `lt_of_rel` below `radius X` and `rel_of_lt` below `8·radius X`.
- The only instance is `FinitePartialClusterData.clusterMetric`, with constant radius.
  No instance exists for `ScaledFinitePartialClusterData.presentation`, on origin or
  on disk.
- None can come from that structure's fields.
  - `lt_of_rel` needs `radius X ≥ r_XY` for every `Y` joined to `X`, when related
    distances approach `r_XY`.
  - `rel_of_lt` needs `8·radius X ≤ 8·r_XY` for every such `Y`, since the recorded
    gap only puts far distances `≥ 8·r_XY`.
  - `r_XY = 2·min(scale X, scale Y)` varies with `Y`, by up to `11/10` under
    `radius_comparable`.

**Fixes.**
1. **A concrete instance at `ScaledPartialClusterSystem.presentation`.** Take
   `radius X := 2·scale X`.
   - Near: `< 2m ≤ 2·scale X`.
   - Far: `agreement_or_disagreement_small` puts one direction at disagreement
     `> |·| − m`, so far distance `≥ min(|X|, |Y|) − m`.
   - A candidate gives `|Y| ≥ |X| − m/100` (`hundred_mul_defects_le_of_candidate`).
   - So far distance `≥ 18·scale X − 1.01·m ≥ 16.99·scale X > 16·scale X`.
   - `comp_close` and `self_small` hold since `2·min ≤ 2·scale X`.
2. **Factor 7 in `rel_of_lt`.** Then `radius X := 2·scale X` works from the abstract
   fields: `14·scale X ≤ 16·(10/11)·scale X ≤ 8·r_XY`.
   - The functor budgets stay satisfiable:
     - `hrespects`: `≈ 2s ≤ 14s`;
     - `hcomp`: `≈ 8.2s ≤ 14s`;
     - `hfaithful`: `≈ 6.2s ≤ 14s`.
3. **A pair radius in `ClusterMetric`.**

**Owner.** kt41-functor.

### `f5a22c36e`: `CompressorNormalizationAssembly`. Sound skeleton; one instantiation trap (B)

`seqNormalizes_of_compressor_of_steps` is correct as stated. The hypotheses match the
paper's steps:
- a joint scale with `ρ = o(threshold)`;
- representation under domination;
- the converse for vanishing thresholds;
- the functor under domination of the matching error;
- `OneSided → Concentrated`;
- counting for every bisection sequence;
- Hamming;
- the wrapper, which is `seqNormalizes_of_forall_not_uniform_lower_bound` from
  `SequentialContradiction`.

**Trap (B).**
- The docstring calls `Rel F` "relative data of t" and `matchingError D` "the matching
  error of t".
- Lemma 4.4 needs the one-sided inequalities along every compressor of a generating
  family: "for every ℓ", and "apply Lemmas 4.2 and 4.3 simultaneously to this finite
  family".
- If `Rel F` carries only `t`, `hmedian : OneSided R → Concentrated R` cannot be
  derived. The clamped observable is controlled only along the `t` and `Γ` labels, and
  `clamped_pinning` needs every ambient generator.
- `MedianVertexFormLocal` already takes a matching for every compressor. So the
  instance should let `Rel F` carry the relative data of all of `C.compressors`, and
  `matchingError D` their sum.

### Other landings. No defect

- **`fc6e7940b` `ComponentCountingRetainedMatching`.**
  `|u Q △ Q'| ≤ |u B △ B'| + |B \ Q| + |B' \ Q'|`. The object match is induced by an
  injective parent map.
- **`d84f69fa4` `CountingEndgameCompletion`.** Completion within orbits.
  `exists_bisection_extend` is the paper's "choose a bijection between their
  complements … arbitrary arrow".
- **`8383dbd5f` `CountingEndgameLift`.** `exists_bisection_lift` for an abstract
  faithful functor that is injective on objects, from
  `|orbit(F X)| < |orbit X| + |orbit(sel X)|` and isotropy index `< 2`. This is
  `Ω₁ = Ω₂` plus the Hom-set bijection.
- **`f3ea74313` `SequentialContradiction`.** Reindexing, the subsequence principle and
  slow diagonals. `seqNormalizes_of_forall_not_uniform_lower_bound` is R1's
  subsequence argument, stated sequentially.
- **`87c53ad0c`, `83a349325`, `773d7952c`, `6870469d4`, `a3ae7dd4c`, `4fd4ba058`.**
  Reviewed pre-landing (R8).
- **`5f364e5f1` `RetainedComponentExpansion`.** L1:
  - removing the maximal sparse cut leaves an exact directed Cheeger bound `c/|T|` on
    every agreeing completion;
  - the removed mass is `≤ E/(γ − c)`;
  - the additive inequality comes from an edited expander.

  This matches kt41-g1-alt's recipe.

## R10. Landings 13:29–13:32. No defect

- **`54691ccdf` `ComponentCountingRetainedMatchingSums`.** Over the retained domain,
  the symmetric differences are at most the block matching error over `Acc` plus twice
  the removed mass. The parent map is injective, so each removed part is counted at
  most twice. The unmatched weight is charged to non-acceptable blocks, empty blocks
  and the matching error.
- **`9105379d6` `SequentialComponentFamily{Pruning,Completion,Levels}`.** This is
  L1.
  - `exists_prune`: `h|U| ≤ 2B`, and inner expansion with factor 8 off `U`, under
    `10B ≤ h|Y|`.
  - `completion_hasCheegerLowerBound`: `h/(8|T|)`, the tagged-to-directed factor
    `|T|`.
  - Being good at level `k` bounds `budget/cheeger` by `|C|/(k+1)` through the level
    error. So the pruned mass `≤ 2B/h` is a vanishing fraction uniformly over good
    components as `level → ∞`. That is what the uniform `locallyMultiplicative` needs,
    since a completed product failure is an ambient failure or an image in `U`.
  - Label injectivity comes through `card_sub_le_collision_add_of_completion_eq`
    against the collision term of the level error.
- **`9d805743d` `RelativeFunctorEstimateMatching`.** Each bridge's missing mass, for
  `q` and for `q⁻¹`, is at most `|q Q_C △ Q_D|`, or the block form plus the removed
  masses. This is `β` for `relativeFunctor`.
- **`b5b7dbc72` `CountingEndgameWeights`.**
  - `card_lt_add_of_ratio`:
    `oX + oX' ≥ (1 − ζ)(cX + cX') ≥ 2(1 − ζ)·oD/ρ > oD` for `ρ < 2(1 − ζ)`. This is
    the `horbit` input of `exists_bisection_lift`, i.e. the splitting.
  - `lt_two_mul_of_ratio`: isotropy index `< 2`.
  - `sum_compl_image_le`: the completion weight.
  - `mul_sum_le_of_dirty`: the orbits with `θ > ζ` weigh at most
    `ν(B)/(ζ(1 − ε))`. This is the paper's "`ℓ`-clean", given `ν(B)/ζ_n → 0`.

## R11. Landings 13:35–13:36

### `514dba1a6` (kt41-functor): pair radii in `ClusterMetric`. Resolves (A)

- **The metric.** `ClusterMetric.radius : I → I → ℕ`. The instances
  `ScaledFinitePartialClusterData.clusterMetric` and
  `ScaledPartialClusterSystem.clusterMetric` (radius `2·min(scale X, scale Y)`) take
  their fields directly from `Near`, `near_of_lt_eight`, `improve_close` and
  `self_small`.
- **The functor budgets, rederived from the landed triangle chains:**
  - **`hrespects`.** `twoSidedDisagreement_transport_le` gives
    `2ρ_XY + β_X + β_Y + r_P(X,Y)`, and the target is `8·r_Q(X,Y)`.
  - **`hcomp`.** `transport_comp_le` with:
    - `f` and `g` self-small at their pairs;
    - `v.sourceDefect ≤ β_Y`;
    - closeness in `Q` at the outer pair.

    This gives
    `ρ_XZ + ρ_XY + ρ_YZ + 2β_X + 2β_Y + 2β_Z + r_P(X,Z) + r_P(X,Y) + r_P(Y,Z) + r_Q(X,Z)`,
    and the target is `8·r_Q(X,Z)`.
  - **`hfaithful`.** `transport_reflect_le` gives
    `5β_X + 5β_Y + 2ρ_XY + 2·r_P(X,Y) + r_Q(X,Y)`, and the target is `8·r_P(X,Y)`.
  - **Estimate (7).** `< r_Q(X,Y) + ρ_XY`.
- **At the intended instance.**
  - Matched objects have scales within `1 + o(1)`, and objects joined by a candidate
    within `11/10`.
  - The left sides are about `4.4·r_Q`, `3.1·r_P` and `r_P` plus the small `ρ, β`.
  - `ρ` comes from `repair_spec`'s `d·|model|` bound, and `β` from
    `RelativeFunctorEstimateMatching`.

### `08e96b025` `ArrowCountMedian`: one median application. No defect

`arrowCount = o·k`. The single application is correct:
- **Drift.** `(1 − ζ)·o(π i) ≤ o(i)` and `k(π i) ≤ k(i)` give
  `(1 − ζ)·arrowCount(π i) ≤ arrowCount(i)`. That is the one-sided hypothesis of
  `localRatio_negligible`.
- **Concentration.** Lemma 4.4 gives `arrowCount(i) ≤ (1 + η)·arrowCount(π i)` on a
  conull family.
- **Isotropy.** `k(i) ≤ ((1 + η)/(1 − ζ))·k(π i) < 2·k(π i)` for `η + 2ζ < 1`.
- **Orbit ratio.** Because `k(π i) ≤ k(i)`, `o(i) ≤ (1 + η)·o(π i)`.
- **Splitting at `i` and `ā i`.** `a < (1 − ζ)(o + o')` from `1 + η < 2(1 − ζ)`.

The paper applies Lemma 4.4 twice, to `o_n` and to `k_n`. The product version needs
only the two one-sided inequalities the paper already has, so it is a genuine
simplification.

## R12. Landings 13:36–13:38

### `563dcd0dc` (kt41-bisection-rep-b): Lemma 4.2(4), forward half. Composition defect (C)

**Sound as finite mathematics.**
- **`overlapObject_unique`.** Two candidate overlap arrows out of `X`, each missing
  `< 2m` source points, with `|X| ≥ 4m`, have the same target.
- **Injectivity on targets.** Via `targetDefect`, symmetrically.
- **`exists_perm_of_isClusterCandidate`.** A class-preserving permutation extending
  the targets.
- **`card_hammingDisagreement_representingPatch_le`.** The patch differs from `v`
  only off the glued domain and on objects outside `overlapGood`.

**Defect (C): the wrong frame.** `variable (D : PartialClusterSystem I L)`, the
global-scale system with `D.h`, `D.scale` and `D.size`.
- **No composition.** The chain's frame is `ScaledPartialClusterSystem`: repair,
  groupoid, functor metric, converse half and the assembly's single `Frame`.
  `hrep` must return bisections of that presentation.
- **No producer.** `PartialClusterSystem.improveExists` is produced only for exact
  transitive actions.
- **The mass bound fails.** `card_compl_overlapGood_mul_le` bounds
  `(#bad objects)·h·scale/2` by the total defects. At one global scale this does not
  bound the bad mass `Σ_{bad} |X|`, because components can be far larger than
  `scale`. This is F1's size-spread example.

**Fix, sent to the owner.** Restate for `ScaledPartialClusterSystem`, testing overlap
arrows at `min(scale X, scale Z)`. A bad object `X` with dominant target `Z` then
carries defect `≥ c·h·|X|`:
- if `|Z| < |X|/2`, the source defect is `≥ |X|/2`;
- otherwise the pair scale is `≳ scale X/2`.

So the bad mass is `≤ C·defects/h`, which is negligible under `hrep`'s domination.

### Other landings. No defect

- **`13382096b` `FixedPointNormalizationScaledBisection`.** The converse half at pair
  scales. `τ X = h·(|X|/18)/2`, so `Σ τ ≤ (h/36)|Y|`.
- **`cd55e0d7d` `ComponentCountingRetainedMatchingNegligible`.** Shifted-index
  asymptotics of the retained matching error and the unmatched weight, from negligible
  removed and empty-component mass. With `withDistinguished` it applies to every
  compressor.

## R13. Landings 13:40–13:41. No defect

- **`db9f4260c` `CentralizerNormalizationPrunedCore`.** Checked by specializing
  `retained_completion_directedCheeger`:
  - The additive inequality from `additiveCheeger_of_edit` has constant
    `γ = cheeger/2` and error `E = b/2`.
  - The cut constant is `c = cheeger/4`.
  - `hsmall` becomes `b·(8·cheeger + 32·|T|) ≤ cheeger²·|C|`, as stated.
  - The core constant is `c/|T| = cheeger/(4|T|)`.
  - The removed mass is `E/(γ − c) = 2b/cheeger`, as in `prunedCore_removed_le`.
- **`9d89ca20e` `ComponentFamilyUniformFields`.** Three transfers to retained sets:
  - `size_tendsTo`, with at most half removed;
  - `locallyMultiplicative`, since a product failure is an ambient failure or an
    image outside `V`, and the removed proportion vanishes uniformly;
  - `labelsInjective`, with collisions at most a quarter and removal at most an
    eighth.

  Freeness is consumed through the collision counts.
- **Coordination note, not a defect.** Two L1 producer routes are on main:
  - kt41-seq-decomp: `9105379d6` Pruning, Completion and Levels, constant `h/(8|T|)`;
  - kt41-g1-alt with kt41-seq-wrapper: `5f364e5f1`, `db9f4260c` and `9d89ca20e`,
    constant `cheeger/(4|T|)`.

  Both are consistent, and one producer suffices.

## R14. Landings 13:42–13:43. No defect

- **`91713c5f5` `SequentialComponentFamilyObjects`** (kt41-seq-decomp).
  - The objects are the components good at the diagonal level, restricted to their
    pruned cores, with completed labels.
  - Four statements fill the `ComponentFamily` fields:
    - `objectAction_expands`: exact directed Cheeger bound `cheeger/(8|T|)`;
    - `objectModel_size`;
    - `objectAction_locallyMultiplicative`, uniform over objects;
    - `objectAction_injOn`, eventually.
  - Inputs: `[Infinite K]`, a symmetric generating `T` and a surjective enumeration.
  - `card_objectAction_disagreement_le` charges label failures to completion
    disagreement plus pruned mass. That is the compatibility-failure count the block
    actions need.
- **`9a752011f` `CountingEndgameRestrict`** (kt41-counting-endgame).
  - The inclusion of a restricted presentation is full, faithful and injective on
    objects.
  - **(2).** `(1 − ζ)·|orbit(J X)| ≤ |orbit(J X) ∩ im J| ≤ |orbit X| ≤ |orbit(F X)|`.
    The last orbit is taken in the restricted target, so it is `≤` the ambient
    `o_n(i)`, which implies the paper's (2).
  - **(3).** `k(J X) = k(X) ≤ k(F X)`, by full-and-faithful `J` and faithful `F`.
  - Together these give the count hypotheses of `exists_bisection_lift` from ambient
    cleanliness and ratio bounds.

## R15. Landings 13:44–13:45. No defect

- **`205fdf5b4` `MedianVertexFormBlocks`** (kt41-median-vertex). Lemma 4.4 for
  embedded blocks.
  - Objects weigh `|E.model i|`. The observable is `f ≥ 1`, read through
    `blockObject` and set to `1` on uncovered vertices.
  - `blockRatio_negligible` takes `hone`, `hbad`, `hout` and `hmiss` for every
    `q ∈ C.compressors`. It is the every-compressor form that trap (B) requires.
  - The `Γ` generators enter through negligible self-bridge missing mass.
  - `sum_abs_sub_negligible_of_closure` extends the label estimates to a symmetric
    generating `T`.
  - The one-sided form `f(π i) ≤ (1 + κ)·f(i)` matches the paper.
- **`ced0eb674` `CentralizerBisectionRepresentationDefects`.** Block-local charging for
  an almost-centralizer `q`.
  - `localObstruction` sums over blocks to the global commutation and compatibility
    counts, which fixes the double counting of `card_equivarianceDefect_bridge_le`.
  - Bridge defects are at most the per-label missing mass plus local obstructions.
  - `sourceDefect_bridge_le_of_reseparation` is Lemma 2.4's dominant cell at a
    vanishing scale: the source is almost invariant and the majority condition holds.
  - `eq_of_isClusterCandidate_bridge` gives at most one candidate bridge per block.
  - `mul_scale_le_of_not_isClusterCandidate` bounds the defect of a non-candidate
    below.
  - It is stated on an abstract `BlockEmbedding` with an explicit scale. So it serves a
    per-object restatement of the forward half, and it supplies the per-block defect
    lower bound that (C)'s mass bound needs.

## R16. `673943642` (kt41-hamming): step 9 rebased on the raw map. No defect

- **References.** The references are now the relative functor's raw maps:
  `sandwich (bridge q⁻¹ (π i) i) (bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)) (β.arrow (π i))`.
  They realize `q⁻¹·β.patch·q` on their source (`realizesOn_sandwich_bridge_inv`),
  so `hc` holds with no condition.
- **`hnear` from estimate (7).** Take the cluster identity `F[b_{π i}] = [a_i]` and a
  representative `θ` of the image class. Then:
  - `twoSided(a_i, θ) < r_Q(i, ā i)`, since they are in the same cluster;
  - `twoSided(θ, raw) < r_Q + ρ` (`twoSidedDisagreement_sandwich_lt_of_ofRep_eq`).

  So `hnear` holds with `sc i ≈ r_Q + ⌈ρ/2⌉`, and `hroom` holds for small `h_n, d_n`.
- **`sum_stepNineBudget_le`.** With `π` injective on `good`, every term is a
  controlled total:
  - retained bridge missing masses, by the retained matching error
    (`RelativeFunctorEstimateMatching`, `ComponentCountingRetainedMatchingNegligible`);
  - arrow defects of `α` and `β`, candidates at `h_n → 0`, at most `O(h_n|Y|)`;
  - label and word compatibility failures;
  - the localized conjugation failures of `q` and `q⁻¹`, whose sum is at most the
    ambient failures of the relations `t s t⁻¹ = w_s`.
- **Instantiation note.** The second bridge term is small only when
  `β.objEquiv (π i) = π (α.objEquiv i)`, i.e. `b_{π i}` lands at `π(ā i)`. The
  counting endgame selects `good` inside that set, as the paper's `E_n` does.

## Named statements in the chain without a producer

- `seqNormalizes_distinguished_of_kazhdan`: pinned name only; its file is absent.
- `ComponentFamily`: no producer yet (L1).
- `PartialClusterSystem.improveExists` at approximate component actions: only
  `ofExactTransitiveKazhdanActions` produces it. Needs F1 and F2.

No section variable hides a hypothesis in `NormalizationProducer`,
`FixedPointNormalizationSummation` or `CentralizerNormalizationImprove`.

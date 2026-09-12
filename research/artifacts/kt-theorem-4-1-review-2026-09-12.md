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
| R4 | gap-1 improvement `2458bbc45` | statement shape right; **F2 (new): no threshold lowering**; F1 known (L2) |
| R5 | counting modules `b30597455` | match the counting and Lemma 4.4; a fixed clamp level suffices |
| R6 | relative-functor finite lemmas | match the sentences of the proof of Lemma 4.3 |
| R7 | scale-defect fix | real on both halves, conditional on L1, F1 and F2 |

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
- Both arrows are almost equivariant for the word labels `α(w_s)` of `t s t⁻¹`, not
  for `α(s)`. The reference comes from `u a u⁻¹`, and `u a u⁻¹` is equivariant for the
  transported labels.
- So `actY C` must be the word labels, and `hexp` is tagged expansion of the
  word-labelled graph on `Q_{π i}`.
- That expansion follows from the Cheeger bound of `P_i = u Q_i` with transported
  labels, minus the edit budget `δ + ξ`. It holds at scales above a multiple of
  budget/`h_Γ`, which is why `x C` carries `2·editBudget`. The exact Cheeger input is
  kt41-g1-alt's L1.

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

## Named statements in the chain without a producer

- `seqNormalizes_distinguished_of_kazhdan`: pinned name only; its file is absent.
- `ComponentFamily`: no producer yet (L1).
- `PartialClusterSystem.improveExists` at approximate component actions: only
  `ofExactTransitiveKazhdanActions` produces it. Needs F1 and F2.

No section variable hides a hypothesis in `NormalizationProducer`,
`FixedPointNormalizationSummation` or `CentralizerNormalizationImprove`.

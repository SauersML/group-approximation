# Component counting and Kun–Thom Theorem 4.1

Lane `kt-norm-counting`, 2026-09-12. Campaign: an unconditional Lean proof that
some finitely generated group is surjunctive and not sofic (Bowen–Chapman,
arXiv:2511.06586, Problem 1.1). The one analytic input is Kun–Thom,
arXiv:2608.06222v3, Theorem 4.1:

> Let Γ be an infranormal subgroup of G, and suppose that both Γ and G have
> Kazhdan's property (T). If σ:G→𝒮_𝒰 is a sofic representation, then
> C_{𝒮_𝒰}(σ(Γ)) is normalized by σ(G).

## 1. The heuristic tested

Fix a compressor t ∈ P_Γ, put Γ' = tΓt⁻¹ ≤ Γ and u = σ(t). The heuristic reads:

1. property (T) splits every model into Γ-expander components plus a small set;
2. u carries Γ-components onto Γ'-components;
3. Γ'-components refine Γ-components;
4. a refinement with the same size spectrum is the original partition;
5. same components imply normalization.

## 2. Verdict

**Steps 1–4 are sound, and they are Kun–Thom's Proposition 3.1.** That is
the partition-level statement that the Γ-components and their u-translates agree
up to o(|Y_n|). Its content is the diagonal fixed-point algebra
D_𝒰^{σ(Γ)}, and it yields Theorem C.

**Step 5 fails.** Let q commute with σ(Γ), put c = u q u⁻¹, and take γ ∈ Γ.
Since σ(γ) preserves every Γ-component, c and σ(γ) c σ(γ)⁻¹ induce the same
permutation of components. Any failure of c to commute with σ(γ) therefore
happens *inside* components, at the level of intertwiners between components.
No partition-level count can see it. The lamp witness of Theorem A is exactly of
this kind: σ(γ)ρ(a_{tΓ})σ(γ)⁻¹ = ρ(a_{γtΓ}) differs from ρ(a_{tΓ}) almost
everywhere, while both permute the same components the same way.

So a proof of normalization needs the counting of §4 of Kun–Thom. Its objects
are the orbit sizes o_n(i) and isotropy orders k_n(i) of the cluster groupoid of
allowed partial bijections between Γ-components. The cluster groupoid, and the
repair theorem that produces it, cannot be bypassed.

## 3. The quantitative step that does carry over: median amplification

Kun–Thom's Lemma 4.4 upgrades one-sided inequalities f_n(π i) ≤ (1+κ_n) f_n(i)
to ratios tending to 1 in component-weight measure. Its vertex form over an
expander decomposition of σ(G) is:

* Let φ be an observable, m_B a median of φ on the ambient component B, and
  ψ = clamp(φ − m_B, [−M, M]).
* Conservation. For a permutation p, ∑|ψ(p y) − ψ(y)| = 2 ∑ max(ψ(p y) − ψ(y), 0).
* One-sided drift. If φ(p y) ≤ φ(y) + κ off a set E, then the total rise is at most
  κ|Y| + 2M·|E ∪ crossings(p)|.
* Pinning. On components with Cheeger constant h,
  h ∑|ψ| ≤ (edge variation of ψ).
* Markov. |{y : |φ(y) − m_B| ≥ M}| ≤ M⁻¹ ∑|ψ|.

**The clamp is necessary, and so is (T) for G.** Consider a cycle of length N
carrying an observable with values in [0, log N]. Let it drop by δ at almost every
step, and jump back up by at most log N once every (log N)/δ steps. The drift is
one-sided except on a set of density δ/log N → 0, yet the drops occupy almost
every vertex. Integrating φ itself cannot exclude this, because the exceptional
mass is multiplied by the range log N. What rules it out is concentration of the
clamped observable at its median on uniformly expanding ambient components,
which is property (T) of G.

## 4. Representations: free, not merely injective

Kun–Thom v3, Definition 2.1: "A homomorphism σ:G→𝒮𝒰 is a sofic
representation if tr(σ(g))=0 for every g≠1." The landed
`HasSoficCentralizerNormalization` quantifies over every injective
representation. That is stronger than Theorem 4.1, and the repo's Kun
decomposition is proved only for sofic approximations. The campaign target is now
kt-norm-repo's sequential free Prop `HasSequentialCentralizerNormalization`.

## 5. Lean

`GroupApproximation/KunThom/ComponentCountingNormalizationMedian.lean`, namespace
`GroupApproximation.ComponentCountingNormalization`:

- the clamp: `clampTo`, `clampTo_le_add`, `abs_clampTo_eq`;
- median transfer: `isMedian_comp_monotone`;
- the observable: `clampedDeviation`, `clampedDeviation_isMedian_on_block`;
- label estimates: `sum_abs_clamped_sub_le_of_oneSided`, `sum_abs_clamped_sub_le_of_eqOff`;
- Markov and drops: `card_deviation_mul_le`, `card_drop_le`;
- edge edits: `edgeVariation_mul_add`, `clamped_modelVariation_le`;
- pinning: `clamped_pinning`;
- assembly: `deviation_negligible` and `drop_negligible`.

They reuse `permutation_conservation_abs`, `FiniteMultiGraph.coarea_mul`,
`EdgeEditWitness.targetVariation_le_unmatchedCount` and
`generatorGraph_edgeVariation_le`. The statements are finite, or asymptotic along
`Negligible`, and involve no ultrafilter.

The same lane owns the finite groupoid counting of §4's endgame:

- the one-sided inequalities for o_n and k_n from a faithful object-injective functor on clean components;
- the splitting bound |Ω| ≥ (1−ζ)(|Ω₁|+|Ω₂|);
- isotropy index below 2 forcing a hom-set bijection.

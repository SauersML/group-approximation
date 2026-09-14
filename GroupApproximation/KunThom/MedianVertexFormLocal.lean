import GroupApproximation.KunThom.MedianVertexForm

/-!
# Kun–Thom Lemma 4.4 for the local criterion data

This file specializes the vertex form of Kun and Thom's one-sided median lemma
(arXiv:2608.06222v3, Lemma 4.4; `MedianVertexForm.failingWeight_negligible`) to
`LocalCriterionData`: a compression setup, a sofic approximation of `G`, an
expander decomposition of its restriction to `Γ` and an ambient expander
decomposition for the labels `generatorsΓ ∪ compressors ∪ compressors⁻¹`.

The objects are the `Γ`-components (`gammaObject`).  A natural observable `f`
of the objects is given, together with, for every compressor `q`, a matching
`π q n` of objects on a domain `Dom q n` and a family `Bad q n` of exceptional
objects.  The hypotheses are exactly those of Lemma 4.4:

* one-sided inequalities `(1 - ζ n) f (π q n i) ≤ f i` for `i ∈ Dom q n \ Bad q n`,
  with `0 ≤ ζ n ≤ 1/2` and `ζ` vanishing;
* negligible weight outside `Dom q n` and of `Bad q n`, and a negligible matching
  leak of the compressor permutation.

The label estimates are discharged here.  Embedded generators of `Γ` preserve
the observable off the crossings of the `Γ`-components, compressors drift
one-sidedly off the vertex exceptional set, and inverse compressors are
approximate inverses.

* `localLogObservable_negligible`: for every `M > 0`, the matched objects whose
  logarithmic observable changes by more than `2M` have negligible weight.
* `localRatio_negligible`: for a positive observable and every `η > 0`, the
  matched objects with `(1 + η) f i < f (π q n i)` or `(1 + η) f (π q n i) < f i`
  have negligible weight.  These are the ratios of equation (4) of Kun and Thom,
  tending to `1` in component-weight measure.
-/

namespace GroupApproximation
namespace MedianVertexForm

open scoped BigOperators
open ComponentCountingNormalization

theorem objectVertices_mono {Y : FiniteModel} {I : Type*} [DecidableEq I] (obj : Y → I)
    {J J' : Finset I} (h : J ⊆ J') : objectVertices obj J ⊆ objectVertices obj J' := by
  intro y hy
  rw [mem_objectVertices] at hy ⊢
  exact h hy

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]

/-- The `Γ`-component through a vertex, as an object. -/
def gammaObject (D : LocalCriterionData G Γ J) (n : ℕ) :
    D.approximation.model n → BlockIndex (D.gammaDecomposition.blocks n) :=
  blockIndexOf (D.gammaDecomposition.blocks n)

/-- The clamped label variation of the logarithmic observable of the
`Γ`-components, centred at its componentwise median on the ambient components. -/
noncomputable def labelVariation (D : LocalCriterionData G Γ J)
    (f : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) → ℕ) (M : ℝ) (g : G) (n : ℕ) : ℝ :=
  ∑ x : D.approximation.model n,
    |clampedDeviation (D.ambientDecomposition.blocks n)
        (logMedian D.ambientDecomposition (gammaObject D) f n)
        (fun y ↦ logObservable (f n) (gammaObject D n y)) M (D.approximation.map n g x) -
      clampedDeviation (D.ambientDecomposition.blocks n)
        (logMedian D.ambientDecomposition (gammaObject D) f n)
        (fun y ↦ logObservable (f n) (gammaObject D n y)) M x|

theorem compressor_mem_ambientGenerators (D : LocalCriterionData G Γ J) {q : G}
    (hq : q ∈ D.setup.compressors) : q ∈ D.setup.ambientGenerators := by
  classical
  unfold CompressionSetup.ambientGenerators
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)

theorem embedΓ_mem_ambientGenerators (D : LocalCriterionData G Γ J) {s : Γ}
    (hs : s ∈ D.setup.generatorsΓ) : D.setup.embedΓ s ∈ D.setup.ambientGenerators := by
  classical
  unfold CompressionSetup.ambientGenerators
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩))

/-- Embedded generators of `Γ` move the clamped logarithmic observable by a
negligible total amount. -/
theorem gammaLabelVariation_negligible (D : LocalCriterionData G Γ J)
    (f : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) → ℕ) {M : ℝ} (hM : 0 ≤ M)
    (s : Γ) (hs : s ∈ D.setup.generatorsΓ) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ))
      (labelVariation D f M (D.setup.embedΓ s)) := by
  have hinner : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((wordCrossing (D.gammaDecomposition.blocks n)
        (D.approximation.map n (D.setup.embedΓ s))).card : ℝ) := by
    have h := D.gammaDecomposition.almost_invariant s hs
    exact h
  have hinv : ∀ n (y : D.approximation.model n),
      y ∉ wordCrossing (D.gammaDecomposition.blocks n)
        (D.approximation.map n (D.setup.embedΓ s)) →
      logObservable (f n) (gammaObject D n (D.approximation.map n (D.setup.embedΓ s) y)) =
        logObservable (f n) (gammaObject D n y) := by
    intro n y hy
    have hblock : (D.gammaDecomposition.blocks n).block
        (D.approximation.map n (D.setup.embedΓ s) y) = (D.gammaDecomposition.blocks n).block y := by
      by_contra hne
      exact hy ((mem_wordCrossing (D.gammaDecomposition.blocks n)
        (D.approximation.map n (D.setup.embedΓ s)) y).mpr hne)
    exact congrArg (logObservable (f n)) (blockIndexOf_eq_of_block_eq _ hblock)
  exact clampedLabel_negligible_of_eqOff D.ambientDecomposition
    (logMedian D.ambientDecomposition (gammaObject D) f)
    (fun n y ↦ logObservable (f n) (gammaObject D n y)) hM (D.setup.embedΓ s)
    (fun n ↦ wordCrossing (D.gammaDecomposition.blocks n)
      (D.approximation.map n (D.setup.embedΓ s)))
    hinner hinv
    (D.ambientDecomposition.almost_invariant _ (embedΓ_mem_ambientGenerators D hs))

/-- Compressors with one-sided object inequalities off negligible exceptional
families move the clamped logarithmic observable by a negligible total amount. -/
theorem compressorLabelVariation_negligible (D : LocalCriterionData G Γ J)
    (f : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) → ℕ) {M : ℝ} (hM : 0 ≤ M)
    (q : G) (hq : q ∈ D.setup.compressors)
    (π : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) →
      BlockIndex (D.gammaDecomposition.blocks n))
    (Dom Bad : ∀ n, Finset (BlockIndex (D.gammaDecomposition.blocks n)))
    (ζ : ℕ → ℝ) (hζ : ∀ n, 0 ≤ ζ n) (hζ₂ : ∀ n, ζ n ≤ 1 / 2) (hζv : Vanishing ζ)
    (hdrift : ∀ n, ∀ i ∈ Dom n, i ∉ Bad n → (1 - ζ n) * (f n (π n i) : ℝ) ≤ f n i)
    (houtside : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((outsideVertices (gammaObject D n) (Dom n)).card : ℝ))
    (hbad : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((objectVertices (gammaObject D n) (Bad n)).card : ℝ))
    (hleak : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((matchLeak (gammaObject D n) (D.approximation.map n q) (π n) (Dom n)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ))
      (labelVariation D f M q) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (D.approximation.model n) := fun n ↦ Nat.cast_nonneg _
  have hE : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((vertexExceptional (gammaObject D n) (D.approximation.map n q) (π n) (Dom n)
        (Bad n)).card : ℝ) := by
    refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
      ((houtside.add hbad).add hleak)
    exact_mod_cast card_vertexExceptional_le (gammaObject D n) (D.approximation.map n q) (π n)
      (Dom n) (Bad n)
  have hdrift' : ∀ n (y : D.approximation.model n),
      y ∉ vertexExceptional (gammaObject D n) (D.approximation.map n q) (π n) (Dom n) (Bad n) →
      logObservable (f n) (gammaObject D n (D.approximation.map n q y)) ≤
        logObservable (f n) (gammaObject D n y) + 2 * ζ n := by
    intro n y hy
    exact drift_of_not_mem_vertexExceptional (gammaObject D n) (D.approximation.map n q) (π n)
      (Dom n) (Bad n) (logObservable (f n)) (2 * ζ n)
      (fun i hi hbi ↦ logCut_le_add_of_mul_le (hζ n) (hζ₂ n) (hdrift n i hi hbi)) y hy
  exact clampedLabel_negligible_of_oneSided D.ambientDecomposition
    (logMedian D.ambientDecomposition (gammaObject D) f)
    (fun n y ↦ logObservable (f n) (gammaObject D n y)) hM (fun n ↦ 2 * ζ n)
    (fun n ↦ mul_nonneg zero_le_two (hζ n)) (Vanishing.const_mul 2 hζv) q
    (fun n ↦ vertexExceptional (gammaObject D n) (D.approximation.map n q) (π n) (Dom n) (Bad n))
    hE hdrift' (D.ambientDecomposition.almost_invariant q (compressor_mem_ambientGenerators D hq))

/-- **Kun–Thom Lemma 4.4 for the local criterion data, logarithmic form.**  If
every compressor satisfies one-sided inequalities between matched `Γ`-components
off negligible exceptional families, then for every compressor and every `M > 0`
the matched components whose logarithmic observable changes by more than `2M`
have negligible weight. -/
theorem localLogObservable_negligible (D : LocalCriterionData G Γ J)
    (f : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) → ℕ)
    (π : G → ∀ n, BlockIndex (D.gammaDecomposition.blocks n) →
      BlockIndex (D.gammaDecomposition.blocks n))
    (Dom Bad : G → ∀ n, Finset (BlockIndex (D.gammaDecomposition.blocks n)))
    (ζ : ℕ → ℝ) (hζ : ∀ n, 0 ≤ ζ n) (hζ₂ : ∀ n, ζ n ≤ 1 / 2) (hζv : Vanishing ζ)
    (hdrift : ∀ q ∈ D.setup.compressors, ∀ n, ∀ i ∈ Dom q n, i ∉ Bad q n →
      (1 - ζ n) * (f n (π q n i) : ℝ) ≤ f n i)
    (houtside : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((outsideVertices (gammaObject D n) (Dom q n)).card : ℝ))
    (hbad : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((objectVertices (gammaObject D n) (Bad q n)).card : ℝ))
    (hleak : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((matchLeak (gammaObject D n) (D.approximation.map n q) (π q n) (Dom q n)).card : ℝ))
    {M : ℝ} (hM : 0 < M) (q : G) (hq : q ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((objectVertices (gammaObject D n) ((Dom q n).filter fun i ↦
        2 * M < |logObservable (f n) (π q n i) - logObservable (f n) i|)).card : ℝ) := by
  have hcomp : ∀ q' ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ))
        (labelVariation D f M q') := fun q' hq' ↦
    compressorLabelVariation_negligible D f hM.le q' hq' (π q') (Dom q') (Bad q') ζ hζ hζ₂ hζv
      (hdrift q' hq') (houtside q' hq') (hbad q' hq') (hleak q' hq')
  have hlabel : ∀ t ∈ D.setup.ambientGenerators,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ))
        (labelVariation D f M t) := by
    intro t ht
    classical
    simp only [CompressionSetup.ambientGenerators, Finset.mem_union, Finset.mem_image] at ht
    rcases ht with (ht | ht) | ht
    · obtain ⟨s, hs, rfl⟩ := ht
      exact gammaLabelVariation_negligible D f hM.le s hs
    · exact hcomp t ht
    · obtain ⟨q', hq', rfl⟩ := ht
      exact clampedLabel_negligible_inv D.ambientDecomposition
        (logMedian D.ambientDecomposition (gammaObject D) f)
        (fun n y ↦ logObservable (f n) (gammaObject D n y)) hM.le q' (hcomp q' hq')
  exact failingWeight_negligible D.ambientDecomposition (gammaObject D) f hM hlabel q (π q)
    (Dom q) (D.ambientDecomposition.almost_invariant q (compressor_mem_ambientGenerators D hq))
    (hleak q hq)

/-- **Kun–Thom Lemma 4.4 for the local criterion data, ratio form.**  Under the
hypotheses of `localLogObservable_negligible`, for a positive observable and every
`η > 0`, the matched components whose observables differ by more than the factor
`1 + η` have negligible weight. -/
theorem localRatio_negligible (D : LocalCriterionData G Γ J)
    (f : ∀ n, BlockIndex (D.gammaDecomposition.blocks n) → ℕ) (hf : ∀ n i, 1 ≤ f n i)
    (π : G → ∀ n, BlockIndex (D.gammaDecomposition.blocks n) →
      BlockIndex (D.gammaDecomposition.blocks n))
    (Dom Bad : G → ∀ n, Finset (BlockIndex (D.gammaDecomposition.blocks n)))
    (ζ : ℕ → ℝ) (hζ : ∀ n, 0 ≤ ζ n) (hζ₂ : ∀ n, ζ n ≤ 1 / 2) (hζv : Vanishing ζ)
    (hdrift : ∀ q ∈ D.setup.compressors, ∀ n, ∀ i ∈ Dom q n, i ∉ Bad q n →
      (1 - ζ n) * (f n (π q n i) : ℝ) ≤ f n i)
    (houtside : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((outsideVertices (gammaObject D n) (Dom q n)).card : ℝ))
    (hbad : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((objectVertices (gammaObject D n) (Bad q n)).card : ℝ))
    (hleak : ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ((matchLeak (gammaObject D n) (D.approximation.map n q) (π q n) (Dom q n)).card : ℝ))
    {η : ℝ} (hη : 0 < η) (q : G) (hq : q ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ((objectVertices (gammaObject D n) ((Dom q n).filter fun i ↦
        (1 + η) * (f n i : ℝ) < f n (π q n i) ∨
          (1 + η) * (f n (π q n i) : ℝ) < f n i)).card : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (D.approximation.model n) := fun n ↦ Nat.cast_nonneg _
  have hη₁ : (0 : ℝ) < 1 + η := by linarith
  have hM : 0 < Real.log (1 + η) / 2 := by
    have hlog := Real.log_pos (by linarith : (1 : ℝ) < 1 + η)
    linarith
  have hlog := localLogObservable_negligible D f π Dom Bad ζ hζ hζ₂ hζv hdrift houtside hbad
    hleak hM q hq
  refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_) hlog
  have hsub : (Dom q n).filter (fun i ↦
      (1 + η) * (f n i : ℝ) < f n (π q n i) ∨ (1 + η) * (f n (π q n i) : ℝ) < f n i) ⊆
      (Dom q n).filter (fun i ↦
        2 * (Real.log (1 + η) / 2) < |logObservable (f n) (π q n i) - logObservable (f n) i|) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hc : |logObservable (f n) (π q n i) - logObservable (f n) i| ≤ Real.log (1 + η) := by
      linarith
    have hc' : |logObservable (f n) i - logObservable (f n) (π q n i)| ≤ Real.log (1 + η) := by
      rw [abs_sub_comm]
      exact hc
    have h₁ := le_exp_mul_of_abs_logCut_sub_le (hf n (π q n i)) (hf n i) hc
    have h₂ := le_exp_mul_of_abs_logCut_sub_le (hf n i) (hf n (π q n i)) hc'
    rw [Real.exp_log hη₁] at h₁ h₂
    rcases hi.2 with h | h
    · linarith
    · linarith
  exact_mod_cast Finset.card_le_card (objectVertices_mono (gammaObject D n) hsub)

end MedianVertexForm
end GroupApproximation

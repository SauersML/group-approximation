import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrameSteps
import GroupApproximation.KunThom.SequentialComponentFamilyKazhdan
import GroupApproximation.Criterion.LocalCriterion

/-!
# Decompositions of the per-compressor assembly

`seqNormalizes_of_compressor_of_frameSteps` needs decomposition data with
retained components, a generator defect, and a Kazhdan pair on the generators.
This module builds them from the landed sequential decompositions.

* `CompressorDecomposition C A`: for a compression setup `C` of `Γ`, an expander
  decomposition of `A` restricted along `C.embedΓ` on the generators of `C`, an
  ambient expander decomposition of `A` on the ambient generators, and a
  surjective enumeration of `Γ`.  `exists_compressorDecomposition` produces one
  when `G` is countable and `G` and `Γ` have property `(T)`.
  `CompressorDecomposition.toLocal` is the corresponding `LocalCriterionData`.
* `retainedOfDecomposition`, `CompressorDecomposition.retained`: the objects of
  `SequentialComponentFamily.componentFamily`, placed by `objectEmbedding`, with
  negligible uncovered mass and negligible compatibility failures.
* `generatorDefect R v`: the commutation defect of `v` with the models of the
  generators, plus the normalized uncovered mass and compatibility failures.  It
  vanishes when `v` almost commutes with the models of the generators
  (`generatorDefect_vanishing`).
* `exists_kazhdanPair_retained`: the generators carry a Kazhdan pair with
  constant at most `1`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open SequentialComponentFamily

open Classical in
/-- The retained components of an expander decomposition of `A` restricted along
`ι`: the objects of the sequential component family, placed as blocks of the
models. -/
noncomputable def retainedOfDecomposition {G : Type} [Group G] {K : Type} [Group K]
    [Infinite K] {A : SoficApproximation G} {ι : K →* G} {hι : Function.Injective ι}
    {SΓ : Finset K} (D : ExpanderDecomposition (A.comap ι hι) SΓ) (hone : (1 : K) ∈ SΓ)
    (hsymm : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ) (hgen : Subgroup.closure (SΓ : Set K) = ⊤)
    (enum : ℕ → K) (henum : Function.Surjective enum) :
    RetainedComponents A K ι where
  data :=
    { generators := SΓ
      one_mem := hone
      generate := hgen
      family := componentFamily D hsymm hgen ⟨1, hone⟩ enum henum
      fintypeIndex := fun n ↦ inferInstanceAs (Fintype (objectIndex D enum n))
      embed := fun n i ↦ objectEmbedding D ⟨1, hone⟩ enum n i
      embed_injective := fun n i ↦ objectEmbedding_injective D ⟨1, hone⟩ enum n i
      embed_disjoint := fun n ↦ (objectBlocks D ⟨1, hone⟩ enum n).embed_disjoint }
  uncovered_negligible := uncovered_objectBlocks_negligible D hsymm hgen ⟨1, hone⟩ enum
  compat_negligible := fun s ↦ compatFailure_sum_negligible D hsymm hgen ⟨1, hone⟩ enum s

/-- Decomposition data for a compression setup `C` of `Γ` over a sofic
approximation `A`. -/
structure CompressorDecomposition {G : Type} [Group G] {Γ : Subgroup G}
    (C : CompressionSetup G ↥Γ PUnit.{1}) (A : SoficApproximation G) where
  gamma : ExpanderDecomposition (A.comap C.embedΓ C.embedΓ_injective) C.generatorsΓ
  ambient : ExpanderDecomposition A C.ambientGenerators
  enum : ℕ → ↥Γ
  enum_surjective : Function.Surjective enum

/-- The retained components of a decomposition. -/
noncomputable def CompressorDecomposition.retained {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) : RetainedComponents A ↥Γ C.embedΓ :=
  retainedOfDecomposition D.gamma C.generatorsΓ_one C.generatorsΓ_symmetric
    C.generatorsΓ_generate D.enum D.enum_surjective

/-- The local criterion data of a decomposition. -/
def CompressorDecomposition.toLocal {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) : LocalCriterionData G ↥Γ PUnit.{1} where
  setup := C
  approximation := A
  gammaDecomposition := D.gamma
  ambientDecomposition := D.ambient

/-- **Decompositions from property `(T)`.** -/
theorem exists_compressorDecomposition {G : Type} [Group G] [Countable G] {Γ : Subgroup G}
    [Infinite ↥Γ] (hTG : HasKazhdanPropertyT.{0, 0} G) (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1}) (A : SoficApproximation G) :
    Nonempty (CompressorDecomposition C A) := by
  haveI : Infinite G := Infinite.of_injective C.embedΓ C.embedΓ_injective
  obtain ⟨D⟩ := KunFixedDecomposition.expanderDecomposition hTΓ C.generatorsΓ
    C.generatorsΓ_one C.generatorsΓ_symmetric C.generatorsΓ_generate
    (A.comap C.embedΓ C.embedΓ_injective)
  obtain ⟨DG⟩ := KunFixedDecomposition.expanderDecomposition hTG C.ambientGenerators
    C.ambientGenerators_one C.ambientGenerators_symmetric C.ambientGenerators_generate A
  obtain ⟨enum, henum⟩ := exists_surjective_nat ↥Γ
  exact ⟨⟨D, DG, enum, henum⟩⟩

/-- The generator defect of a sequence of permutations: its normalized
commutation defect with the models of the generators, plus the normalized
uncovered mass and compatibility failures of the retained components. -/
noncomputable def generatorDefect {G : Type} [Group G] {K : Type} [Group K]
    {A : SoficApproximation G} {ι : K →* G} (R : RetainedComponents A K ι)
    (v : ∀ n, Equiv.Perm (A.model n)) (n : ℕ) : ℝ :=
  (∑ s ∈ R.data.generators,
      hammingDistance (A.model n) (v n * A.map n (ι s)) (A.map n (ι s) * v n)) +
    ((R.data.embedding n).uncovered.card : ℝ) / Fintype.card (A.model n) +
    ∑ s : ↥R.data.generators,
      (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) / Fintype.card (A.model n)

/-- The generator defect of a sequence almost commuting with the models of the
generators is nonnegative and vanishes. -/
theorem generatorDefect_vanishing {G : Type} [Group G] {K : Type} [Group K]
    {A : SoficApproximation G} {ι : K →* G} (R : RetainedComponents A K ι)
    (v : ∀ n, Equiv.Perm (A.model n)) (hv : ∀ s ∈ R.data.generators, A.AlmostCommutes v (ι s)) :
    (∀ n, 0 ≤ generatorDefect R v n) ∧ Vanishing (generatorDefect R v) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact Finset.sum_nonneg fun _ _ ↦ hammingDistance_nonnegative _ _ _
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact Finset.sum_nonneg fun _ _ ↦
        div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hcomm : Vanishing fun n ↦ ∑ s ∈ R.data.generators,
        hammingDistance (A.model n) (v n * A.map n (ι s)) (A.map n (ι s) * v n) :=
      Vanishing.sum R.data.generators
        (fun s n ↦ hammingDistance (A.model n) (v n * A.map n (ι s)) (A.map n (ι s) * v n))
        fun s hs ↦ hv s hs
    have hcompat : Vanishing fun n ↦ ∑ s : ↥R.data.generators,
        (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) /
          Fintype.card (A.model n) :=
      Vanishing.sum Finset.univ
        (fun s n ↦ (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) /
          Fintype.card (A.model n))
        fun s _ ↦ R.compat_negligible s
    exact (hcomm.add R.uncovered_negligible).add hcompat

/-- **A Kazhdan pair on the generators.** -/
theorem exists_kazhdanPair_retained {G : Type} [Group G] {K : Type} [Group K]
    {A : SoficApproximation G} {ι : K →* G} (hTK : HasKazhdanPropertyT.{0, 0} K)
    (R : RetainedComponents A K ι)
    (hsymm : ∀ g ∈ R.data.generators, g⁻¹ ∈ R.data.generators) :
    ∃ (Q : Finset K) (κ : ℝ), IsKazhdanPair.{0, 0} K Q κ ∧
      Q ⊆ R.data.generators ∧ κ ≤ 1 := by
  obtain ⟨κ, hκ, hκone⟩ :=
    exists_kazhdanPair_on_generators hTK R.data.generators hsymm R.data.generate
  exact ⟨R.data.generators, κ, hκ, Finset.Subset.rfl, hκone⟩

end CompressorNormalizationAssembly
end GroupApproximation

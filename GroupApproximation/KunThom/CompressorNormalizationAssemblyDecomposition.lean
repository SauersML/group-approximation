import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrameSteps
import GroupApproximation.KunThom.SequentialComponentFamilyKazhdan
import GroupApproximation.Criterion.LocalCriterion

/-!
# Decompositions of the per-compressor assembly

`seqNormalizes_of_compressor_of_frameSteps` needs decomposition data with
retained components, a generator defect, and a Kazhdan pair on the generators.
This module builds them from the landed sequential decompositions.

* `CompressorDecomposition C A`: for a compression setup `C` of `Γ`, an expander
  decomposition of `A|Γ` on the generators of `C`, an ambient expander
  decomposition of `A` on the ambient generators, and a surjective enumeration of
  `Γ`.  `exists_compressorDecomposition` produces one when `G` is countable and
  `G` and `Γ` have property `(T)`.
* `retainedOfDecomposition`, `CompressorDecomposition.retained`: the objects of
  `SequentialComponentFamily.componentFamily`, placed by `objectEmbedding`, with
  negligible uncovered mass and negligible compatibility failures.
* `generatorDefect R v`: the commutation defect of `v` with the models of the
  generators, plus the normalized uncovered mass and compatibility failures.  It
  vanishes when `v` almost commutes with `A(Γ)` (`generatorDefect_vanishing`).
* `exists_kazhdanPair_retained`: the generators carry a Kazhdan pair with
  constant at most `1`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open SequentialComponentFamily

open Classical in
/-- The retained components of an expander decomposition of `A|Γ`: the objects of
the sequential component family, placed as blocks of the models. -/
noncomputable def retainedOfDecomposition {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {A : SoficApproximation G} {SΓ : Finset ↥Γ}
    (D : ExpanderDecomposition (A.restrict Γ) SΓ) (hone : (1 : ↥Γ) ∈ SΓ)
    (hsymm : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ) (hgen : Subgroup.closure (SΓ : Set ↥Γ) = ⊤)
    (enum : ℕ → ↥Γ) (henum : Function.Surjective enum) :
    RetainedComponents A ↥Γ Γ.subtype where
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
  gamma : ExpanderDecomposition (A.restrict Γ) C.generatorsΓ
  ambient : ExpanderDecomposition A C.ambientGenerators
  enum : ℕ → ↥Γ
  enum_surjective : Function.Surjective enum

/-- The retained components of a decomposition. -/
noncomputable def CompressorDecomposition.retained {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) : RetainedComponents A ↥Γ Γ.subtype :=
  retainedOfDecomposition D.gamma C.generatorsΓ_one C.generatorsΓ_symmetric
    C.generatorsΓ_generate D.enum D.enum_surjective

/-- **Decompositions from property `(T)`.** -/
theorem exists_compressorDecomposition {G : Type} [Group G] [Countable G] {Γ : Subgroup G}
    [Infinite ↥Γ] (hTG : HasKazhdanPropertyT.{0, 0} G) (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1}) (A : SoficApproximation G) :
    Nonempty (CompressorDecomposition C A) := by
  obtain ⟨⟨D⟩, ⟨DG⟩, enum, henum⟩ :=
    exists_sequentialDecompositions hTG hTΓ A C.generatorsΓ C.generatorsΓ_one
      C.generatorsΓ_symmetric C.generatorsΓ_generate C.ambientGenerators
      C.ambientGenerators_one C.ambientGenerators_symmetric C.ambientGenerators_generate
  exact ⟨⟨D, DG, enum, henum⟩⟩

/-- The generator defect of a sequence of permutations: its normalized
commutation defect with the models of the generators, plus the normalized
uncovered mass and compatibility failures of the retained components. -/
noncomputable def generatorDefect {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} (R : RetainedComponents A ↥Γ Γ.subtype)
    (v : ∀ n, Equiv.Perm (A.model n)) (n : ℕ) : ℝ :=
  (∑ s ∈ R.data.generators,
      hammingDistance (A.model n) (v n * A.map n (s : G)) (A.map n (s : G) * v n)) +
    ((R.data.embedding n).uncovered.card : ℝ) / Fintype.card (A.model n) +
    ∑ s : ↥R.data.generators,
      (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) / Fintype.card (A.model n)

/-- The generator defect of an almost-centralizer is nonnegative and vanishes. -/
theorem generatorDefect_vanishing {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} (R : RetainedComponents A ↥Γ Γ.subtype)
    (v : ∀ n, Equiv.Perm (A.model n)) (hv : ∀ γ ∈ Γ, A.AlmostCommutes v γ) :
    (∀ n, 0 ≤ generatorDefect R v n) ∧ Vanishing (generatorDefect R v) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact Finset.sum_nonneg fun _ _ ↦ hammingDistance_nonnegative _ _ _
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact Finset.sum_nonneg fun _ _ ↦
        div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hcomm : Vanishing fun n ↦ ∑ s ∈ R.data.generators,
        hammingDistance (A.model n) (v n * A.map n (s : G)) (A.map n (s : G) * v n) :=
      Vanishing.sum R.data.generators
        (fun s n ↦ hammingDistance (A.model n) (v n * A.map n (s : G)) (A.map n (s : G) * v n))
        fun s _ ↦ hv (s : G) s.2
    have hcompat : Vanishing fun n ↦ ∑ s : ↥R.data.generators,
        (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) /
          Fintype.card (A.model n) :=
      Vanishing.sum Finset.univ
        (fun s n ↦ (∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ)) /
          Fintype.card (A.model n))
        fun s _ ↦ R.compat_negligible s
    exact (hcomm.add R.uncovered_negligible).add hcompat

/-- **A Kazhdan pair on the generators.** -/
theorem exists_kazhdanPair_retained {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (R : RetainedComponents A ↥Γ Γ.subtype)
    (hsymm : ∀ g ∈ R.data.generators, g⁻¹ ∈ R.data.generators) :
    ∃ (Q : Finset ↥Γ) (κ : ℝ), IsKazhdanPair.{0, 0} ↥Γ Q κ ∧
      Q ⊆ R.data.generators ∧ κ ≤ 1 := by
  obtain ⟨κ, hκ, hκone⟩ :=
    exists_kazhdanPair_on_generators hTΓ R.data.generators hsymm R.data.generate
  exact ⟨R.data.generators, κ, hκ, Finset.Subset.rfl, hκone⟩

end CompressorNormalizationAssembly
end GroupApproximation

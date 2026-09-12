import GroupApproximation.KunThom.NormalizationFromCriterion
import GroupApproximation.Criterion.CompressionSetup
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration

/-!
# Producing sequential centralizer normalization from one compressor at a time

`HasSequentialCentralizerNormalization Γ`, the sequential form of Kun--Thom's
Theorem 4.1, reduces to compressors by
`hasSequentialCentralizerNormalization_of_compressorNormalization`.  This module
supplies the finite algebra that turns a single compressor `t` of a Kazhdan
infranormal pair into the data consumed by the compression criterion, and
derives the whole normalization statement from the per-compressor core.

* `exists_finset_compressors_generate`: in a finitely generated group, finitely
  many compressors of an infranormal subgroup already generate the group.
* `CompressionSetup.conjugationEnd` and `CompressionSetup.ofCompressor`: the
  criterion setup `CompressionSetup G ↥Γ PUnit` of one compressor `t`, built
  from a finite symmetric generating set of `Γ` and a finite set of compressors
  containing `t` that generates `G` together with `Γ`.  The commuting factor is
  trivial.
* `hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core`: for a
  countable Kazhdan group `G` with an infranormal Kazhdan subgroup `Γ`, the
  per-compressor core `hcore` gives normalization for every element of `G`.  A
  finite infranormal subgroup is normal, and then every element normalizes with
  no analysis at all; otherwise `Γ` is infinite, both groups are finitely
  generated, and every compressor `t` has a setup `ofCompressor` whose
  distinguished compressor is `t`.

The hypothesis `hcore` is the analytic content of Theorem 4.1, stated per
criterion setup: `SeqNormalizes Γ C.distinguished` for every
`C : CompressionSetup G ↥Γ PUnit` whose embedding is the inclusion of `Γ`.
-/

namespace GroupApproximation

variable {G : Type} [Group G]

/-- **Finitely many compressors generate.**  If `G` is finitely generated and
the compressors of `Γ` generate `G`, then some finite set of compressors
generates `G`. -/
theorem exists_finset_compressors_generate [Group.FG G] {Γ : Subgroup G}
    (hinf : IsInfranormal Γ) :
    ∃ T : Finset G, (∀ q ∈ T, q ∈ compressionSubmonoid Γ) ∧
      Subgroup.closure (T : Set G) = ⊤ := by
  classical
  have htop : Subgroup.closure (compressionSubmonoid Γ : Set G) = ⊤ := hinf
  have hfinite : ∀ x : G, ∃ T : Finset G, (∀ q ∈ T, q ∈ compressionSubmonoid Γ) ∧
      x ∈ Subgroup.closure (T : Set G) := by
    intro x
    have hx : x ∈ Subgroup.closure (compressionSubmonoid Γ : Set G) := by
      rw [htop]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        refine ⟨{y}, fun q hq ↦ ?_, Subgroup.subset_closure (by simp)⟩
        rw [Finset.mem_singleton.mp hq]
        exact hy
    | one =>
        exact ⟨∅, fun q hq ↦ absurd hq (Finset.notMem_empty q), Subgroup.one_mem _⟩
    | mul y z _ _ hy hz =>
        obtain ⟨T₁, hT₁, hy₁⟩ := hy
        obtain ⟨T₂, hT₂, hz₂⟩ := hz
        refine ⟨T₁ ∪ T₂, fun q hq ↦ ?_, Subgroup.mul_mem _ ?_ ?_⟩
        · rcases Finset.mem_union.mp hq with hq₁ | hq₂
          · exact hT₁ q hq₁
          · exact hT₂ q hq₂
        · exact Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_left) hy₁
        · exact Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_right) hz₂
    | inv y _ hy =>
        obtain ⟨T, hT, hyT⟩ := hy
        exact ⟨T, hT, Subgroup.inv_mem _ hyT⟩
  obtain ⟨_, S, _, hS⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  choose f hf₁ hf₂ using hfinite
  refine ⟨S.biUnion f, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨s, _, hqs⟩ := Finset.mem_biUnion.mp hq
    exact hf₁ s q hqs
  · apply top_unique
    rw [← hS, Subgroup.closure_le]
    intro s hs
    have hsub : f s ⊆ S.biUnion f := fun q hq ↦
      Finset.mem_biUnion.mpr ⟨s, Finset.mem_coe.mp hs, hq⟩
    exact Subgroup.closure_mono (Finset.coe_subset.mpr hsub) (hf₂ s)

namespace CompressionSetup

/-- Conjugation by a compressor, as an endomorphism of the compressed
subgroup. -/
def conjugationEnd {Γ : Subgroup G} {q : G} (hq : q ∈ compressionSubmonoid Γ) :
    ↥Γ →* ↥Γ where
  toFun g := ⟨q * (g : G) * q⁻¹, mem_compressionSubmonoid.mp hq (g : G) g.2⟩
  map_one' := by
    apply Subtype.ext
    show q * ((1 : ↥Γ) : G) * q⁻¹ = ((1 : ↥Γ) : G)
    simp
  map_mul' a b := by
    apply Subtype.ext
    show q * ((a : G) * (b : G)) * q⁻¹ = (q * (a : G) * q⁻¹) * (q * (b : G) * q⁻¹)
    group

/-- **The criterion setup of one compressor.**  The compressed group is `Γ`
itself, embedded by inclusion; its generating set is a finite symmetric
generating set `SΓ`; the compressors are a finite set `T` of compressors that
generates `G` together with `Γ`; the distinguished compressor is `t ∈ T`; and
the commuting factor is trivial. -/
noncomputable def ofCompressor {Γ : Subgroup G} [Infinite ↥Γ]
    (SΓ : Finset ↥Γ) (hone : 1 ∈ SΓ) (hsymm : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgen : Subgroup.closure (SΓ : Set ↥Γ) = ⊤)
    (T : Finset G) (hT : ∀ q ∈ T, q ∈ compressionSubmonoid Γ)
    (hTgen : Subgroup.closure (Set.range Γ.subtype ∪ (T : Set G)) = ⊤)
    (t : G) (ht : t ∈ T) : CompressionSetup G ↥Γ PUnit.{1} where
  embedΓ := Γ.subtype
  embedΓ_injective := Γ.subtype_injective
  embedJ := 1
  embedJ_injective := fun a b _ ↦ Subsingleton.elim a b
  generatorsΓ := SΓ
  generatorsΓ_one := hone
  generatorsΓ_symmetric := hsymm
  generatorsΓ_generate := hgen
  generatorsJ := ∅
  generatorsJ_generate := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  infiniteΓ := inferInstance
  compressors := T
  distinguished := t
  distinguished_mem := ht
  compressedEnd q hq := conjugationEnd (hT q hq)
  compressedEnd_spec _ _ _ := rfl
  generates := hTgen
  centralizes _ _ := Commute.one_right _
  disjoint g j h := by
    refine ⟨Subtype.ext ?_, Subsingleton.elim j 1⟩
    have h1 : t * (g : G) * t⁻¹ = 1 := h
    have h2 : (g : G) = 1 := by
      calc (g : G) = t⁻¹ * (t * (g : G) * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h1]
        _ = 1 := by group
    exact h2

end CompressionSetup

/-- **Sequential centralizer normalization from the per-compressor core.**  For
a countable Kazhdan group `G` and an infranormal Kazhdan subgroup `Γ`, the
statement `SeqNormalizes Γ C.distinguished` for every criterion setup `C` of
`Γ` with the inclusion as embedding gives normalization for every element of
`G`.

A finite infranormal subgroup is normal, and then every inverse is a
compressor, so every element normalizes by the automatic direction.  Otherwise
`Γ` is infinite, both groups are finitely generated by property `(T)`, and every
compressor `t` is the distinguished compressor of `CompressionSetup.ofCompressor`
with the compressor set `insert t T₀`. -/
theorem hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core
    [Countable G] {Γ : Subgroup G}
    (hG : HasKazhdanPropertyT.{0, 0} G) (hΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (hinf : IsInfranormal Γ)
    (hcore : ∀ C : CompressionSetup G ↥Γ PUnit.{1},
      (∀ g : ↥Γ, C.embedΓ g = (g : G)) → SeqNormalizes Γ C.distinguished) :
    HasSequentialCentralizerNormalization Γ := by
  classical
  by_cases hfin : Finite ↥Γ
  · haveI := hfin
    haveI hnormal : Γ.Normal := normal_of_isInfranormal_of_finite hinf
    intro A v hv g γ hγ
    have hg : g⁻¹ ∈ compressionSubmonoid Γ :=
      mem_compressionSubmonoid.mpr fun δ hδ ↦ hnormal.conj_mem δ hδ g⁻¹
    have h := seqNormalizes_inv_of_mem_compressionSubmonoid hg A v hv γ hγ
    rwa [inv_inv] at h
  · haveI : Infinite ↥Γ := not_finite_iff_infinite.mp hfin
    haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hG
    obtain ⟨SΓ, hone, hsymm, hgen⟩ :=
      KazhdanFiniteGeneration.exists_symmetric_generating_finset ↥Γ hΓ
    obtain ⟨T₀, hT₀, hT₀gen⟩ := exists_finset_compressors_generate hinf
    refine hasSequentialCentralizerNormalization_of_compressorNormalization hinf ?_
    intro t ht
    have hT : ∀ q ∈ insert t T₀, q ∈ compressionSubmonoid Γ := by
      intro q hq
      rcases Finset.mem_insert.mp hq with hqt | hqT
      · rw [hqt]
        exact ht
      · exact hT₀ q hqT
    have hTgen : Subgroup.closure
        (Set.range Γ.subtype ∪ ((insert t T₀ : Finset G) : Set G)) = ⊤ := by
      apply top_unique
      rw [← hT₀gen]
      apply Subgroup.closure_mono
      intro q hq
      exact Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hq)))
    exact hcore (CompressionSetup.ofCompressor SΓ hone hsymm hgen (insert t T₀) hT hTgen t
      (Finset.mem_insert_self t T₀)) fun _ ↦ rfl

end GroupApproximation

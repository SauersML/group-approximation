import GroupApproximation.Sofic.CoveringWitness
import GroupApproximation.Sofic.FreeLampKernelSplitting
import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint
import GroupApproximation.Sofic.SymmetricDoubleCovering

/-!
# The Kun--Thom/Shulman double construction, unconditionally

`metadata/LITERATURE_QUARANTINE.md` carries `KunThomShulmanDoubleData` with the
note that discharging it needs "the construction".  This file supplies the
construction.

## What the construction is

Fix a group `G` and a subgroup `Γ ≤ G`.  The construction produces, from that
inclusion alone:

* the two-vertex symmetric double `G *_Γ G` and its flip extension;
* the `ι`-fold amalgam `⋆_{Γ, i ∈ ι} G` for any vertex set, which contains the
  two-vertex double on any two distinct vertices, and which at `ι = ℤ` is the
  line double of Gao--Kunnawalkam Elayavalli--Mj Question 1.6 (`Sofic/LineDouble`
  builds that case separately and is unchanged);
* the free-lamp amalgam `H_K = G *_Γ (Γ × K)` and its retraction onto `K`;
* the Bass--Serre covering identifying `ker(H_K → K)` with `⋆_{Γ, k ∈ K} G`,
  and `H_K` with the semidirect product of that covering by `K`;
* the witness commutator `[t k t⁻¹, γ]`, nontrivial once the mark escapes and
  the lamp is nontrivial (`Sofic/FreeLampReduction.lampWitness_ne_one`).

Every item on that list is proved in this repository with no hypothesis beyond
`Group G` -- see `Sofic/WeakMFNonsoficDouble`, `Sofic/SymmetricDoubleFlip`,
`Sofic/LineDouble`, `Sofic/FreeLampReduction`, `Sofic/IteratedDoubleAmalgam`
and `Sofic/FreeLampKernelSplitting`.  `construction_unconditional` below
collects the covering half in one statement, so that the claim "the
construction is formalized" is a single checkable proposition rather than a
reading of a file list.

## What the construction is not

Two *theorems* were being carried inside the phrase "the double construction",
and they are not part of it.  They are separate published results about
separate objects:

* **Shulman**, *The MF property for amalgamated free products*: the amalgam of
  MF C\*-algebras over a common subalgebra is MF.  What the construction
  consumes from it is one sentence -- `IsOperatorMF (IteratedDouble G Γ K)` --
  and nothing else.
* **Kun--Thom**: in a permutation ultraproduct, the centralizer of an
  infranormal Kazhdan subgroup is normalized.  What the construction consumes
  is `HasSoficCentralizerNormalization Γ`.

Those two sentences appear below as *bare hypotheses* of the endpoint theorems,
never bundled into a named structure: `metadata/LITERATURE_QUARANTINE.md`
records that a name for a package of literature conclusions is exactly the
shape the kernel cannot see, so this file adds no new package to that roster.
Anything else that used to appear in the interface is proved here.

## The four fields that were never inputs

`KunThomShulmanDoubleData` also asked its caller for a compressor `t`, a mark
`γ`, its membership, and the escape `t⁻¹ γ t ∉ Γ`.  Those are not hypotheses:
`Sofic/InfranormalCompressionPair.exists_escape_of_not_normal` produces all
four from `¬ Γ.Normal` alone, for every group and every subgroup.  `ofNotNormal`
below builds the datum from the two literature sentences plus non-normality,
and `not_normal_of_data` proves the converse, so the replacement is exact and
loses nothing.
-/

namespace GroupApproximation

namespace KunThomShulmanDouble

/-! ## The covering half of the construction, in one statement -/

/-- **The Kun--Thom/Shulman double construction.**  For every group `G`, every
subgroup `Γ`, and every finite lamp group `K`:

* the `K`-fold amalgam of copies of `G` over `Γ` embeds in the free-lamp
  amalgam `G *_Γ (Γ × K)`;
* its image is exactly the kernel of the retraction onto `K`, so the covering
  has index `|K|`;
* operator-MF passes from the covering to the amalgam;
* soficity of the covering and of the amalgam are equivalent.

No hypothesis on `Γ`, no approximation hypothesis, and no literature input
occurs. -/
theorem construction_unconditional (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] [Finite K] :
    Function.Injective (iteratedToFreeLamp G Γ K) ∧
      (iteratedToFreeLamp G Γ K).range = lampKernel G Γ K ∧
      (lampKernel G Γ K).FiniteIndex ∧
      (IsOperatorMF (IteratedDouble G Γ K) → IsOperatorMF (FreeLamp G Γ K)) ∧
      (IsSofic (IteratedDouble G Γ K) ↔ IsSofic (FreeLamp G Γ K)) :=
  ⟨iteratedToFreeLamp_injective G Γ K,
    range_iteratedToFreeLamp G Γ K,
    lampKernel_finiteIndex G Γ K,
    isOperatorMF_freeLamp_of_isOperatorMF_iterated G Γ K,
    ⟨isSofic_freeLamp_of_isSofic_iterated G Γ K,
      isSofic_iterated_of_isSofic_freeLamp G Γ K⟩⟩

/-- The two-vertex symmetric double embeds in the free-lamp amalgam whenever
the lamp is nontrivial: it is the sub-amalgam on the vertices `1` and `k` of
the covering. -/
theorem symmetricDouble_embeds_in_freeLamp (G : Type) [Group G] (Γ : Subgroup G)
    (K : Type) [Group K] {k : K} (hk : k ≠ 1) :
    Function.Injective ((iteratedToFreeLamp G Γ K).comp
      (doubleToIterated G Γ (1 : K) k)) :=
  (iteratedToFreeLamp_injective G Γ K).comp
    (doubleToIterated_injective G Γ hk)

/-! ## The endpoint

The two literature sentences appear below as bare hypotheses rather than as a
bundled datum.  That is deliberate: `metadata/LITERATURE_QUARANTINE.md` records
that a *named* package of literature conclusions is the shape the kernel cannot
see, so no new package is introduced here.  What the construction consumes is

* `hiter : IsOperatorMF (IteratedDouble G Γ K)` -- Shulman;
* `hcent : HasSoficCentralizerNormalization Γ` -- Kun--Thom,

both printed in the statement of every theorem that uses them. -/

/-- **The free-lamp family separation.**  With the two literature sentences and
nothing else -- in particular with the compressor data replaced by the bare
statement that `Γ` is not normal -- every free-lamp amalgam over a nontrivial
finite lamp is operator-MF and nonsofic. -/
theorem freeLamp_isOperatorMF_and_not_isSofic {G : Type} [Group G] [Countable G]
    (Γ : Subgroup G) (K : Type) [Group K] [Finite K] [Nontrivial K]
    (hiter : IsOperatorMF (IteratedDouble G Γ K))
    (hcent : HasSoficCentralizerNormalization Γ) (hnn : ¬ Γ.Normal) :
    IsOperatorMF (FreeLamp G Γ K) ∧ ¬ IsSofic (FreeLamp G Γ K) := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal hnn
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  refine ⟨isOperatorMF_freeLamp_of_isOperatorMF_iterated G Γ K hiter, ?_⟩
  exact not_isSofic_freeLamp_of_centralizerNormalization Γ hcent hγ hesc hk

/-- The symmetric double is nonsofic from centralizer normalization and
non-normality alone. -/
theorem symmetricDouble_not_isSofic {G : Type} [Group G] [Countable G]
    (Γ : Subgroup G) (hcent : HasSoficCentralizerNormalization Γ)
    (hnn : ¬ Γ.Normal) : ¬ IsSofic (SymmetricDouble G Γ) := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal hnn
  exact not_isSofic_symmetricDouble_of_centralizerNormalization Γ hcent hγ hesc

/-! ## The old interface, rebuilt from three hypotheses -/

/-- The six-field datum, from three hypotheses: two literature sentences and
non-normality. -/
noncomputable def ofNotNormal {G : Type} [Group G] {Γ : Subgroup G}
    (hMF : IsGroupTheoreticMF (SymmetricDouble G Γ))
    (hcent : HasSoficCentralizerNormalization Γ)
    (hnn : ¬ Γ.Normal) : KunThomShulmanDoubleData G Γ where
  operatorMF := hMF
  centralizerNormalization := hcent
  t := (nonempty_escapeWitness_of_not_normal hnn).some.compressor
  γ := (nonempty_escapeWitness_of_not_normal hnn).some.marked
  γ_mem := (nonempty_escapeWitness_of_not_normal hnn).some.marked_mem
  escapes := (nonempty_escapeWitness_of_not_normal hnn).some.escapes

/-- Conversely, a datum forces non-normality, so nothing was weakened. -/
theorem not_normal_of_data {G : Type} [Group G] {Γ : Subgroup G}
    (D : KunThomShulmanDoubleData G Γ) : ¬ Γ.Normal := by
  have w : EscapeWitness Γ :=
    { compressor := D.t
      marked := D.γ
      marked_mem := D.γ_mem
      escapes := D.escapes }
  exact w.not_normal

/-- The combinatorial half of the datum is exactly non-normality: the four
fields exist for a pair if and only if the subgroup fails to be normal. -/
theorem nonempty_escapeWitness_iff_not_normal {G : Type} [Group G]
    (Γ : Subgroup G) : Nonempty (EscapeWitness Γ) ↔ ¬ Γ.Normal :=
  nonempty_escapeWitness_iff

/-! ## The order-two lamp, where only the symmetric theorem is needed

`Sofic/SymmetricDoubleCovering` identifies the covering of `G *_Γ (Γ × C₂)`
with `G *_Γ G` itself.  That collapses the MF input at the order-two lamp from
the finitely-many-factors form of the amalgamation theorem to its **symmetric**
form -- and `IsOperatorMF (SymmetricDouble G Γ)` is exactly the `operatorMF`
field of the datum the repository already quarantines.  So the existing datum,
unchanged, now settles the free-lamp amalgam as well as the double. -/

/-- At the order-two lamp the construction is a biconditional in both
directions: the covering *is* the symmetric double, so operator-MF and
soficity are literally the same question for `G *_Γ G` and for
`G *_Γ (Γ × C₂)`.  Unconditional. -/
theorem flipLamp_construction_unconditional (G : Type) [Group G]
    (Γ : Subgroup G) :
    Nonempty (SymmetricDouble G Γ ≃* ↥(lampKernel G Γ FlipC2)) ∧
      (IsOperatorMF (FreeLamp G Γ FlipC2)
        ↔ IsOperatorMF (SymmetricDouble G Γ)) ∧
      (IsSofic (FreeLamp G Γ FlipC2) ↔ IsSofic (SymmetricDouble G Γ)) :=
  ⟨lampKernelFlip_equiv_symmetricDouble G Γ,
    isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble G Γ,
    isSofic_freeLampFlip_iff_isSofic_symmetricDouble G Γ⟩

/-- **The whole construction at the order-two lamp, from `¬ Γ.Normal` alone.**
The covering of `G *_Γ (Γ × C₂)` is `G *_Γ G`; the two groups have the same
operator-MF status and the same soficity status; and the double carries a named
nontrivial element whose image is the commutator the centralizer theorem kills.
No literature input, no approximation hypothesis. -/
theorem flipLamp_construction_with_witness (G : Type) [Group G]
    (Γ : Subgroup G) (hnn : ¬ Γ.Normal) :
    Nonempty (SymmetricDouble G Γ ≃* ↥(lampKernel G Γ FlipC2)) ∧
      (IsOperatorMF (FreeLamp G Γ FlipC2)
        ↔ IsOperatorMF (SymmetricDouble G Γ)) ∧
      (IsSofic (FreeLamp G Γ FlipC2) ↔ IsSofic (SymmetricDouble G Γ)) ∧
      (∃ t γ : G, γ ∈ Γ ∧ doubleWitness G Γ t γ ≠ 1) :=
  ⟨lampKernelFlip_equiv_symmetricDouble G Γ,
    isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble G Γ,
    isSofic_freeLampFlip_iff_isSofic_symmetricDouble G Γ,
    exists_doubleWitness_ne_one G Γ hnn⟩

/-- **The `C₂` free-lamp separation**, from the symmetric MF sentence, the
Kun--Thom sentence, and non-normality. -/
theorem freeLampFlip_isOperatorMF_and_not_isSofic {G : Type} [Group G]
    [Countable G] (Γ : Subgroup G)
    (hMF : IsOperatorMF (SymmetricDouble G Γ))
    (hcent : HasSoficCentralizerNormalization Γ) (hnn : ¬ Γ.Normal) :
    IsOperatorMF (FreeLamp G Γ FlipC2) ∧ ¬ IsSofic (FreeLamp G Γ FlipC2) := by
  refine ⟨isOperatorMF_freeLampFlip_of_isOperatorMF_symmetricDouble G Γ hMF, ?_⟩
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal hnn
  exact not_isSofic_freeLamp_of_centralizerNormalization Γ hcent hγ hesc
    flipC2_swap_ne_one

/-- Every `KunThomShulmanDoubleData` settles the `C₂` free-lamp amalgam too,
with no additional hypothesis: non-normality is read off the datum's own
escape field by `not_normal_of_data`. -/
theorem data_freeLampFlip_conclusion {G : Type} [Group G] [Countable G]
    {Γ : Subgroup G} (D : KunThomShulmanDoubleData G Γ) :
    IsOperatorMF (FreeLamp G Γ FlipC2) ∧ ¬ IsSofic (FreeLamp G Γ FlipC2) :=
  freeLampFlip_isOperatorMF_and_not_isSofic Γ D.operatorMF
    D.centralizerNormalization (not_normal_of_data D)

/-- The datum's full yield: the double and the `C₂` free-lamp amalgam are both
operator-MF and both nonsofic. -/
theorem data_conclusion_both {G : Type} [Group G] [Countable G]
    {Γ : Subgroup G} (D : KunThomShulmanDoubleData G Γ) :
    (IsOperatorMF (SymmetricDouble G Γ) ∧ ¬ IsSofic (SymmetricDouble G Γ)) ∧
      (IsOperatorMF (FreeLamp G Γ FlipC2)
        ∧ ¬ IsSofic (FreeLamp G Γ FlipC2)) :=
  ⟨D.conclusion, data_freeLampFlip_conclusion D⟩

end KunThomShulmanDouble

end GroupApproximation

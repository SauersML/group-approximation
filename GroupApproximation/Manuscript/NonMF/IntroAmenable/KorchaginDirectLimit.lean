import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.WeakMFTransfer
import GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF
import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin, Corollary 10 and Proposition 13: direct limits of residually finite groups are MF

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace` (tex 270):

> Since $W_0$ is a direct limit of residually finite groups, it is MF~\cite[Corollary~10 and
> Proposition~13]{Korchagin}.

Both cited facts are proved here, with no literature input.

* **Corollary 10** (residually finite ⇒ MF): `GroupApproximation.isOperatorMF_of_residuallyFinite`
  (finite quotients give exact finite permutation representations; a residually finite group is
  LEF, hence weak-MF, hence operator-MF).  Endpoint:
  `manuscriptSentence_residuallyFiniteIsMF`, stated for both `LiteralMF` and `IsOperatorMF`.
* **Proposition 13** (MF passes to direct limits): `isOperatorMF_of_injective_directLimit`.  For a
  directed family of injective homomorphisms `f_i : A_i → G` whose ranges exhaust `G`, every finite
  subset of `G` lies in one range (`exists_index_of_directed`); the range is isomorphic to `A_i`,
  hence MF, hence has operator-norm local models at separation `1`
  (`OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one`); a local model of the
  range, extended by the identity matrix off the range, is a local model of `G` on the same finite
  set (`isNormApproximable_of_finset_exhaustion`), so `G` is MF.
* The printed sentence: `manuscriptSentence_shiftKernelDirectLimitMF`.  The shift kernel `W₀` is
  the injective direct limit of its finitely generated subgroups `⟨s⟩` (`s` a finite set), each
  residually finite (`shiftKernel_isLocallyResiduallyFinite`), so it is MF.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroAmenable

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **Direct-limit permanence of operator-norm local models**: if every finite subset of `G` lies
in a subgroup that is norm-approximable at separation `δ`, then `G` is norm-approximable at `δ`.
A model of the subgroup, extended by the identity matrix off the subgroup, is a model of `G`. -/
theorem isNormApproximable_of_finset_exhaustion {G : Type} [Group G] {δ : ℝ}
    (h : ∀ F : Finset G, ∃ H : Subgroup G, (∀ g ∈ F, g ∈ H) ∧ IsNormApproximable H δ) :
    IsNormApproximable G δ := by
  classical
  intro F ε hε
  obtain ⟨H, hF, hH⟩ := h F
  obtain ⟨M⟩ := hH (F.subtype (· ∈ H)) ε hε
  exact ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g => if hg : g ∈ H then M.map ⟨g, hg⟩ else 1
    isUnitary := by
      intro g
      by_cases hg : g ∈ H
      · simp only [dif_pos hg]
        exact M.isUnitary _
      · simp only [dif_neg hg]
        exact one_mem _
    multiplicative := by
      intro g hg k hk
      have hgH := hF g hg
      have hkH := hF k hk
      have hgkH : g * k ∈ H := H.mul_mem hgH hkH
      have hM := M.multiplicative ⟨g, hgH⟩ (Finset.mem_subtype.2 hg) ⟨k, hkH⟩
        (Finset.mem_subtype.2 hk)
      simp only [dif_pos hgH, dif_pos hkH, dif_pos hgkH]
      exact hM
    separated := by
      intro g hg k hk hne
      have hgH := hF g hg
      have hkH := hF k hk
      have hM := M.separated ⟨g, hgH⟩ (Finset.mem_subtype.2 hg) ⟨k, hkH⟩
        (Finset.mem_subtype.2 hk) (fun heq => hne (congrArg Subtype.val heq))
      simp only [dif_pos hgH, dif_pos hkH]
      exact hM }⟩

/-- In a directed family of subgroups covering `G`, every finite subset lies in one member. -/
theorem exists_index_of_directed {G ι : Type} [Group G] (R : ι → Subgroup G)
    (hdir : ∀ i j, ∃ k, R i ≤ R k ∧ R j ≤ R k) (hcover : ∀ g, ∃ i, g ∈ R i)
    (F : Finset G) : ∃ i, ∀ g ∈ F, g ∈ R i := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨i, -⟩ := hcover 1
    exact ⟨i, fun g hg => absurd hg (Finset.notMem_empty g)⟩
  | insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcover a
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, fun g hg => ?_⟩
    rcases Finset.mem_insert.mp hg with hga | hgs
    · rw [hga]
      exact hjk hj
    · exact hik (hi g hgs)

/-- **Korchagin, Proposition 13** (MF passes to direct limits).  If `G` is the union of the
directed family of ranges of injective homomorphisms `f i : A i →* G` and every `A i` is MF, then
`G` is MF. -/
theorem isOperatorMF_of_injective_directLimit {G ι : Type} [Group G] [Countable G]
    (A : ι → Type) [∀ i, Group (A i)] (f : ∀ i, A i →* G)
    (hinj : ∀ i, Function.Injective (f i))
    (hdir : ∀ i j, ∃ k, (f i).range ≤ (f k).range ∧ (f j).range ≤ (f k).range)
    (hcover : ∀ g, ∃ i, g ∈ (f i).range) (hMF : ∀ i, IsOperatorMF (A i)) :
    IsOperatorMF G := by
  refine GroupApproximation.OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (isNormApproximable_of_finset_exhaustion fun F => ?_)
  obtain ⟨i, hi⟩ := exists_index_of_directed (fun i => (f i).range) hdir hcover F
  have hrange : IsOperatorMF (f i).range :=
    GroupApproximation.CommensurabilityInvariance.isOperatorMF_of_mulEquiv
      (MonoidHom.ofInjective (hinj i)) (hMF i)
  exact ⟨(f i).range, hi,
    GroupApproximation.OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mp
      hrange⟩

/-- `G` is an injective direct limit of residually finite groups: a directed family of injective
homomorphisms from residually finite groups whose ranges exhaust `G`. -/
def IsInjectiveDirectLimitOfResiduallyFinite (G : Type) [Group G] : Prop :=
  ∃ (ι : Type) (A : ι → Type) (_ : ∀ i, Group (A i)) (f : ∀ i, A i →* G),
    (∀ i, Function.Injective (f i)) ∧
      (∀ i j, ∃ k, (f i).range ≤ (f k).range ∧ (f j).range ≤ (f k).range) ∧
      (∀ g : G, ∃ i, g ∈ (f i).range) ∧
      (∀ i, Group.ResiduallyFinite (A i))

/-- **Korchagin, Corollary 10 and Proposition 13**: a countable direct limit of residually
finite groups is MF. -/
theorem isOperatorMF_of_isInjectiveDirectLimitOfResiduallyFinite {G : Type} [Group G]
    [Countable G] (h : IsInjectiveDirectLimitOfResiduallyFinite G) : IsOperatorMF G := by
  obtain ⟨_, A, _, f, hinj, hdir, hcover, hRF⟩ := h
  refine isOperatorMF_of_injective_directLimit A f hinj hdir hcover fun i => ?_
  haveI : Countable (A i) := (hinj i).countable
  haveI := hRF i
  exact GroupApproximation.isOperatorMF_of_residuallyFinite

/-- **Korchagin, Corollary 10**, printed form: a countable residually finite group is MF, in the
Introduction's literal sense and as `IsOperatorMF`. -/
theorem manuscriptSentence_residuallyFiniteIsMF :
    ∀ (G : Type) [Group G] [Countable G] [Group.ResiduallyFinite G],
      LiteralMF G ∧ IsOperatorMF G := by
  intro G _ _ _
  have hMF : IsOperatorMF G := GroupApproximation.isOperatorMF_of_residuallyFinite
  exact ⟨(literalMF_iff_isOperatorMF G).mpr hMF, hMF⟩

/-- **Korchagin, Corollary 10 and Proposition 13**, printed form: a countable direct limit of
residually finite groups is MF, in the Introduction's literal sense and as `IsOperatorMF`. -/
theorem manuscriptSentence_directLimitOfResiduallyFiniteIsMF :
    ∀ (G : Type) [Group G] [Countable G],
      IsInjectiveDirectLimitOfResiduallyFinite G → LiteralMF G ∧ IsOperatorMF G := by
  intro G _ _ h
  have hMF : IsOperatorMF G := isOperatorMF_of_isInjectiveDirectLimitOfResiduallyFinite h
  exact ⟨(literalMF_iff_isOperatorMF G).mpr hMF, hMF⟩

/-- The shift kernel `W₀` is the injective direct limit of the subgroups generated by its finite
subsets, each residually finite. -/
theorem shiftKernel_isInjectiveDirectLimitOfResiduallyFinite :
    IsInjectiveDirectLimitOfResiduallyFinite
      GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel := by
  classical
  refine ⟨Finset GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel,
    fun s => ↥(Subgroup.closure
      (s : Set GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel)),
    fun s => (Subgroup.closure
      (s : Set GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel)).toGroup,
    fun s => (Subgroup.closure
      (s : Set GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel)).subtype,
    ?_, ?_, ?_, ?_⟩
  · intro s
    exact Subgroup.subtype_injective _
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro g hg
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
      exact MonoidHom.mem_range.mpr
        ⟨⟨x.1, Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_left) x.2⟩, rfl⟩
    · intro g hg
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
      exact MonoidHom.mem_range.mpr
        ⟨⟨x.1, Subgroup.closure_mono (Finset.coe_subset.mpr Finset.subset_union_right) x.2⟩, rfl⟩
  · intro g
    exact ⟨{g}, MonoidHom.mem_range.mpr
      ⟨⟨g, Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_singleton_self g))⟩, rfl⟩⟩
  · intro s
    exact GroupApproximation.CliffordWitnessLocallyRFByInt.shiftKernel_isLocallyResiduallyFinite _
      ⟨s, rfl⟩

/-- **tex 270.**  "Since `W₀` is a direct limit of residually finite groups, it is MF": the shift
kernel is an injective direct limit of residually finite groups, and it is MF, both in the
Introduction's literal sense and as `IsOperatorMF`. -/
theorem manuscriptSentence_shiftKernelDirectLimitMF :
    IsInjectiveDirectLimitOfResiduallyFinite
        GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel ∧
      LiteralMF GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel ∧
      IsOperatorMF GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel := by
  have hlim := shiftKernel_isInjectiveDirectLimitOfResiduallyFinite
  have hMF : IsOperatorMF GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel :=
    isOperatorMF_of_isInjectiveDirectLimitOfResiduallyFinite hlim
  exact ⟨hlim, (literalMF_iff_isOperatorMF _).mpr hMF, hMF⟩

end IntroAmenable
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.isOperatorMF_of_injective_directLimit
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_residuallyFiniteIsMF
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_directLimitOfResiduallyFiniteIsMF
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_shiftKernelDirectLimitMF

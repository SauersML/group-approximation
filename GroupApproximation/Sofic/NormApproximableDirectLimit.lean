import GroupApproximation.Sofic.WeakMFTransfer
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# MF is closed under direct limits, in the local-model form

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace`, remark after the proof (tex 284–286):

> Since $W_0$ is a direct limit of residually finite groups, it is MF~\cite[Corollary~10 and
> Proposition~13]{Korchagin}.

The printed route has two steps: residually finite groups are MF (Korchagin, Corollary 10), and MF passes to
direct limits (Korchagin, Proposition 13).  This module records both at the level of the operator-norm local
models `IsNormApproximable` behind `IsWeakMF`.

* `isNormApproximable_of_forall_finset_subgroup`: **direct-limit permanence**.  If every finite subset lies in a
  subgroup with operator-norm local models at separation `δ`, then so does the group.  A model of the subgroup,
  extended by the identity matrix off the subgroup, is a model of the group on the same finite set.
* `isWeakMF_of_forall_finset_residuallyFinite_subgroup`: a group exhausted by residually finite subgroups is
  weak-MF, from `isWeakMF_of_residuallyFinite` (Corollary 10) and the permanence lemma (Proposition 13).
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **Direct-limit permanence of operator-norm local models** (Korchagin, Proposition 13): if every finite subset
of `G` lies in a subgroup that is norm-approximable at separation `δ`, then `G` is norm-approximable at `δ`. -/
theorem isNormApproximable_of_forall_finset_subgroup {G : Type*} [Group G] {δ : ℝ}
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
      have hM := M.multiplicative ⟨g, hgH⟩ (Finset.mem_subtype.2 hg) ⟨k, hkH⟩ (Finset.mem_subtype.2 hk)
      simp only [dif_pos hgH, dif_pos hkH, dif_pos hgkH]
      exact hM
    separated := by
      intro g hg k hk hne
      have hgH := hF g hg
      have hkH := hF k hk
      have hM := M.separated ⟨g, hgH⟩ (Finset.mem_subtype.2 hg) ⟨k, hkH⟩ (Finset.mem_subtype.2 hk)
        (fun heq => hne (congrArg Subtype.val heq))
      simp only [dif_pos hgH, dif_pos hkH]
      exact hM }⟩

/-- **A direct limit of residually finite groups is weak-MF**: residually finite groups are weak-MF
(Korchagin, Corollary 10), and weak-MF passes to the direct limit (Proposition 13). -/
theorem isWeakMF_of_forall_finset_residuallyFinite_subgroup {G : Type*} [Group G]
    (h : ∀ F : Finset G, ∃ H : Subgroup G, (∀ g ∈ F, g ∈ H) ∧ Group.ResiduallyFinite H) :
    IsWeakMF G :=
  ⟨1, one_pos, isNormApproximable_of_forall_finset_subgroup fun F => by
    obtain ⟨H, hF, hRF⟩ := h F
    haveI := hRF
    exact ⟨H, hF, isNormApproximable_of_isLEF isLEF_of_residuallyFinite⟩⟩

end GroupApproximation

#audit_axioms GroupApproximation.isNormApproximable_of_forall_finset_subgroup
#audit_axioms GroupApproximation.isWeakMF_of_forall_finset_residuallyFinite_subgroup

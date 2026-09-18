import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Meta.AxiomGuard

/-!
# Directed unions of residually finite subgroups are MF

Manuscript `non_mf_groups_exist.tex`, discussion after `thm:amenable-trace`
(tex lines 284--288): "Since `W_0` is a direct limit of residually finite
groups, it is MF [Korchagin, Corollary 10 and Proposition 13]."

This file proves the *internal* form of that sentence, for a group written as a
directed union of residually finite subgroups (in particular an increasing
union `H 0 ≤ H 1 ≤ ⋯`).  The route is the one of the manuscript:

* a directed union of residually finite subgroups is locally residually finite
  (every finitely generated subgroup lies in one member, hence embeds in a
  residually finite group);
* locally residually finite groups are LEF
  (`GroupApproximation.isLEF_of_locallyResiduallyFinite`);
* countable LEF groups are MF (`GroupApproximation.isOperatorMF_of_isLEF`).

The general, possibly non-injective, direct-limit form is in
`Full/Korchagin/DirectLimit.lean`.
-/

namespace GroupApproximation.Full.NM09

variable {G : Type*} [Group G]

/-- Every finite subset of a group covered by a directed family of subgroups
lies in a single member of the family. -/
theorem exists_mem_of_directed_cover {ι : Type*} [Nonempty ι] (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hcov : ∀ g : G, ∃ i, g ∈ H i) (s : Finset G) :
    ∃ i, ∀ x ∈ s, x ∈ H i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov a
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with hxa | hxs
    · rw [hxa]
      exact hjk hj
    · exact hik (hi x hxs)

/-- A directed union of residually finite subgroups is locally residually
finite: every finitely generated subgroup is residually finite. -/
theorem locallyResiduallyFinite_of_directed {ι : Type*} [Nonempty ι] (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hcov : ∀ g : G, ∃ i, g ∈ H i)
    (hRF : ∀ i, Group.ResiduallyFinite (H i)) :
    ∀ K : Subgroup G, K.FG → Group.ResiduallyFinite K := by
  intro K hK
  obtain ⟨S, hS⟩ := hK
  obtain ⟨i, hi⟩ := exists_mem_of_directed_cover H hdir hcov S
  have hle : K ≤ H i := by
    rw [← hS]
    exact (Subgroup.closure_le (H i)).mpr fun x hx => hi x hx
  haveI := hRF i
  exact GroupApproximation.residuallyFinite_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

/-- A directed union of residually finite subgroups is LEF. -/
theorem isLEF_of_directed_residuallyFinite {ι : Type*} [Nonempty ι] (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hcov : ∀ g : G, ∃ i, g ∈ H i)
    (hRF : ∀ i, Group.ResiduallyFinite (H i)) : IsLEF G :=
  GroupApproximation.isLEF_of_locallyResiduallyFinite
    (locallyResiduallyFinite_of_directed H hdir hcov hRF)

/-- A countable directed union of residually finite subgroups is MF. -/
theorem isOperatorMF_of_directed_residuallyFinite [Countable G] {ι : Type*} [Nonempty ι]
    (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hcov : ∀ g : G, ∃ i, g ∈ H i)
    (hRF : ∀ i, Group.ResiduallyFinite (H i)) : IsOperatorMF G :=
  GroupApproximation.isOperatorMF_of_isLEF
    (isLEF_of_directed_residuallyFinite H hdir hcov hRF)

/-- An increasing sequence of subgroups whose supremum is `⊤` covers the group
elementwise. -/
theorem forall_exists_mem_of_iSup_eq_top (H : ℕ → Subgroup G) (hmono : Monotone H)
    (hcov : ⨆ n, H n = ⊤) : ∀ g : G, ∃ n, g ∈ H n := by
  intro g
  have hg : g ∈ ⨆ n, H n := by
    rw [hcov]
    exact Subgroup.mem_top g
  exact (Subgroup.mem_iSup_of_directed hmono.directed_le).mp hg

/-- An increasing union of residually finite subgroups is LEF. -/
theorem isLEF_of_directedUnion_residuallyFinite (H : ℕ → Subgroup G) (hmono : Monotone H)
    (hcov : ⨆ n, H n = ⊤) (hRF : ∀ n, Group.ResiduallyFinite (H n)) : IsLEF G :=
  isLEF_of_directed_residuallyFinite H hmono.directed_le
    (forall_exists_mem_of_iSup_eq_top H hmono hcov) hRF

/-- **Korchagin, internal form** (`non_mf_groups_exist.tex`, tex lines 284--288,
after `thm:amenable-trace`): a countable group that is an increasing union of
residually finite subgroups is MF. -/
theorem isOperatorMF_of_directedUnion_residuallyFinite [Countable G]
    (H : ℕ → Subgroup G) (hmono : Monotone H) (hcov : ⨆ n, H n = ⊤)
    (hRF : ∀ n, Group.ResiduallyFinite (H n)) : IsOperatorMF G :=
  GroupApproximation.isOperatorMF_of_isLEF
    (isLEF_of_directedUnion_residuallyFinite H hmono hcov hRF)

#audit_axioms isOperatorMF_of_directed_residuallyFinite
#audit_axioms isOperatorMF_of_directedUnion_residuallyFinite

end GroupApproximation.Full.NM09

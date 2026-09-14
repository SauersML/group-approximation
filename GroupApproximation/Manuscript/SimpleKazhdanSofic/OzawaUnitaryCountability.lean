import GroupApproximation.Analysis.TracialStandardFormBimodule
import GroupApproximation.Kazhdan.KazhdanProjection
import GroupApproximation.Meta.AxiomGuard

/-!
# The unitary group of a separable II₁ factor contains only countably many simple quotients

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, section "Word problems and factors", tex l.541–546:

> For a fixed alphabet, every $G_X$ is a simple quotient of the Kazhdan group $\EL_3(F)$, and [...]
> different subshifts give different kernels. The proof of~\cite[Theorem~2]{OzawaUniversal} then shows that
> the unitary group of a separable $\mathrm{II}_1$ factor contains $G_X$ for only countably many $X$.

No literature input is used.  The Hilbert estimate is `KazhdanBimoduleRigidity.bimodule_rigidity`, and the
left and right actions on a tracial standard form are `TracialStandardFormBimodule`.

* `exists_nonisolated`: an uncountable injective family in a separable pseudo-metric space has a member that
  is not isolated.  The isolated members form a discrete, hence countable, subspace.
* `countable_kernels_of_unitary`: let `Γ` have property (T), let `M` act on a separable `H` with a tracial
  cyclic separating vector `Ω`, and let the normal subgroups `N i` be distinct, maximal and proper.  Then only
  countably many `N i` are kernels of homomorphisms `Γ → U(M)`.  The route is Ozawa's:
  - the tuples `(u_i(s)Ω)_{s ∈ S}` over a finite generating Kazhdan set are distinct, as `Ω` separates;
  - uncountably many of them have a non-isolated member `i`;
  - for every `δ` a different `j` lies within `εδ`, so `bimodule_rigidity` gives `‖u_i(g)Ω − Ω‖ < 2δ`;
  - hence `u_i` is trivial and `N i = Γ`, which is excluded.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace OzawaUnitaryCountability

open TracialStandardForm TracialStandardFormBimodule KazhdanBimoduleRigidity

/-- **Condensation.**  In a separable pseudo-metric space, an uncountable injective family has a member all
of whose neighbourhoods contain another member. -/
theorem exists_nonisolated {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    {ι : Type*} (T : ι → X) {A : Set ι} (hinj : Set.InjOn T A) (hA : ¬ A.Countable) :
    ∃ i ∈ A, ∀ η > 0, ∃ j ∈ A, j ≠ i ∧ dist (T i) (T j) < η := by
  by_contra hcon
  push Not at hcon
  apply hA
  refine Set.countable_of_injective_of_countable_image hinj ?_
  haveI : DiscreteTopology ↥(T '' A) := by
    rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨_, i, hi, rfl⟩
    obtain ⟨η, hη, hsep⟩ := hcon i hi
    rw [Metric.isOpen_singleton_iff]
    refine ⟨η, hη, fun y hy ↦ ?_⟩
    obtain ⟨_, j, hj, rfl⟩ := y
    by_contra hne
    have hji : j ≠ i := fun h ↦ hne (Subtype.ext (by rw [h]))
    have h1 := hsep j hj hji
    have h2 : dist (T j) (T i) < η := hy
    rw [dist_comm] at h2
    exact absurd h2 (not_lt.mpr h1)
  haveI : TopologicalSpace.SeparableSpace ↥(T '' A) :=
    ((TopologicalSpace.isSeparable_univ_iff.mpr inferInstance).mono
      (Set.subset_univ (T '' A))).separableSpace
  exact Set.countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- Unitaries of `M` that agree on the separating vector are equal. -/
theorem eq_of_apply_omega_eq (hsf : IsTracialStandardForm M Ω) {a b : unitary ↥M.toStarSubalgebra}
    (h : ((a : ↥M.toStarSubalgebra) : H →L[ℂ] H) Ω = ((b : ↥M.toStarSubalgebra) : H →L[ℂ] H) Ω) :
    a = b := by
  have hmem : ((a : ↥M.toStarSubalgebra) : H →L[ℂ] H) - ((b : ↥M.toStarSubalgebra) : H →L[ℂ] H) ∈ M :=
    sub_mem (a : ↥M.toStarSubalgebra).2 (b : ↥M.toStarSubalgebra).2
  have h0 : ((a : ↥M.toStarSubalgebra) : H →L[ℂ] H) - ((b : ↥M.toStarSubalgebra) : H →L[ℂ] H) = 0 := by
    refine hsf.separating _ hmem ?_
    show ((a : ↥M.toStarSubalgebra) : H →L[ℂ] H) Ω - ((b : ↥M.toStarSubalgebra) : H →L[ℂ] H) Ω = 0
    exact sub_eq_zero.mpr h
  apply Subtype.ext
  apply Subtype.ext
  exact sub_eq_zero.mp h0

/-- **Ozawa's countability** (tex l.544–546, general form).  For a group with property (T) and a von
Neumann algebra in tracial standard form on a separable Hilbert space, only countably many of a family of
distinct maximal proper normal subgroups are kernels of homomorphisms into the unitary group. -/
theorem countable_kernels_of_unitary {Γ : Type} [Group Γ] (hT : HasKazhdanPropertyT.{0, 0} Γ)
    [TopologicalSpace.SeparableSpace H] (hsf : IsTracialStandardForm M Ω) {I : Type*}
    (N : I → Subgroup Γ) (hN : Function.Injective N) (hmax : ∀ i, IsMaximalNormal (N i))
    (hproper : ∀ i, N i ≠ ⊤) :
    {i | ∃ u : Γ →* unitary ↥M.toStarSubalgebra, u.ker = N i}.Countable := by
  classical
  obtain ⟨S, ε, -, -, hgen, hε, -, hS⟩ := HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  let c := tracialConjugation hsf
  by_contra hcnt
  let A : Set I := {i | ∃ u : Γ →* unitary ↥M.toStarSubalgebra, u.ker = N i}
  have hex : ∀ i, ∃ u : Γ →* unitary ↥M.toStarSubalgebra, i ∈ A → u.ker = N i := by
    intro i
    by_cases hi : i ∈ A
    · obtain ⟨u, hu⟩ := hi
      exact ⟨u, fun _ ↦ hu⟩
    · exact ⟨1, fun h ↦ absurd h hi⟩
  choose u hu using hex
  let T : I → (↥S → H) := fun i s ↦ leftRep (u i) s Ω
  have hinj : Set.InjOn T A := by
    intro i hi j hj hij
    have heq : u i = u j := by
      refine MonoidHom.eq_of_eqOn_dense hgen fun s hs ↦ ?_
      exact eq_of_apply_omega_eq hsf (congrFun hij ⟨s, hs⟩)
    exact hN (by rw [← hu i hi, ← hu j hj, heq])
  obtain ⟨i, hi, hclose⟩ := exists_nonisolated T hinj hcnt
  have hsmall : ∀ δ > 0, ∀ g, ‖leftRep (u i) g Ω - Ω‖ < 2 * δ := by
    intro δ hδ
    obtain ⟨j, hj, hji, hdist⟩ := hclose (ε * δ) (mul_pos hε hδ)
    have hker_i : (leftRep (u i)).ker = N i := by rw [ker_leftRep, hu i hi]
    have hker_j : (leftRep (u j)).ker = N j := by rw [ker_leftRep, hu j hj]
    have hmax_i : IsMaximalNormal (leftRep (u i)).ker := by
      rw [hker_i]
      exact hmax i
    have hmax_j : IsMaximalNormal (leftRep (u j)).ker := by
      rw [hker_j]
      exact hmax j
    have hne : (leftRep (u i)).ker ≠ (leftRep (u j)).ker := by
      rw [hker_i, hker_j]
      exact fun h ↦ hji (hN h).symm
    refine bimodule_rigidity hS Ω (leftRep (u i)) (leftRep (u j)) (rightRep c (u j))
      (leftRep_mul_rightRep_comm c hsf (u i) (u j)) (rightRep_omega c (u j))
      (ker_rightRep c (u j)) hmax_i hmax_j hne hδ fun s hs ↦ ?_
    calc ‖leftRep (u i) s Ω - leftRep (u j) s Ω‖ = dist (T i ⟨s, hs⟩) (T j ⟨s, hs⟩) :=
          (dist_eq_norm _ _).symm
      _ ≤ dist (T i) (T j) := dist_le_pi_dist (T i) (T j) ⟨s, hs⟩
      _ < ε * δ := hdist
  have hfix : ∀ g, leftRep (u i) g Ω = Ω := by
    intro g
    by_contra hne
    have hpos : 0 < ‖leftRep (u i) g Ω - Ω‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h := hsmall (‖leftRep (u i) g Ω - Ω‖ / 2) (by positivity) g
    linarith
  have htop : N i = ⊤ := by
    rw [← hu i hi]
    refine top_unique fun g _ ↦ ?_
    exact MonoidHom.mem_ker.mpr (eq_one_of_leftRep_omega hsf (u i) g (hfix g))
  exact hproper i htop

#audit_axioms exists_nonisolated
#audit_axioms countable_kernels_of_unitary

end OzawaUnitaryCountability
end GroupApproximation

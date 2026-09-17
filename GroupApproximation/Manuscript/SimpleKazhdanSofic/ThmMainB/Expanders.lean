import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialQuotientsExpanders
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:main`, proof sketch: marked limits of `SL_{3N}(F₂)` and expanders

`simple_kazhdan_sofic_group.tex`, l.129–134:

> These models make $G_X$ a limit of the groups $\SL_{3N}(\F_2)$ in the space of marked groups.
> The $\SL_{3N}(\F_2)$ are quotients of one Kazhdan group, $\EL_3$ of a finitely generated free
> algebra over $\F_2$, so their Cayley graphs form expanders as in Kassabov's
> construction~\cite{Kassabov}, and $G_X$ is an expander limit of them.

Route (everything used is a closed theorem of the repository).

* The periodic models give `φ_k : R S → M_{N_k}(F₂)`, matricial on the printed generators
  (`printedPeriodicMatricialStatement`, closed).
* `printedSimpleKazhdanGeneral` (closed) for the crossed product `ringEquiv S` gives the marked limit
  `EL_3(R) = lim EL_3(M_{N_k}(F₂))` with expanders, and the simplicity of `EL_3(M_{N_k}(F₂))`. Both
  transport to `G_X = EL_3(R S)` and to `SL_{3N_k}(F₂)` through `elementaryGroupEquivOfRingEquiv` and
  `elementaryBlockEquivSL`.
* The one Kazhdan group is `EL_3(F₂⟨τ_s : s ∈ S₀⟩)` for the finite printed generating set `S₀`. It has
  `(T)` by `hasKazhdanPropertyT_elementaryGroup_freeAlgebra`, which is EJZ proved in the repository.
* `ρ_k = lift (τ_s ↦ φ_k s)` is onto because `φ_k(S₀)` generates `M_{N_k}(F₂)`, so
  `EL_3(ρ_k)` is onto.
* The generator `e_ij(τ_s)` maps to the marking generator `e_ij(φ_k s)`.

Endpoints.
* `manuscriptSentence_limitOfSpecialLinearGroups` (l.129–130).
* `manuscriptSentence_quotientsOfOneKazhdanGroupExpanderLimit` (l.131–134).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainB

open SymbolicDynamics.FullShift

/-- An element of the image of a finset along a ring isomorphism pulls back into the finset. -/
theorem symm_mem_of_mem_map {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] (e : R₁ ≃+* R₂) {S : Finset R₁}
    {y : R₂} (hy : y ∈ S.map e.toEquiv.toEmbedding) : e.symm y ∈ S := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
  show e.symm (e a) ∈ S
  rw [RingEquiv.symm_apply_apply]
  exact ha

section Letters

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]

/-- The marking of the Kazhdan group `EL_3(F₂⟨τ_s : s ∈ S₀⟩)` by the `e_ij(τ_s)`, indexed like the
marking of `EL_3` of the crossed product. -/
noncomputable def freeLetterMarking (S : Subshift A ℤ) :
    MarkingIndex 3 ((printedGenerators S).map (ringEquiv S).toEquiv.toEmbedding) →
      ↥(elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) ↥(printedGenerators S))) :=
  fun p => ⟨elementaryUnit p.1.1.1 p.1.1.2 p.1.2
    (FreeAlgebra.ι (ZMod 2) ⟨(ringEquiv S).symm p.2.1, symm_mem_of_mem_map (ringEquiv S) p.2.2⟩),
    elementaryUnit_mem _ _ _ _⟩

/-- `EL_3(ρ)` sends the letter generator `e_ij(τ_s)` to `e_ij(ψ s)`, for `ρ = lift (τ_s ↦ ψ s)`. -/
theorem elementaryGroupMap_freeLetterMarking (S : Subshift A ℤ) {M : ℕ}
    (ψ : R S → Matrix (Fin M) (Fin M) (ZMod 2))
    (p : MarkingIndex 3 ((printedGenerators S).map (ringEquiv S).toEquiv.toEmbedding)) :
    elementaryGroupMap (FreeAlgebra.lift (ZMod 2) fun t : ↥(printedGenerators S) => ψ t).toRingHom
        (freeLetterMarking S p) =
      (⟨elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (ψ ((ringEquiv S).symm p.2.1)),
        elementaryUnit_mem _ _ _ _⟩ :
          ↥(elementaryGroup (Fin 3) (Matrix (Fin M) (Fin M) (ZMod 2)))) := by
  apply Subtype.ext
  change elementaryMatrixUnitMap
      (FreeAlgebra.lift (ZMod 2) fun t : ↥(printedGenerators S) => ψ t).toRingHom
      (elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (FreeAlgebra.ι (ZMod 2)
        ⟨(ringEquiv S).symm p.2.1, symm_mem_of_mem_map (ringEquiv S) p.2.2⟩)) =
    elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (ψ ((ringEquiv S).symm p.2.1))
  rw [elementaryMatrixUnitMap_elementaryUnit]
  congr 1
  exact FreeAlgebra.lift_ι_apply (fun t : ↥(printedGenerators S) => ψ t)
    ⟨(ringEquiv S).symm p.2.1, symm_mem_of_mem_map (ringEquiv S) p.2.2⟩

end Letters

/-- **tex l.131–134.** The `SL_{3N}(F₂)` are quotients of one Kazhdan group, `EL_3` of a finitely
generated free algebra over `F₂`, compatibly with the markings. Their Cayley graphs form expanders,
and `G_X` is an expander limit of them. -/
theorem manuscriptSentence_quotientsOfOneKazhdanGroupExpanderLimit (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    ∃ (N : ℕ → ℕ) (ι : Type) (s : ι → G S)
      (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))
      (κ : Type) (τ : ι → ↥(elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) κ)))
      (π : ∀ ℓ, ↥(elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) κ)) →*
        Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))) ∧
      Finite κ ∧
      HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) κ)) ∧
      (∀ ℓ, Function.Surjective (π ℓ)) ∧ (∀ ℓ i, π ℓ (τ i) = σ ℓ i) ∧
      IsMarkedLimit s σ ∧ IsExpanderFamily σ := by
  classical
  haveI := compactSpace_carrier S
  haveI : Nonempty S.carrier := hinf.nonempty
  haveI := perfectSpace_carrier S hinf hmin
  haveI : Group.FG (Multiplicative ℤ) := fg_multiplicative_int
  obtain ⟨N, φ, hφ⟩ := printedPeriodicMatricialStatement A S hinf hmin
  have hpos : ∀ k, 0 < N k := And.left hφ
  have hgen : ∀ k, Subring.closure (φ k '' (printedGenerators S : Set (R S))) = ⊤ :=
    And.left (And.right (And.right hφ))
  obtain ⟨-, -, -, -, hlim', hsimpleM, -, hexp'⟩ :=
    printedSimpleKazhdanGeneral (Multiplicative ℤ) S.carrier (isMinimal_shift S hmin)
      (isTopologicallyFree_shift S hinf hmin) _
      (one_mem_map_ringEquiv (ringEquiv S) (one_mem_printedGenerators S))
      (closure_map_ringEquiv (ringEquiv S) (closure_printedGenerators S)) N _
      (isMatricialVia_ringEquiv (ringEquiv S) hφ) 3 le_rfl
  have hlimSL :=
    (hlim'.map_source (elementaryGroupEquivOfRingEquiv 3 (ringEquiv S)).symm).map_target
      fun ℓ => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)
  have hexpSL := hexp'.map_target fun ℓ => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)
  refine ⟨N, MarkingIndex 3 ((printedGenerators S).map (ringEquiv S).toEquiv.toEmbedding), _, _,
    ↥(printedGenerators S), freeLetterMarking S,
    fun ℓ => (elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)).toMonoidHom.comp
      (elementaryGroupMap
        (FreeAlgebra.lift (ZMod 2) fun t : ↥(printedGenerators S) => φ ℓ t).toRingHom),
    fun ℓ => ?_, inferInstance, hasKazhdanPropertyT_elementaryGroup_freeAlgebra _ 3 le_rfl,
    fun ℓ => ?_, fun ℓ p => ?_, hlimSL, hexpSL⟩
  · haveI := hsimpleM ℓ
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)) :=
      (elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)).injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective
      (elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)).toMonoidHom
      (elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)).surjective
  · intro y
    obtain ⟨z, hz⟩ := elementaryGroupMap_surjective_of_surjective (ι := Fin 3)
      (FreeAlgebra.lift (ZMod 2) fun t : ↥(printedGenerators S) => φ ℓ t).toRingHom
      (lift_surjective_of_closure (printedGenerators S) (φ ℓ) (hgen ℓ))
      ((elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)).symm y)
    refine ⟨z, ?_⟩
    show elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ)
      (elementaryGroupMap (ι := Fin 3)
        (FreeAlgebra.lift (ZMod 2) fun t : ↥(printedGenerators S) => φ ℓ t).toRingHom z) = y
    rw [hz, MulEquiv.apply_symm_apply]
  · exact congrArg (fun z => elementaryBlockEquivSL 3 le_rfl (N ℓ) (hpos ℓ) z)
      (elementaryGroupMap_freeLetterMarking S (φ ℓ) p)

/-- **tex l.129–130.** The periodic models make `G_X` a limit of the groups `SL_{3N}(F₂)` in the
space of marked groups. -/
theorem manuscriptSentence_limitOfSpecialLinearGroups (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    ∃ (N : ℕ → ℕ) (ι : Type) (s : ι → G S)
      (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
      Finite ι ∧ IsMarkedLimit s σ := by
  obtain ⟨N, ι, s, σ, _, _, _, _, _, _, _, _, hlim, hexp⟩ :=
    manuscriptSentence_quotientsOfOneKazhdanGroupExpanderLimit A S hinf hmin
  exact ⟨N, ι, s, σ, And.left hexp, hlim⟩

end ThmMainB
end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_quotientsOfOneKazhdanGroupExpanderLimit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_limitOfSpecialLinearGroups

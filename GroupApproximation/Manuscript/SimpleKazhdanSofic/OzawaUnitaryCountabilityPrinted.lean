import GroupApproximation.Manuscript.SimpleKazhdanSofic.OzawaUnitaryCountability
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemKernels
import GroupApproximation.Manuscript.SimpleKazhdanSofic.StepanovSimplicity
import GroupApproximation.Analysis.GroupVonNeumannIIOneFactor
import GroupApproximation.Meta.AxiomGuard

/-!
# Tex l.544–546: `U(M)` contains `G_X` for only countably many `X`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, section "Word problems and factors":

> For a fixed alphabet, every $G_X$ is a simple quotient of the Kazhdan group $\EL_3(F)$, and
> $e_{12}(\prod_{t<m}\tau_-^t\tau_{v_t}\tau_+^t)$ lies in the kernel if and only if $v\notin L(X)$, so
> different subshifts give different kernels. The proof of~\cite[Theorem~2]{OzawaUniversal} then shows that
> the unitary group of a separable $\mathrm{II}_1$ factor contains $G_X$ for only countably many $X$.

* A separable II₁ factor is `IIOneFactor.IsIIOneFactor M`, with `M` in tracial standard form
  (`TracialStandardForm.IsTracialStandardForm M Ω`, so `H = L²(M)`) on a separable Hilbert space `H`.
* "`U(M)` contains `G_X`" is an injective homomorphism `G S →* unitary M`, as in oa-mcduff's
  `GroupVonNeumann.leftRegularUnitaryHom`.
* The first sentence is `PrintedWordProblemKernels` (`WordProblemKernels`), instantiated at the simplicity
  piece `printedSimplicityStatement_stepanov`.  It gives property (T) of `EL₃(F)`, surjections onto the
  simple groups `G_X`, and distinct kernels.
* The second is `OzawaUnitaryCountability.countable_kernels_of_unitary`.  If `f : G_X → U(M)` is injective,
  then `f ∘ π_X` has kernel `ker π_X`, which is maximal and proper because `G_X` is simple.

The endpoint uses only the standard form.  Factoriality is not needed, and it is kept for the printed
generality.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open OzawaUnitaryCountability KazhdanBimoduleRigidity SymbolicDynamics.FullShift

/-- The kernel of a surjection onto a simple group is maximal among normal subgroups. -/
theorem isMaximalNormal_ker {G₁ G₂ : Type*} [Group G₁] [Group G₂] [IsSimpleGroup G₂]
    (π : G₁ →* G₂) (hπ : Function.Surjective π) : IsMaximalNormal π.ker := by
  intro K hK hle
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) (hK.map π hπ) with h | h
  · left
    refine le_antisymm (fun g hg ↦ ?_) hle
    have hmem : π g ∈ K.map π := Subgroup.mem_map_of_mem π hg
    rw [h] at hmem
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hmem)
  · right
    refine top_unique fun g _ ↦ ?_
    have hπg : π g ∈ K.map π := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := hπg
    have hker : k⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have hprod := K.mul_mem hk (hle hker)
    simpa using hprod

/-- **Tex l.544–546**, "the unitary group of a separable II₁ factor contains $G_X$ for only countably
many $X$": for a fixed finite alphabet, the infinite minimal subshifts `X` whose group `G_X` embeds in the
unitary group of a separable II₁ factor form a countable set. -/
def PrintedUnitaryGroupContainsCountablyMany : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (M : VonNeumannAlgebra H) (Ω : H),
    TracialStandardForm.IsTracialStandardForm M Ω → IIOneFactor.IsIIOneFactor M →
      {S : Subshift A ℤ | Infinite S.carrier ∧ IsMinimal S ∧
        ∃ f : G S →* unitary ↥M.toStarSubalgebra, Function.Injective f}.Countable

theorem printedUnitaryGroupContainsCountablyMany : PrintedUnitaryGroupContainsCountablyMany := by
  intro A _ _ _ _ H _ _ _ _ M Ω hsf _
  obtain ⟨hT, hquot, -, hker⟩ :=
    printedWordProblemKernels_of_simplicity printedSimplicityStatement_stepanov A
  let N : {S : Subshift A ℤ // Infinite S.carrier ∧ IsMinimal S} →
      Subgroup ↥(elementaryGroup (Fin 3) (KernelFreeAlgebra A)) :=
    fun S ↦ (elementaryGroupMap (ι := Fin 3) (freeAlgebraProj S.1)).ker
  have hN : Function.Injective N := by
    intro S S' h
    by_contra hne
    exact hker S.1 S'.1 (fun h' ↦ hne (Subtype.ext h')) h
  have hmax : ∀ S, IsMaximalNormal (N S) := by
    intro S
    obtain ⟨hsimple, hsurj⟩ := hquot S.1 S.2.1 S.2.2
    haveI : IsSimpleGroup (G S.1) := hsimple
    exact isMaximalNormal_ker _ hsurj
  have hproper : ∀ S, N S ≠ ⊤ := by
    intro S htop
    obtain ⟨hsimple, hsurj⟩ := hquot S.1 S.2.1 S.2.2
    haveI : Nontrivial (G S.1) := hsimple.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : G S.1)
    obtain ⟨g, rfl⟩ := hsurj y
    have hg : g ∈ N S := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hy (MonoidHom.mem_ker.mp hg)
  have hcount := countable_kernels_of_unitary hT hsf N hN hmax hproper
  refine Set.Countable.mono ?_ (hcount.image Subtype.val)
  rintro S ⟨hinf, hmin, f, hf⟩
  refine ⟨⟨S, hinf, hmin⟩, ⟨f.comp (elementaryGroupMap (ι := Fin 3) (freeAlgebraProj S)), ?_⟩, rfl⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact ⟨fun h ↦ hf (h.trans (map_one f).symm), fun h ↦ by rw [h, map_one]⟩

#audit_closed_axioms printedUnitaryGroupContainsCountablyMany

end SimpleKazhdanSofic
end GroupApproximation

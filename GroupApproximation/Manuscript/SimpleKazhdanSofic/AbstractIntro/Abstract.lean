import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, abstract (tex l.33–46)

> l.33–34: Infinite simple groups with property~\textup{(T)} can be limits of finite simple groups.
>
> l.34–38: For every infinite minimal subshift $X$, the group $G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is
> an infinite, finitely generated, simple group with property~\textup{(T)} and a limit of finite
> simple groups $\SL_{3N}(\F_2)$ whose Cayley graphs form expanders, so it is locally embeddable
> into finite groups (LEF), sofic and hyperlinear.
>
> l.41–45: A finitely generated group is LEF if and only if it is a subgroup of an infinite, finitely
> generated, simple Kazhdan group that is a limit of finite simple groups whose Cayley graphs form
> expanders, and the host can be chosen with a word problem of the same Turing degree as that of
> the group.
>
> l.45–46: One such host contains every recursively presented finitely generated LEF group.

Route.

* `manuscriptSentence_gXInfiniteSimpleKazhdanExpanderLimitLEFSoficHyperlinear` is the closed
  `printedSimpleKazhdanSoficMain` at rank `3`, with the expander clause unfolded: a marked limit of
  the finite simple groups `SL_{3N_ℓ}(F₂)` (indexed by `Fin 3 × Fin N_ℓ`) whose Cayley graphs have
  uniform edge expansion.
* `manuscriptSentence_infiniteSimpleKazhdanLimitOfFiniteSimple` instantiates it at the Toeplitz
  subshift, which is infinite and minimal.
* `manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimit` is `cor:lef`, first statement
  (`printedLEFSubgroupCharacterization`); the Turing-degree clause is not stated here.
* `manuscriptSentence_hostContainsRecursivelyPresentedLEF` is `printedRecursivelyPresentedLEFHost`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **tex l.34–38**: for every infinite minimal subshift `X` over a finite alphabet, `G_X = EL₃(R_X)`
is infinite, finitely generated, simple and Kazhdan, is a marked limit of the finite simple groups
`SL_{3N_ℓ}(F₂)` whose Cayley graphs form an expander family, and is LEF, sofic and hyperlinear. -/
theorem manuscriptSentence_gXInfiniteSimpleKazhdanExpanderLimitLEFSoficHyperlinear
    (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ)
    (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    Infinite (G S) ∧ Group.FG (G S) ∧ IsSimpleGroup (G S) ∧ HasKazhdanPropertyT.{0, 0} (G S) ∧
      (∃ (ι : Type) (s : ι → G S) (N : ℕ → ℕ)
          (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)),
        (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2))) ∧
          IsMarkedLimit s σ ∧ IsExpanderFamily σ) ∧
      IsLEF (G S) ∧ IsSofic (G S) ∧ IsHyperlinear (G S) :=
  printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl

/-- **tex l.33–34**: there is an infinite simple group with property (T) which is a marked limit of
finite simple groups. -/
theorem manuscriptSentence_infiniteSimpleKazhdanLimitOfFiniteSimple :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      ∃ (ι : Type) (s : ι → E) (H : ℕ → Type) (_ : ∀ ℓ, Group (H ℓ)) (σ : ∀ ℓ, ι → H ℓ),
        (∀ ℓ, Finite (H ℓ)) ∧ (∀ ℓ, IsSimpleGroup (H ℓ)) ∧ IsMarkedLimit s σ := by
  obtain ⟨hinf, -, hsimple, hT, hlimit, -, -, -⟩ :=
    manuscriptSentence_gXInfiniteSimpleKazhdanExpanderLimitLEFSoficHyperlinear Bool toeplitzSubshift
      toeplitzSubshift_infinite toeplitzSubshift_isMinimal
  obtain ⟨ι, s, N, σ, hsimpleSL, hlim, hexp⟩ := hlimit
  obtain ⟨-, hfin, -, -⟩ := hexp
  exact ⟨G toeplitzSubshift, inferInstance, hinf, hsimple, hT, ι, s,
    fun ℓ => Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2), fun _ => inferInstance, σ, hfin,
    hsimpleSL, hlim⟩

/-- **tex l.41–43**, first clause: a finitely generated group is LEF if and only if it is a subgroup of
an infinite, finitely generated, simple Kazhdan group that is a marked limit of finite simple groups
`SL_κ(F₂)` whose Cayley graphs form expanders (`IsLEFHost`). -/
theorem manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimit (Γ : Type) [Group Γ]
    (hfg : Group.FG Γ) :
    IsLEF Γ ↔ ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f :=
  printedLEFSubgroupCharacterization Γ hfg

/-- **tex l.45–46**: one such host contains every recursively presented finitely generated LEF
group. -/
theorem manuscriptSentence_hostContainsRecursivelyPresentedLEF :
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧
      ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (GroupApproximation.Higman.RecursivePresentation Γ) →
        IsLEF Γ → ∃ f : Γ →* E, Function.Injective f :=
  printedRecursivelyPresentedLEFHost

end GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_gXInfiniteSimpleKazhdanExpanderLimitLEFSoficHyperlinear
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_infiniteSimpleKazhdanLimitOfFiniteSimple
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.AbstractIntro.manuscriptSentence_hostContainsRecursivelyPresentedLEF

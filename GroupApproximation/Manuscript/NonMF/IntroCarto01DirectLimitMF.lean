import GroupApproximation.Manuscript.NonMF.IntroCarto01DirectLimitOf
import GroupApproximation.Manuscript.NonMF.IntroAmenable.KorchaginDirectLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin, Proposition 13, in Mathlib `DirectLimit` form

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace`, tex 284–286:

> Since $W_0$ is a direct limit of residually finite groups, it is MF~\cite[Corollary~10 and
> Proposition~13]{Korchagin}.

MF is printed for countable groups (tex 87), so the endpoints derive countability of the limit
and then prove MF.

* `manuscriptSentence_directLimitMF` (Proposition 13): for a countable directed index set and a
  directed system of countable MF groups with injective connecting maps, Mathlib's
  `DirectLimit G f` is countable and MF.  Route: the canonical stage maps `IntroCarto01.of` are
  injective (`of_injective`), their ranges are directed (`range_of_directed`) and cover the limit
  (`exists_mem_range_of`), and the limit is countable (`countable_directLimit`); then
  `IntroAmenable.isOperatorMF_of_injective_directLimit` applies.
* `manuscriptSentence_directLimitResiduallyFiniteMF` (Corollary 10 and Proposition 13): the same
  with residually finite stages, where each stage is MF by
  `GroupApproximation.isOperatorMF_of_residuallyFinite`; MF also in the Introduction's literal
  sense (`IntroAmenable.literalMF_iff_isOperatorMF`).

Injectivity of the connecting maps is what the manuscript uses (the shift kernel `W₀` is a union
of subgroups).  Permanence along non-injective systems is not claimed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto01

/-- **Korchagin, Proposition 13**, Mathlib `DirectLimit` form: a countably indexed directed system
of countable MF groups with injective connecting maps has a countable MF direct limit. -/
theorem manuscriptSentence_directLimitMF {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] [Countable ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)]
    (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G fun i j h ↦ f i j h]
    (hinj : ∀ i j h, Function.Injective (f i j h)) (hMF : ∀ i, IsOperatorMF (G i)) :
    Countable (DirectLimit G f) ∧ IsOperatorMF (DirectLimit G f) := by
  have hcount : Countable (DirectLimit G f) := countable_directLimit G f
  exact ⟨hcount, IntroAmenable.isOperatorMF_of_injective_directLimit G (of G f)
    (of_injective G f hinj) (range_of_directed G f) (exists_mem_range_of G f) hMF⟩

/-- **Korchagin, Corollary 10 and Proposition 13**, Mathlib `DirectLimit` form: a countably
indexed directed system of countable residually finite groups with injective connecting maps has
a countable direct limit that is MF, in the Introduction's literal sense and as `IsOperatorMF`. -/
theorem manuscriptSentence_directLimitResiduallyFiniteMF {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] [Countable ι] (G : ι → Type) [∀ i, Group (G i)]
    [∀ i, Countable (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h]
    (hinj : ∀ i j h, Function.Injective (f i j h)) (hRF : ∀ i, Group.ResiduallyFinite (G i)) :
    Countable (DirectLimit G f) ∧ IntroAmenable.LiteralMF (DirectLimit G f) ∧
      IsOperatorMF (DirectLimit G f) := by
  have hMF : ∀ i, IsOperatorMF (G i) := fun i => by
    haveI := hRF i
    exact GroupApproximation.isOperatorMF_of_residuallyFinite
  have hlim := manuscriptSentence_directLimitMF G f hinj hMF
  haveI : Countable (DirectLimit G f) := hlim.1
  exact ⟨hlim.1,
    (IntroAmenable.literalMF_iff_isOperatorMF (DirectLimit G f)).mpr hlim.2, hlim.2⟩

end IntroCarto01
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.manuscriptSentence_directLimitMF
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.manuscriptSentence_directLimitResiduallyFiniteMF

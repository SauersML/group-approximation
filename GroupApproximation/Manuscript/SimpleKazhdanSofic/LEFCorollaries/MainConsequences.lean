import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Meta.AxiomGuard

/-!
# `G_X` is LEF, sofic and hyperlinear, and answers Brown, Ozawa and Pestov

`simple_kazhdan_sofic_group.tex` (current text, commit 1eefb3bbb), `thm:main`, l.78–79:

> So $G_X$ is locally embeddable into finite groups \textup{(LEF)}, sofic and hyperlinear.

Abstract, l.36–40:

> For every infinite minimal subshift $X$, the group $G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an
> infinite, finitely generated, simple group with property~\textup{(T)} and a limit of finite simple
> groups $\SL_{3N}(\F_2)$ whose Cayley graphs form expanders, so it is locally embeddable into finite
> groups (LEF), sofic and hyperlinear. This answers the question of Brown and Ozawa whether an
> infinite simple Kazhdan group can be hyperlinear, and Pestov's sofic version of it.

## Spelling

* `G S = EL_3(R S)` with `R S = LC(X, F₂) ⋊ ℤ` (`SimpleKazhdanSofic.Setting`).
* "can be hyperlinear" is answered by an infinite simple Kazhdan hyperlinear group, and "Pestov's sofic
  version" by an infinite simple Kazhdan sofic group. "This answers" refers to the groups `G_X`. So
  the endpoint states both existence claims, and that every `G_X` with `X` infinite minimal has all the
  properties. It also states that such an `X` exists (the Toeplitz subshift), so the answer is not
  vacuous.

## Proof route

`thm:main` is closed (`printedSimpleKazhdanSoficMain`). Its last three conjuncts at `n = 3` give
LEF, sofic and hyperlinear. The Toeplitz subshift (`toeplitzSubshift`, closed: infinite and minimal)
supplies the groups for the two existence claims.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LEFCorollaries

open SymbolicDynamics.FullShift Set

/-- **`thm:main`, last sentence** (tex l.78–79): for an infinite minimal subshift `X` over a finite
alphabet, `G_X` is LEF, sofic and hyperlinear. -/
theorem manuscriptSentence_gxLEFSoficHyperlinear (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    IsLEF (G S) ∧ IsSofic (G S) ∧ IsHyperlinear (G S) := by
  obtain ⟨-, -, -, -, -, hlef, hsofic, hhyp⟩ := printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  exact ⟨hlef, hsofic, hhyp⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_gxLEFSoficHyperlinear

/-- **The abstract's answer** (tex l.38–40). Some infinite simple Kazhdan group is hyperlinear (the
question of Brown and Ozawa), and some infinite simple Kazhdan group is sofic (Pestov's version).
The groups `G_X` answer both: every `G_X` with `X` an infinite minimal subshift is infinite, simple,
Kazhdan, hyperlinear and sofic, and such subshifts exist. -/
theorem manuscriptSentence_answersBrownOzawaPestov :
    (∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
        IsHyperlinear E) ∧
      (∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
        IsSofic E) ∧
      (∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S) ∧
      ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
        Infinite S.carrier → IsMinimal S →
          Infinite (G S) ∧ IsSimpleGroup (G S) ∧ HasKazhdanPropertyT.{0, 0} (G S) ∧
            IsHyperlinear (G S) ∧ IsSofic (G S) := by
  have hall : ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
      (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
        Infinite (G S) ∧ IsSimpleGroup (G S) ∧ HasKazhdanPropertyT.{0, 0} (G S) ∧
          IsHyperlinear (G S) ∧ IsSofic (G S) := by
    intro A _ _ _ S hinf hmin
    obtain ⟨hinfG, -, hsimple, hT, -, -, hsofic, hhyp⟩ :=
      printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
    exact ⟨hinfG, hsimple, hT, hhyp, hsofic⟩
  obtain ⟨hinfT, hsimpleT, hTT, hhypT, hsoficT⟩ :=
    hall Bool toeplitzSubshift toeplitzSubshift_infinite toeplitzSubshift_isMinimal
  exact ⟨⟨G toeplitzSubshift, inferInstance, hinfT, hsimpleT, hTT, hhypT⟩,
    ⟨G toeplitzSubshift, inferInstance, hinfT, hsimpleT, hTT, hsoficT⟩,
    ⟨toeplitzSubshift, toeplitzSubshift_infinite, toeplitzSubshift_isMinimal⟩, hall⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_answersBrownOzawaPestov

end LEFCorollaries
end SimpleKazhdanSofic
end GroupApproximation

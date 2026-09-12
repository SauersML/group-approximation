import GroupApproximation.Leavitt.BinaryLeavittAllRanksUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction: the unit group of the binary Leavitt algebra (tex 145–153)

`non_mf_groups_exist.tex`, Introduction:

> This paper focuses on a different counterexample, `H = L_{𝔽₂}(1,2)^×`, the unit group of
> the binary Leavitt algebra, because `H` is simple and every homomorphism from `H` to an
> MF group is trivial.  The right module `R_R` over `R = L_{𝔽₂}(1,2)` satisfies
> `R_R ≅ R_R ⊕ R_R`, and `H` is its automorphism group; Khanh--Thanh show that
> `H ≅ GL_n(R) = EL_n(R)` for every `n ≥ 2` [Khanh--Thanh, Proposition 4.2 and
> Corollary 4.4].

One closed proposition carries every clause, at the literal ring
`UniversalLeavitt.BinaryLeavittAlgebra = L_{𝔽₂}(1,2)` (the ring `R` of `thm:headline`,
`RankFourEndpoint.R`):

* simplicity and triviality of every homomorphism to an MF group are clauses of
  `UnitGroupHeadline.manuscriptUnitGroupHeadline`;
* `R_R ≅ R_R ⊕ R_R` as right `R`-modules is `LeavittFamily.rightLinearEquivSquare`;
* `H ≅ Aut_R(R_R) = (End_R(R_R))^×` is `unitsEquivEndUnits`;
* `H ≅ GL_n(R)` for every `n ≥ 2` is the prefix-code self-similarity
  `LeavittFamily.nonempty_prefixUnitsEquiv`, and `GL_n(R) = EL_n(R)` is
  `BinaryLeavitt.elementaryGroup_eq_top`.

The Khanh--Thanh citation is attribution: every clause is proved in this repository.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroUnitGroupSentences

/-- **Printed (tex 145–153).**  For `R = L_{𝔽₂}(1,2)` and `H = R^×`: `H` is simple and
every homomorphism from `H` to an MF group is trivial; `R_R ≅ R_R ⊕ R_R` as right
`R`-modules; `H` is the automorphism group of `R_R`; and `H ≅ GL_n(R) = EL_n(R)` for every
`n ≥ 2`. -/
def PrintedIntroUnitGroup : Prop :=
  (IsSimpleGroup (UniversalLeavitt.BinaryLeavittAlgebra)ˣ ∧
      ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ (f : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ →* M)
          (x : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ), f x = 1) ∧
    Nonempty (UniversalLeavitt.BinaryLeavittAlgebra
        ≃ₗ[(UniversalLeavitt.BinaryLeavittAlgebra)ᵐᵒᵖ]
      UniversalLeavitt.BinaryLeavittAlgebra × UniversalLeavitt.BinaryLeavittAlgebra) ∧
    Nonempty ((UniversalLeavitt.BinaryLeavittAlgebra)ˣ ≃*
      (Module.End (UniversalLeavitt.BinaryLeavittAlgebra)ᵐᵒᵖ
        UniversalLeavitt.BinaryLeavittAlgebra)ˣ) ∧
    ∀ n : ℕ, 2 ≤ n →
      Nonempty ((UniversalLeavitt.BinaryLeavittAlgebra)ˣ ≃*
          (Matrix (Fin n) (Fin n) UniversalLeavitt.BinaryLeavittAlgebra)ˣ) ∧
        elementaryGroup (Fin n) UniversalLeavitt.BinaryLeavittAlgebra = ⊤

theorem manuscriptSentence_introUnitGroup : PrintedIntroUnitGroup := by
  obtain ⟨-, -, -, hsimple, -, -, hkill, -⟩ :=
    OneSidedMFRadical.UnitGroupHeadline.manuscriptUnitGroupHeadline
  refine ⟨⟨hsimple, hkill⟩, ⟨UniversalLeavitt.family.rightLinearEquivSquare⟩,
    ⟨unitsEquivEndUnits _⟩, ?_⟩
  intro n hn
  obtain ⟨e⟩ := UniversalLeavitt.family.nonempty_prefixUnitsEquiv (show 1 ≤ n by omega)
  exact ⟨⟨e.symm⟩, BinaryLeavitt.elementaryGroup_eq_top (ZMod 2) n hn⟩

end IntroUnitGroupSentences
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroUnitGroupSentences.manuscriptSentence_introUnitGroup

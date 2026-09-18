import GroupApproximation.Analysis.McDuffTensorHyperfinite
import GroupApproximation.Analysis.GroupVonNeumannUnitaryGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.InfiniteSimpleICC
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's formulation: the factor clauses for an infinite simple group

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation" (after the proof of
`thm:general`), for `G` as in Theorem `thm:general`(b):

> As `G` is infinite and simple, its nontrivial conjugacy classes are infinite, so `L(G)` is a
> `II₁` factor. Then `G` lies in the unitary group of the McDuff factor `L(G) ⊗̄ 𝓡` [McDuff], ...

`printedBrownFactors` proves these clauses for every infinite simple group, which covers the groups
of `thm:general`(b). It is also the factor half of table row `T3` of `tab:props` ("`L(G_X)` is a
`II₁` factor ... | infinite conjugacy classes") and of sentence M2 ("`G_X` lies in the unitary group
of the McDuff factor `L(G_X) ⊗̄ 𝓡`").

What the Lean objects are:
* `L(G)` is `GroupVonNeumann.groupVonNeumannAlgebra G = λ(G)''` on `ℓ²(G)`.
* A II₁ factor (`IIOneFactor.IsIIOneFactor`) is an infinite-dimensional factor with a faithful
  normal tracial state.
* `𝓡` is the Pauli model `L_β(Γ)`, `Γ = ℕ →₀ (ZMod 2 × ZMod 2)`, and `M ⊗̄ 𝓡` is
  `McDuff.tensorHyperfinite M`, generated on `ℓ²(Γ; H)` by `M ⊗ 1` and `1 ⊗ 𝓡`.
* A McDuff factor (`McDuff.IsMcDuffFactor`) is a II₁ factor `M` with `M ≅ M ⊗̄ 𝓡` as unital
  ⋆-algebras.
* "`G` lies in the unitary group" means there is an injective group homomorphism into the unitary
  group, `g ↦ λ(g) ⊗ 1`.

The embedding of `L(G) ⊗̄ 𝓡` in `𝓡^ω` is a separate file of this lane.
-/

namespace GroupApproximation.Full.SK06

universe u

/-- **Brown's formulation, factor clauses** (`simple_kazhdan_sofic_group.tex`, "Brown's
formulation"; the factor half of `tab:props` row T3 and of sentence M2). Let `G` be an infinite
simple group. Then:
1. its nontrivial conjugacy classes are infinite;
2. `L(G)` is a II₁ factor;
3. `L(G) ⊗̄ 𝓡` is a McDuff factor;
4. `G` embeds in the unitary group of `L(G)`;
5. `G` embeds in the unitary group of `L(G) ⊗̄ 𝓡`. -/
def PrintedBrownFactors : Prop :=
  ∀ (G : Type u) [Group G], IsSimpleGroup G → Infinite G →
    TwoSidedRegularCommutant.IsICC G ∧
      IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra G) ∧
      McDuff.IsMcDuffFactor (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)) ∧
      (∃ φ : G →* unitary ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra,
        Function.Injective φ) ∧
      ∃ φ : G →* unitary
          ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)).toStarSubalgebra,
        Function.Injective φ

theorem printedBrownFactors : PrintedBrownFactors.{u} := by
  intro G _ _ _
  have hICC : TwoSidedRegularCommutant.IsICC G :=
    SimpleKazhdanSofic.isICC_of_isSimpleGroup_of_infinite G
  exact ⟨hICC, IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra G hICC,
    McDuff.isMcDuffFactor_tensorHyperfinite G hICC,
    ⟨GroupVonNeumann.leftRegularUnitaryHom G, GroupVonNeumann.leftRegularUnitaryHom_injective G⟩,
    McDuff.groupUnitaryHom G, McDuff.groupUnitaryHom_injective G⟩

end GroupApproximation.Full.SK06

#audit_closed_axioms GroupApproximation.Full.SK06.printedBrownFactors

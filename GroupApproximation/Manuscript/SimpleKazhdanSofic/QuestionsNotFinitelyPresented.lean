import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsGroup
import GroupApproximation.Sofic.FinitelyPresentedLEF
import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Pestov91.CentreSkew
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# `G_X` is not finitely presented

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, "Questions" (census key `44b4aa4489ab`, tex l.556–558):

> A finitely presented LEF group is residually finite [Stepin, VershikGordon], and the infinite simple group
> `G_X` is not, so `G_X` is not finitely presented.

The two inputs are already proved in this repository:
* `finitelyPresented_isLEF_residuallyFinite` (Vershik--Gordon, over `PresentedGroup` of a finite relator
  set);
* `NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`.

This module closes what the sentence adds:

* `exists_presentedGroup_mulEquiv`: a group finitely presented in Mathlib's sense
  (`Group.IsFinitelyPresented`: a finite generating set whose relation kernel is the normal closure of
  finitely many relators) is isomorphic to `PresentedGroup` of a finite relator set;
* `PrintedFinitelyPresentedLEFResiduallyFinite`: a finitely presented LEF group is residually finite;
* `PrintedNotFinitelyPresentedOfLEFSimpleInfinite`: an infinite simple LEF group is not finitely
  presented;
* `PrintedGXNotFinitelyPresented`: the instance at `G_X = EL_3(LC(X, F_2) ⋊_T ℤ)`, for every infinite
  minimal subshift.  It is assembled from the ring models of "Finite models"
  (`IsMatricialLEFRing (ZMod 2) (R S)`) and simplicity from "Simplicity", named hypotheses until
  their owners close them.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

universe u

open SymbolicDynamics.FullShift

/-- **From a finite presentation to a presented group.**  If `G` is finitely presented, there are a
finite relator set `rels` in a free group of finite rank and an isomorphism
`PresentedGroup rels ≃* G`. -/
theorem exists_presentedGroup_mulEquiv {G : Type u} [Group G] (hfp : Group.IsFinitelyPresented G) :
    ∃ (n : ℕ) (rels : Finset (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (rels : Set (FreeGroup (Fin n))) ≃* G) := by
  classical
  obtain ⟨n, φ, hφ, S, hSfin, hS⟩ := hfp.out
  refine ⟨n, hSfin.toFinset, ⟨?_⟩⟩
  have hker : Subgroup.normalClosure
      ((hSfin.toFinset : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n))) = φ.ker := by
    rw [Set.Finite.coe_toFinset]
    exact hS
  change FreeGroup (Fin n) ⧸ Subgroup.normalClosure
    ((hSfin.toFinset : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n))) ≃* G
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

/-- **A finitely presented LEF group is residually finite** (tex 496, [Stepin, VershikGordon]). -/
def PrintedFinitelyPresentedLEFResiduallyFinite : Prop :=
  ∀ (G : Type u) [Group G], Group.IsFinitelyPresented G → IsLEF G → IsResiduallyFinite G

theorem printedFinitelyPresentedLEFResiduallyFinite :
    PrintedFinitelyPresentedLEFResiduallyFinite.{u} := by
  intro G _ hfp hLEF
  obtain ⟨n, rels, ⟨e⟩⟩ := exists_presentedGroup_mulEquiv hfp
  have hLEF' : IsLEF (PresentedGroup (rels : Set (FreeGroup (Fin n)))) :=
    isLEF_of_injective e.toMonoidHom e.injective hLEF
  refine isResiduallyFinite_iff.mpr fun x hx => ?_
  have hx' : e.symm x ≠ 1 := fun h => hx (e.symm.injective (h.trans (map_one e.symm).symm))
  obtain ⟨m, ψ, hψ⟩ := finitelyPresented_isLEF_residuallyFinite rels hLEF' (e.symm x) hx'
  refine ⟨(ψ.comp e.symm.toMonoidHom).ker, inferInstance, fun hmem => hψ ?_⟩
  exact MonoidHom.mem_ker.mp hmem

/-- **An infinite simple LEF group is not finitely presented** (tex 496–498): it is not residually
finite, and a finitely presented LEF group is. -/
def PrintedNotFinitelyPresentedOfLEFSimpleInfinite : Prop :=
  ∀ (G : Type u) [Group G] [IsSimpleGroup G] [Infinite G], IsLEF G → ¬ Group.IsFinitelyPresented G

theorem printedNotFinitelyPresentedOfLEFSimpleInfinite :
    PrintedNotFinitelyPresentedOfLEFSimpleInfinite.{u} := by
  intro G _ _ _ hLEF hfp
  exact NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite G
    (printedFinitelyPresentedLEFResiduallyFinite G hfp hLEF)

/-- **`G_X` is not finitely presented** (tex 496–498), for every infinite minimal subshift `X ⊆ A^ℤ`
over a finite alphabet. -/
def PrintedGXNotFinitelyPresented : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → IsMinimal S → ¬ Group.IsFinitelyPresented (G S)

/-- The instance at `G_X`, from the ring models of "Finite models" and simplicity from "Simplicity".
`G_X` is infinite because `R` is, and LEF by `printedFiniteModelsLEFSoficHyperlinear`. -/
theorem printedGXNotFinitelyPresented_of_pieces
    (hlef : ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
      Infinite S.carrier → IsMinimal S → IsMatricialLEFRing (ZMod 2) (R S))
    (hsimple : ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
      (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S → IsSimpleGroup (G S)) :
    PrintedGXNotFinitelyPresented := by
  intro A _ _ _ S hinf hmin
  haveI := hsimple A S hinf hmin
  haveI : Nonempty S.carrier := hinf.nonempty
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne (0 : ZMod 2) 1 (by decide)
  haveI : Nontrivial (LocallyConstant S.carrier (ZMod 2)) := Pestov91.locallyConstant_nontrivial
  haveI : Nontrivial (ClopenCoeff (subshiftHomeo S) (ZMod 2)) :=
    inferInstanceAs (Nontrivial (LocallyConstant S.carrier (ZMod 2)))
  haveI : Infinite (Multiplicative ℤ) := inferInstanceAs (Infinite ℤ)
  haveI : Infinite (R S) := Pestov91.skewMonoidAlgebra_infinite
  haveI : Infinite (G S) := elementaryGroup_infinite (ι := Fin 3) (R := R S) 0 1 (by decide)
  exact printedNotFinitelyPresentedOfLEFSimpleInfinite (G S)
    (printedFiniteModelsLEFSoficHyperlinear (ZMod 2) (R S) (hlef A S hinf hmin)).1

/-- **The instance at `G_X` from `thm:main`.**  The theorem of the note makes `G_X` infinite, simple
and LEF, so `G_X` is not finitely presented.  This closes when the assembly
`printedSimpleKazhdanSoficMain_of_pieces` closes. -/
theorem printedGXNotFinitelyPresented_of_main (hmain : PrintedSimpleKazhdanSoficMain) :
    PrintedGXNotFinitelyPresented := by
  intro A _ _ _ S hinf hmin
  obtain ⟨hinfG, -, hsimple, -, -, hLEF, -, -⟩ := hmain A S hinf hmin 3 le_rfl
  haveI := hinfG
  haveI := hsimple
  exact printedNotFinitelyPresentedOfLEFSimpleInfinite (G S) hLEF

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_presentedGroup_mulEquiv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedGXNotFinitelyPresented_of_pieces
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedGXNotFinitelyPresented_of_main
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedNotFinitelyPresentedOfLEFSimpleInfinite

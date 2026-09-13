import GroupApproximation.Kazhdan.GHWJacobsonKazhdanFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresentedSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Kazhdan subgroups of `GL_2(J)` at the printed `J = F_2⟨s,t | ts=1⟩`

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1151):

> Every countable subgroup of `GL_2` over a field has the Haagerup property [GHW, Theorem 4],
> and the kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, so a Kazhdan subgroup of
> `GL_2(J)` has finite image in `GL_2(F_2(z))` and a locally finite subgroup of finite index,
> and is finite.

`GHW.printedJacobsonRankTwoKazhdanFiniteField` proves the sentence for the operator model
`jacobsonAlgebra`.  Here it is proved for the presented algebra
`ToeplitzJacobson = F_2⟨s,t⟩/(ts = 1)`:

* `presGLSymbolMap : GL_2(J) → GL_2(F_2[z,z^{-1}])` applies the symbol `presSymbol`
  (`s ↦ z`, `t ↦ z^{-1}`) entrywise.  It is the operator symbol map precomposed with
  `GL_2(jacobsonEquiv)` (`presGLSymbolMap_eq_comp`);
* `GL_2(jacobsonEquiv)` is injective, so precomposing with it keeps a kernel locally finite
  (`isLocallyFiniteGroup_ker_comp_presGLEquivMap`);
* the Kazhdan deduction `JacobsonRankTwo.manuscriptSentence_kazhdanSubgroupFinite` is applied at
  `GL_2(J) → GL_2(F_2(z))`, with its Haagerup binder discharged by `GHW.printedGHWTheoremFour`
  at `F_2(z)`.  No transport of property (T) is needed.

## Manuscript status

Tex 1146--1151: `formalized` at the printed `J`,
`printedPresentedJacobsonRankTwoKazhdanFiniteField`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonPresented

open TorsionComplementaryIdempotents JacobsonSymbol JacobsonLaurent

noncomputable section

/-- `GL_2(jacobsonEquiv) : GL_2(J) → GL_2` of the operator model. -/
def presGLEquivMap : GL (Fin 2) ToeplitzJacobson →* GL (Fin 2) ↥jacobsonAlgebra :=
  Units.map (jacobsonEquiv.toRingHom.mapMatrix : Matrix (Fin 2) (Fin 2) ToeplitzJacobson →+*
    Matrix (Fin 2) (Fin 2) ↥jacobsonAlgebra).toMonoidHom

theorem presGLEquivMap_injective : Function.Injective presGLEquivMap := by
  intro x y hxy
  refine Units.ext (Matrix.ext fun a b ↦ jacobsonEquiv.injective ?_)
  exact congrArg (fun z : GL (Fin 2) ↥jacobsonAlgebra ↦
    (z : Matrix (Fin 2) (Fin 2) ↥jacobsonAlgebra) a b) hxy

/-- Precomposing with `GL_2(jacobsonEquiv)` keeps the kernel locally finite. -/
theorem isLocallyFiniteGroup_ker_comp_presGLEquivMap {K : Type} [Group K]
    (φ : GL (Fin 2) ↥jacobsonAlgebra →* K) (hφ : IsLocallyFiniteGroup φ.ker) :
    IsLocallyFiniteGroup (φ.comp presGLEquivMap).ker :=
  hφ.comap ((presGLEquivMap.restrict (φ.comp presGLEquivMap).ker).codRestrict φ.ker
      fun x ↦ MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2))
    fun _ _ hxy ↦ Subtype.ext (presGLEquivMap_injective (congrArg Subtype.val hxy :))

/-- The symbol map `GL_2(J) → GL_2(F_2[z,z^{-1}])`: `presSymbol` on every entry. -/
def presGLSymbolMap : GL (Fin 2) ToeplitzJacobson →* GL (Fin 2) BinaryLaurent :=
  Units.map (presSymbol.mapMatrix : Matrix (Fin 2) (Fin 2) ToeplitzJacobson →+*
    Matrix (Fin 2) (Fin 2) BinaryLaurent).toMonoidHom

theorem presGLSymbolMap_apply (g : GL (Fin 2) ToeplitzJacobson) :
    presGLSymbolMap g = glSymbolMap 2 (presGLEquivMap g) :=
  rfl

theorem presGLSymbolMap_eq_comp : presGLSymbolMap = (glSymbolMap 2).comp presGLEquivMap :=
  MonoidHom.ext presGLSymbolMap_apply

/-- `GL_2(J) → GL_2(F_2(z))`: the symbol map followed by `F_2[z,z^{-1}] ⊆ F_2(z)`. -/
def presGLFieldSymbolMap : GL (Fin 2) ToeplitzJacobson →* GL (Fin 2) GHW.BinaryRatFunc :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2)
    (algebraMap BinaryLaurent GHW.BinaryRatFunc)).comp presGLSymbolMap

theorem presGLFieldSymbolMap_apply (g : GL (Fin 2) ToeplitzJacobson) :
    presGLFieldSymbolMap g = GHW.glFieldSymbolMap (presGLEquivMap g) :=
  rfl

theorem presGLFieldSymbolMap_eq_comp :
    presGLFieldSymbolMap = GHW.glFieldSymbolMap.comp presGLEquivMap :=
  MonoidHom.ext presGLFieldSymbolMap_apply

/-- The kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite. -/
theorem isLocallyFiniteGroup_ker_presGLSymbolMap : IsLocallyFiniteGroup presGLSymbolMap.ker := by
  rw [presGLSymbolMap_eq_comp]
  exact isLocallyFiniteGroup_ker_comp_presGLEquivMap _ (isLocallyFiniteGroup_ker_glSymbolMap 2)

theorem isLocallyFiniteGroup_ker_presGLFieldSymbolMap :
    IsLocallyFiniteGroup presGLFieldSymbolMap.ker := by
  rw [presGLFieldSymbolMap_eq_comp]
  refine isLocallyFiniteGroup_ker_comp_presGLEquivMap _ ?_
  rw [GHW.ker_glFieldSymbolMap]
  exact isLocallyFiniteGroup_ker_glSymbolMap 2

/-- **Printed (tex 1146--1151)**, at `J = F_2⟨s,t | ts=1⟩`.  "Every countable subgroup of
$\mathrm{GL}_2$ over a field has the Haagerup property~\cite[Theorem~4]{GHW}, and the kernel of
$\mathrm{GL}_2(J)\to\mathrm{GL}_2(\F_2[z,z^{-1}])$ is locally finite, so a Kazhdan subgroup of
$\mathrm{GL}_2(J)$ has finite image in $\mathrm{GL}_2(\F_2(z))$ and a locally finite subgroup of
finite index, and is finite."  The symbol sends `s ↦ z` and `t ↦ z^{-1}`. -/
def PrintedPresentedJacobsonRankTwoKazhdanFiniteField : Prop :=
  GHW.PrintedGHWTheoremFour ∧
    presSymbol presS = LaurentPolynomial.T 1 ∧ presSymbol presT = LaurentPolynomial.T (-1) ∧
      IsLocallyFiniteGroup presGLSymbolMap.ker ∧
        ∀ L : Subgroup (GL (Fin 2) ToeplitzJacobson), HasKazhdanPropertyT.{0, 0} L →
          Finite (L.map presGLFieldSymbolMap) ∧
            (presGLFieldSymbolMap.subgroupMap L).ker.FiniteIndex ∧
              IsLocallyFiniteGroup (presGLFieldSymbolMap.subgroupMap L).ker ∧ Finite L

theorem printedPresentedJacobsonRankTwoKazhdanFiniteField :
    PrintedPresentedJacobsonRankTwoKazhdanFiniteField :=
  ⟨GHW.printedGHWTheoremFour, presSymbol_presS, presSymbol_presT,
    isLocallyFiniteGroup_ker_presGLSymbolMap, fun L hL ↦
      JacobsonRankTwo.manuscriptSentence_kazhdanSubgroupFinite _ _ presGLFieldSymbolMap
        isLocallyFiniteGroup_ker_presGLFieldSymbolMap
        (fun M hM ↦ GHW.printedGHWTheoremFour GHW.BinaryRatFunc M hM) L hL⟩

end

end JacobsonPresented
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.presGLEquivMap_injective
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.isLocallyFiniteGroup_ker_presGLSymbolMap
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.printedPresentedJacobsonRankTwoKazhdanFiniteField

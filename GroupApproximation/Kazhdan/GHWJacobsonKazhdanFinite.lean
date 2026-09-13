import GroupApproximation.Kazhdan.GHWTheoremFourClosed
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankTwoCarrier
import GroupApproximation.Meta.AxiomGuard

/-!
# Kazhdan subgroups of `GL_2(J)` are finite, along the printed route

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1151):

> Every countable subgroup of `GL_2` over a field has the Haagerup property [GHW, Theorem 4], and
> the kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, so a Kazhdan subgroup of
> `GL_2(J)` has finite image in `GL_2(F_2(z))` and a locally finite subgroup of finite index, and
> is finite.

`JacobsonSymbol.manuscriptSentence_jacobsonRankTwoKazhdanFinite` proves the second clause with the
image in `GL_2(F_2[z,z^{-1}])`, whose Haagerup property it proves directly.  This module follows
the printed deduction instead.

* `F_2(z)` is the fraction field `BinaryRatFunc` of `F_2[z,z^{-1}]`, and `glFieldSymbolMap` is the
  symbol map `GL_2(J) → GL_2(F_2(z))`.  Its kernel is the kernel of the symbol map to
  `GL_2(F_2[z,z^{-1}])` (`ker_glFieldSymbolMap`), which is locally finite.
* Every countable subgroup of `GL_2(F_2(z))` has the Haagerup property (`printedGHWTheoremFour`),
  so `JacobsonRankTwo.manuscriptSentence_kazhdanSubgroupFinite` gives the conclusion
  (`printedJacobsonRankTwoKazhdanFiniteField`).
-/

namespace GroupApproximation
namespace GHW

open Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents
  Manuscript.OneSidedMFRadical.JacobsonSymbol JacobsonLaurent

/-- `F_2(z)`, the fraction field of `F_2[z,z^{-1}]`. -/
abbrev BinaryRatFunc : Type := FractionRing BinaryLaurent

/-- The symbol map `GL_2(J) → GL_2(F_2(z))`. -/
noncomputable def glFieldSymbolMap : GL (Fin 2) ↥jacobsonAlgebra →* GL (Fin 2) BinaryRatFunc :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap BinaryLaurent BinaryRatFunc)).comp
    (glSymbolMap 2)

/-- The kernel of `GL_2(J) → GL_2(F_2(z))` is the kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])`. -/
theorem ker_glFieldSymbolMap : glFieldSymbolMap.ker = (glSymbolMap 2).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  refine ⟨fun h ↦ GHW.glMap_injective (IsFractionRing.injective BinaryLaurent BinaryRatFunc) ?_,
    fun h ↦ ?_⟩
  · rw [map_one]
    exact h
  · show Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap BinaryLaurent BinaryRatFunc)
      (glSymbolMap 2 g) = 1
    rw [h, map_one]

/-- **Printed (tex 1146--1151), along the printed route.**  The kernel of
`GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, and every Kazhdan subgroup of `GL_2(J)` has
finite image in `GL_2(F_2(z))`, a locally finite subgroup of finite index, and is finite. -/
def PrintedJacobsonRankTwoKazhdanFiniteField : Prop :=
  IsLocallyFiniteGroup (glSymbolMap 2).ker ∧
    ∀ L : Subgroup (GL (Fin 2) ↥jacobsonAlgebra), HasKazhdanPropertyT.{0, 0} L →
      Finite (L.map glFieldSymbolMap) ∧ (glFieldSymbolMap.subgroupMap L).ker.FiniteIndex ∧
        IsLocallyFiniteGroup (glFieldSymbolMap.subgroupMap L).ker ∧ Finite L

/-- **Printed (tex 1146--1151)**, closed: GHW Theorem 4 at `F_2(z)` and the locally finite kernel
give the finiteness of Kazhdan subgroups of `GL_2(J)`. -/
theorem printedJacobsonRankTwoKazhdanFiniteField : PrintedJacobsonRankTwoKazhdanFiniteField := by
  have hker : IsLocallyFiniteGroup glFieldSymbolMap.ker := by
    rw [ker_glFieldSymbolMap]
    exact isLocallyFiniteGroup_ker_glSymbolMap 2
  exact ⟨isLocallyFiniteGroup_ker_glSymbolMap 2, fun L hL ↦
    Manuscript.OneSidedMFRadical.JacobsonRankTwo.manuscriptSentence_kazhdanSubgroupFinite _ _
      glFieldSymbolMap hker (fun M hM ↦ printedGHWTheoremFour BinaryRatFunc M hM) L hL⟩

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.ker_glFieldSymbolMap
#audit_closed_axioms GroupApproximation.GHW.printedJacobsonRankTwoKazhdanFiniteField

import GroupApproximation.Sofic.LiteralAffineFreeProductSource
import GroupApproximation.Sofic.BassSerreHullGeometry
import GroupApproximation.Sofic.HullSuitableDefectSubgroup

/-!
# Bass--Serre adapter for the amplified affine source

Kept separate from the source package so the algebraic torsion-free and
finite-presentation results do not depend on the graph development.
-/

namespace GroupApproximation.LiteralAffineFreeProductBassSerre

open scoped commutatorElement

open Monoid Monoid.CoprodI
open LiteralAffineCongruenceSource
open LiteralAffineFreeProductSource

noncomputable section

abbrev BassSerreVertex := BassSerreFreeProduct.Vertex Envelope

def bassSerreBaseEdge : BassSerreVertex × BassSerreVertex :=
  BassSerreFreeProduct.baseEdge Envelope

/-- The generic free-product action applies definitionally to the amplified
ambient. Its base edge has trivial pointwise stabilizer. -/
theorem bassSerreBaseEdge_pointwiseStabilizer_eq_bot :
    MulAction.stabilizer Ambient bassSerreBaseEdge = ⊥ :=
  BassSerreFreeProduct.baseEdge_pointwiseStabilizer_eq_bot Envelope

/-! ## The concrete Hull-facing action package

The free-product amplification was chosen precisely so that its Bass--Serre
action is acylindrical.  The compression defect is a nontrivial normal subgroup
of the torsion-free ambient, hence is infinite and `s`-normal.  These are the
fully algebraic and acylindricity inputs to the remaining Osin step: proving
that this particular `s`-normal subgroup acts non-elementarily on the tree.
-/

/-- The path-metric Bass--Serre action of the amplified ambient is isometric. -/
theorem bassSerre_isometric :
    HullGeometry.IsIsometricAction Ambient
      (BassSerreHullGeometry.PathVertex Envelope) :=
  BassSerreHullGeometry.isIsometricAction Envelope

/-- The concrete amplified Bass--Serre path metric is one-hyperbolic. -/
theorem bassSerre_hyperbolic :
    HullGeometry.IsHyperbolicSpace 1
      (BassSerreHullGeometry.PathVertex Envelope) :=
  BassSerreHullGeometry.isHyperbolicSpace Envelope

/-- The same action is acylindrical, with the counting proof coming from the
trivial stabilizer of every Bass--Serre edge. -/
theorem bassSerre_acylindrical :
    HullGeometry.IsAcylindrical Ambient
      (BassSerreHullGeometry.PathVertex Envelope) :=
  BassSerreHullGeometry.isAcylindrical Envelope

/-- The amplified compression defect is `s`-normal.  This is unconditional:
its selected marked commutator is nontrivial, ambient torsion-freeness makes
its powers infinite, and the defect is normal by construction. -/
theorem amplifiedDefect_isSNormal :
    HullSuitable.IsSNormal amplifiedDefectData.core.defectNormal :=
  amplifiedDefectData.defectNormal_isSNormal ambient_isPowerTorsionFree

/-- In particular, the subgroup whose Bass--Serre dynamics remain to be
analyzed is genuinely infinite; no non-elementarity argument may be discharged
by replacing it with a finite or trivial candidate. -/
theorem amplifiedDefect_infinite :
    Infinite amplifiedDefectData.core.defectNormal :=
  amplifiedDefectData.defectNormal_infinite ambient_isPowerTorsionFree

/-- Hull's finite-normalizer suitability clause is automatic for the amplified
defect because the whole free-product ambient is torsion-free. -/
theorem amplifiedDefect_normalizesNoNontrivialFinite :
    HullSuitable.NormalizesNoNontrivialFinite
      amplifiedDefectData.core.defectNormal :=
  amplifiedDefectData.defectNormal_normalizesNoNontrivialFinite
    ambient_isPowerTorsionFree

/-! ## An explicit defect element crossing the Bass--Serre edge

The marked compression commutator lies in the left free factor.  Conjugating
it by the right generator and multiplying by its inverse produces an element
of the normal defect whose word crosses the Bass--Serre edge.  This is the
concrete element whose axis is used in the non-elementarity proof; no choice
of a hypothetical loxodromic element is introduced.
-/

/-- The selected nonidentity generator of the amplified normal defect. -/
def markedDefect : Ambient :=
  ⁅amplifiedDefectData.s,
    amplifiedDefectData.iota amplifiedDefectData.witness⁆

theorem markedDefect_mem :
    markedDefect ∈ amplifiedDefectData.core.defectNormal :=
  by simpa only [markedDefect] using
    amplifiedDefectData.witness_commutator_mem_defectNormal

theorem markedDefect_ne_one : markedDefect ≠ 1 :=
  by simpa only [markedDefect] using
    amplifiedDefectData.witness_commutator_ne_one

/-- The marked defect is still a literal left-factor element after
free-product amplification. -/
theorem markedDefect_mem_leftFactor :
    markedDefect ∈ BassSerreFreeProduct.leftFactor Envelope := by
  refine ⟨⁅literalBareDefectSourceData.s,
    literalBareDefectSourceData.iota literalBareDefectSourceData.witness⁆, ?_⟩
  simp only [markedDefect, amplifiedDefectData, BareDefectSourceData.mapAmbient,
    envelopeEmbedding, MonoidHom.comp_apply, map_commutatorElement]

/-- The unit translation in the right free factor. -/
def rightShift : Ambient :=
  Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))

theorem rightShift_mem_rightFactor :
    rightShift ∈ BassSerreFreeProduct.rightFactor Envelope :=
  ⟨Multiplicative.ofAdd (1 : ℤ), rfl⟩

theorem rightShift_not_mem_leftFactor :
    rightShift ∉ BassSerreFreeProduct.leftFactor Envelope := by
  intro hleft
  have hinter : rightShift ∈
      BassSerreFreeProduct.leftFactor Envelope ⊓
        BassSerreFreeProduct.rightFactor Envelope :=
    ⟨hleft, rightShift_mem_rightFactor⟩
  rw [BassSerreFreeProduct.leftFactor_inf_rightFactor Envelope] at hinter
  have hone : rightShift = 1 := by simpa using hinter
  exact inr_one_ne_one hone

/-- The explicit commutator between the right translation and the marked
left-factor defect. -/
def crossingDefect : Ambient :=
  rightShift * markedDefect * rightShift⁻¹ * markedDefect⁻¹

/-- Normality puts the crossing commutator back in the compression defect. -/
theorem crossingDefect_mem :
    crossingDefect ∈ amplifiedDefectData.core.defectNormal := by
  have hd := markedDefect_mem
  have hconj : rightShift * markedDefect * rightShift⁻¹ ∈
      amplifiedDefectData.core.defectNormal :=
    (inferInstance : amplifiedDefectData.core.defectNormal.Normal).conj_mem
      markedDefect hd rightShift
  exact amplifiedDefectData.core.defectNormal.mul_mem hconj
    (amplifiedDefectData.core.defectNormal.inv_mem hd)

/-- The crossing commutator is nonidentity.  If it vanished, the marked
left-factor element would fix both the left base vertex and its right
translate.  Those vertices are distinct, while faithfulness along the unique
path between them forces such an element to be the identity. -/
theorem crossingDefect_ne_one : crossingDefect ≠ 1 := by
  intro hcross
  have hconj : rightShift * markedDefect * rightShift⁻¹ = markedDefect := by
    apply mul_inv_eq_one.mp
    simpa only [crossingDefect] using hcross
  have hfixBase : markedDefect • BassSerreFreeProduct.baseLeft Envelope =
      BassSerreFreeProduct.baseLeft Envelope :=
    (BassSerreFreeProduct.smul_baseLeft_eq_iff Envelope markedDefect).mpr
      markedDefect_mem_leftFactor
  have hfixShift : markedDefect •
      (rightShift • BassSerreFreeProduct.baseLeft Envelope) =
      rightShift • BassSerreFreeProduct.baseLeft Envelope := by
    calc
      markedDefect • (rightShift • BassSerreFreeProduct.baseLeft Envelope) =
          (rightShift * markedDefect * rightShift⁻¹) •
            (rightShift • BassSerreFreeProduct.baseLeft Envelope) := by
              rw [hconj]
      _ = rightShift •
          (markedDefect • BassSerreFreeProduct.baseLeft Envelope) := by
            simp only [mul_smul, inv_smul_smul]
      _ = rightShift • BassSerreFreeProduct.baseLeft Envelope := by
            rw [hfixBase]
  have hvertices : BassSerreFreeProduct.baseLeft Envelope ≠
      rightShift • BassSerreFreeProduct.baseLeft Envelope := by
    intro heq
    apply rightShift_not_mem_leftFactor
    apply (BassSerreFreeProduct.smul_baseLeft_eq_iff Envelope rightShift).mp
    exact heq.symm
  have hone := BassSerreHullGeometry.eq_one_of_fixes_distinct Envelope hvertices
    hfixBase hfixShift
  exact markedDefect_ne_one hone

/-! ## Linear normal-form growth of the crossing defect -/

/-- The explicit crossing commutator is loxodromic on the Bass--Serre tree.
Its indexed normal form is a cyclically reduced four-syllable word, so its
`n`-th power has exactly `4n` syllables. -/
theorem crossingDefect_isLoxodromic :
    HullGeometry.IsLoxodromic crossingDefect
      (BassSerreFreeProduct.baseLeft Envelope :
        BassSerreHullGeometry.PathVertex Envelope) := by
  classical
  let x : Envelope := Classical.choose markedDefect_mem_leftFactor
  have hxEq : Monoid.Coprod.inl x = markedDefect :=
    Classical.choose_spec markedDefect_mem_leftFactor
  have hx : x ≠ 1 := by
    intro hxone
    apply markedDefect_ne_one
    exact hxEq.symm.trans (by simp [hxone])
  let y : BinaryCoprodNormalForm.factor Envelope true :=
    MulEquiv.ulift.symm (Multiplicative.ofAdd (1 : ℤ))
  have hy : y ≠ 1 := by
    intro hyone
    have hone' : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      calc
        Multiplicative.ofAdd (1 : ℤ) = MulEquiv.ulift y := by simp [y]
        _ = MulEquiv.ulift 1 := congrArg MulEquiv.ulift hyone
        _ = 1 := map_one _
    norm_num at hone'
  have hxi : x⁻¹ ≠ 1 := inv_ne_one.mpr hx
  have hyi : y⁻¹ ≠ 1 := inv_ne_one.mpr hy
  let u : CoprodI.NeWord (BinaryCoprodNormalForm.factor Envelope) true false :=
    ((CoprodI.NeWord.singleton y hy).append Bool.false_ne_true.symm
      (CoprodI.NeWord.singleton
        (M := BinaryCoprodNormalForm.factor Envelope) (i := false) x hx)).append
          Bool.false_ne_true
        ((CoprodI.NeWord.singleton y⁻¹ hyi).append Bool.false_ne_true.symm
          (CoprodI.NeWord.singleton
            (M := BinaryCoprodNormalForm.factor Envelope) (i := false) x⁻¹ hxi))
  have huLength : u.toList.length = 4 := by
    simp [u, CoprodI.NeWord.toList]
  have huProd : u.prod =
      BinaryCoprodNormalForm.toIndexed Envelope crossingDefect := by
    rw [crossingDefect, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp only [rightShift, BinaryCoprodNormalForm.toIndexed_inr]
    change u.prod = CoprodI.of y *
      BinaryCoprodNormalForm.toIndexed Envelope markedDefect *
        (CoprodI.of y)⁻¹ *
          (BinaryCoprodNormalForm.toIndexed Envelope markedDefect)⁻¹
    rw [← hxEq, BinaryCoprodNormalForm.toIndexed_inl]
    simp [u, CoprodI.NeWord.append_prod, mul_assoc]
  apply BassSerreHullGeometry.isLoxodromic_of_sylLength_pow_lower
    Envelope crossingDefect 4 (by omega)
  intro n
  cases n with
  | zero => simp [FreeProductCyclic.sylLength]
  | succ n =>
      rw [map_pow, ← huProd]
      simpa [huLength] using
        (FreeProductCyclic.sylLength_npow Bool.false_ne_true.symm u n).ge

end

end GroupApproximation.LiteralAffineFreeProductBassSerre

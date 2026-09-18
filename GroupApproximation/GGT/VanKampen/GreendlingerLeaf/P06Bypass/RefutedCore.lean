import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.RefutedDef
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# The refuted cell pocket walk binder, from the P07 inner two-arc residuals

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p06-01`.  The target is
`CellPocketWalkRefutedBelowSectionStatement` (`RefutedDef.lean`).

## Proof route

This is the body of `P07LakeExclusion.proof_of_innerTwoArcLong` (`InnerTwoArc.lean:86–116`) with
the goal `False` from the start instead of after `exfalso`.

* **Thresholds** (`refutedBelowSection_of_innerTwoArcLong`): `ε₀ = 0`; `ρ₀ = max 2 ρ₁`, where `ρ₁`
  comes from `SameCellSimplePocket.exists_rho_large`, so `λ⁻¹ (3ε + c) < (μ/2) ρ` for `ρ ≥ ρ₁`.
  `ε₀` is never raised: `OsinCCondition` is not monotone in `ε`.
* **Fixed parameters** (`refutedBelowInput_of_innerTwoArcLong`).  Let `X = S.diagram`.
  * Least area passes to `X` (`OuterCellThickening.leastArea_of_oEquivalent`).
  * Both Euler equalities of the walk hold (`cellPocketWalkEuler`).
  * A relator cell is kept on the side of the pocket region, off `a` and `b`
    (`exists_kept_of_cellPocketRegion_of_leastArea`).  It is off every region candidate because at
    least area no relator word has value one, while region faces are G-cells.
  * The residual gives a two-arc lake-fill exit of `X`.  Clause (b) below
    `X.rCellCount = Δ.rCellCount` refutes it (`Piece06.false_of_lakeFillTwoArcExit`), with relator
    words longer than one letter from `2 ≤ ρ` (`one_lt_length_of_two_le_rho`).
* **The enclosed variant** (`refutedBelowSection_of_innerPocketEnclosed`): compose with
  `P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed` (`InnerTwoArcLong.lean:85`).

## Status

These are `_of_` reductions to the P07 residuals `CellPocketInnerTwoArcLongStatement` and
`InnerPocketEnclosedTwoArcStatement`, which are on disk and still open (gl-p07-15).  Nothing here
adds a hypothesis beyond what the P07 residuals already need.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The refuted binder at fixed parameters, from the long-word inner two-arc residual.**  The
body of `P07LakeExclusion.proof_of_innerTwoArcLong` after its thresholds, with goal `False`. -/
theorem refutedBelowInput_of_innerTwoArcLong
    (h : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho2 : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta _ hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  obtain ⟨hinner, houter⟩ :=
    cellPocketWalkEuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K
    hfirst hsecond h₁ hlea' (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  rw [PocketRegion.ofNoncrossingClosedWalkEuler_faces] at hkept
  have hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
    fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea' C hC
  have hcell : ∀ z : RegionCandidate D eps S.diagram, (cell S.diagram kept).face ∉ z.1 := by
    intro z hkz
    have hz := (z.2.boundary.all_gCells _ hkz).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word _ (cell_mem S.diagram kept)] at hz
    exact hvalue _ (cell_mem S.diagram kept) hz
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hbelow
  exact Piece06.false_of_lakeFillTwoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge
    hlea' hbelow'
    (h D eps S.diagram a b K hij hai hbi (S.pairwise a ha b hb hab) S.label_admissible
      (one_lt_length_of_two_le_rho hcondition hrho2) hfirst hsecond h₁ h₂ hw hoff hinner houter _
      (cell_mem S.diagram kept) hkept (hcell a) (hcell b))

/-- **The refuted section statement from the long-word inner two-arc residual.**  Thresholds
`ε₀ = 0` and `ρ₀ = max 2 ρ₁`, as in `P07LakeExclusion.proof_of_innerTwoArcLong`. -/
theorem refutedBelowSection_of_innerTwoArcLong
    (h : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v}) :
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, lt_of_lt_of_le Nat.zero_lt_two (le_max_left 2 rho1),
    fun rho hrho W hcondition => ?_⟩
  exact refutedBelowInput_of_innerTwoArcLong h hcondition hlambda hlambda1 hc hmu hmu1
    (le_of_max_le_left hrho) (hrho1 rho (le_of_max_le_right hrho))

/-- **The refuted section statement from the enclosed inner pocket**, through
`P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed`. -/
theorem refutedBelowSection_of_innerPocketEnclosed
    (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  refutedBelowSection_of_innerTwoArcLong
    (P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.refutedBelowInput_of_innerTwoArcLong
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.refutedBelowSection_of_innerTwoArcLong
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.refutedBelowSection_of_innerPocketEnclosed

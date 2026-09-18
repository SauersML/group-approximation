import GroupApproximation.Manuscript.NonMF.Full.GL06e.Statements
import GroupApproximation.Manuscript.NonMF.Full.GL06e.TwoArcUnpinch
import GroupApproximation.Manuscript.NonMF.Full.GL06e.AllCellsStatement
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: the cell pocket walk binder is refuted, from the enclosed inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Two distinct selected regions `a`, `b` joining the distinct cells `Π_i`, `Π_j` of the optimal copy
of a least-area `Δ` bound, through their cell pocket walk `K`, a subdiagram `Γ_1`.  With the
exterior off the side of `K`:

* both reclosings of `K` keep the Euler characteristic (`cellPocketWalkEuler`), so the side of `K`
  is a pocket region, and it holds a relator cell `Π` (`exists_kept_of_cellPocketRegion_of_leastArea`);
* at least area no relator cell lies in a contiguity region (`cell_face_not_mem_region`), so `Π`
  is off `a` and `b`;
* the corrected enclosed inner pocket statement `GL03BPinch.InnerPocketEnclosedTwoArcCorrected`
  gives either an enclosed face set holding a relator cell with two arcs outside and short sides,
  or an enclosed face set holding every relator cell with an outer walk of length at most `2ε`;
* in the first case `twoArcExit_of_enclosed` gives a two-arc exit, which clause (b) of Lemma 9.7
  below `Δ.rCellCount` refutes (`GL06g.false_of_twoArcExit`);
* the second case is refuted by `AllCellsShortEnclosedRefutedBelowInput` (`Full/GL06e/AllCellsStatement`).

* `refutedBelowInput_of_innerPocketEnclosedCorrected`: the fixed-parameter statement.
* `refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells`: the statement beyond
  thresholds, the local restatement of `P06Bypass.CellPocketWalkRefutedBelowSectionStatement`
  (`Full/GL06e/Statements`).

The earlier route from `GL03B.InnerPocketEnclosedTwoArcLocal` is dropped, since that statement is
false (see `Full/GL03BPinch/Statement`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06e

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Refuted

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **At least area no relator cell lies in a contiguity region** (Osin, proof of Lemma 9.7(b);
`thm:hull`).  The faces of a region have boundary words of value one, the relator words do not. -/
theorem cell_face_not_mem_region {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
    {eps : ℕ} {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea) (k : Fin X.rCellCount)
    (z : RegionCandidate D eps X) : (cell X k).face ∉ z.1 := by
  intro hz
  exact DiscDiagram.leastArea_listVal_word_ne_one hlea (cell X k) (cell_mem X k)
    (by
      rw [X.relatorCell_word (cell X k) (cell_mem X k)]
      exact (z.2.boundary.all_gCells (cell X k).face hz).2)

/-- **The cell pocket walk binder is refuted below the inductive bound, at fixed parameters**
(Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121), from the corrected
enclosed inner pocket statement and the refutation of the all-cells short enclosed face set. -/
theorem refutedBelowInput_of_innerPocketEnclosedCorrected
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ}
    {mu lambda c : ℝ} (hall : AllCellsShortEnclosedRefutedBelowInput.{u, w, v} D lambda c mu eps W)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W := by
  intro _Delta _cuts hlea hbelow S _i _j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂
    hw hoff
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  have hW : ∀ word ∈ W, 1 < word.length := one_lt_length_of_two_le_rho hcondition hrho
  obtain ⟨hinner, houter⟩ :=
    cellPocketWalkEuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K
    hfirst hsecond h₁ hlea' (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter)
    (PocketRegion.ofNoncrossingClosedWalkEuler_inner_cycle hw hoff hinner houter)
  have hside : (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk := hkept
  have hdisj : Disjoint a.1 b.1 := S.pairwise a ha b hb hab
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hbelow
  rcases hencl D eps S.diagram a b K hij hai hbi hdisj S.label_admissible hW hfirst hsecond h₁ h₂
      hw hoff hinner houter (cell S.diagram kept) (cell_mem S.diagram kept) hside
      (cell_face_not_mem_region hlea' kept a) (cell_face_not_mem_region hlea' kept b) with
    ⟨_faces, _outerWalk, _k₁, _k₂, A₁, A₂, s₁, s₂, E, hC, hk₁, hk₂, hdec, hs₁, hs₂, hpos⟩ |
      ⟨faces, outerWalk, E, hcells, hlen⟩
  · exact GL06g.false_of_twoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge hlea'
      hbelow'
      (twoArcExit_of_enclosed D S.label_admissible hW E hC hk₁ hk₂ A₁ A₂ s₁ s₂ hdec hs₁ hs₂ hpos)
  · exact hall S.diagram hlea' hbelow' S.label_admissible hW kept.pos faces outerWalk E hcells hlen

end Refuted

/-- **The cell pocket walk binder is refuted below the inductive bound, beyond thresholds**
(Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121), from the corrected
enclosed inner pocket statement and the refutation of the all-cells short enclosed face set.  The
thresholds are those of the all-cells refutation, with `ρ` also at least `2` and making
`λ⁻¹ (3ε + c) < (μ/2) ρ`. -/
theorem refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hall : AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps1, heps1⟩ := hall D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps1, fun eps heps => ?_⟩
  obtain ⟨rho1, hrho1pos, hrho1⟩ := heps1 eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (lambda⁻¹ * (3 * (eps : ℝ) + c)) / mu)
  refine ⟨max rho1 (max 2 N), Nat.lt_of_lt_of_le hrho1pos (Nat.le_max_left rho1 (max 2 N)),
    fun rho hrho W hcondition => ?_⟩
  have hrho1' : rho1 ≤ rho := le_of_max_le_left hrho
  have hrest : max 2 N ≤ rho := le_of_max_le_right hrho
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrest
  have hNrho : (N : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr (le_of_max_le_right hrest)
  have hmul : 2 * (lambda⁻¹ * (3 * (eps : ℝ) + c)) < (rho : ℝ) * mu :=
    (div_lt_iff₀ hmu).mp (lt_of_lt_of_le hN hNrho)
  have hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by linarith
  exact refutedBelowInput_of_innerPocketEnclosedCorrected hencl (hrho1 rho hrho1' W hcondition)
    hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge

end GroupApproximation.Full.GL06e

#audit_axioms GroupApproximation.Full.GL06e.cell_face_not_mem_region
#audit_axioms GroupApproximation.Full.GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected
#audit_axioms GroupApproximation.Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells

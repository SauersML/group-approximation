import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch between two cells, with the hypotheses of the multiple-edge cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

`CellPocketPinchPosStatement` (`Estimating/OsinPocketCellFaceSet.lean`) is the cell analogue of
`PocketPinchLabelledPosStatement`, which fails at `ε = 1` on a full source arc with both sides of
length `ε`.  The multiple-edge cut reads the pinch only beyond thresholds, under Osin's condition,
on least-area copies, and it can supply proper arcs.  So the cell pinch is respelled additively, as
`PocketPinchLabelledSectionStatement` respells the section pinch
(`Estimating/OsinPocketPinchSection.lean`).

* `CellPocketPinchSectionInput D eps W`: at fixed parameters, a cell pocket face set in walk order
  of a least-area diagram with letter labels, whose two arcs are both shorter than the boundaries of
  their cells, has an O-equivalent copy with letter labels and a simple cell pocket face set.
* `CellPocketPinchSectionStatement`: that input beyond thresholds for `ε` and `ρ`, for every family
  satisfying `C(ε, μ, λ, c, ρ)`, with the quantifier prefix of
  `PocketPinchLabelledSectionStatement`.
* `cellPocketPinchSectionStatement_of_pos`: the positive cell pinch gives it, at `ε₀ = ρ₀ = 1`.
* `CellPocketFaceSet.copyRegion_of_pinchSection`: from the input, the region data of the copy form
  of `MultipleEdgePocketRegionInput`, as `CellPocketFaceSet.copyRegion_of_pinch` gives from the
  positive pinch.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded WordMetric

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pinch at fixed parameters, on proper arcs.**  A cell pocket face set in walk order of a
least-area diagram whose labels are letters, with both arcs shorter than the boundaries of their
cells, has an O-equivalent copy with letter labels and a simple cell pocket face set. -/
def CellPocketPinchSectionInput (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple

end Input

/-- **The pinch between two cells with the hypotheses of the multiple-edge cut.**  Beyond
thresholds for `ε` and `ρ`, for a family satisfying Osin's condition, `CellPocketPinchSectionInput`
holds. -/
def CellPocketPinchSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketPinchSectionInput.{u, w, v} D eps W

/-- The positive cell pinch gives the section cell pinch, at `ε₀ = ρ₀ = 1`. -/
theorem cellPocketPinchSectionStatement_of_pos (h : CellPocketPinchPosStatement.{u, w, v}) :
    CellPocketPinchSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  refine ⟨1, fun eps heps => ⟨1, Nat.one_pos, fun _ _ W _ X i j _ hlabel K hK _ _ => ?_⟩⟩
  exact h D eps (Nat.lt_of_lt_of_le Nat.one_pos heps) W X i j hlabel K hK

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The region data of the copy form of `MultipleEdgePocketRegionInput`, from the section cell
pinch.**  A cell pocket face set in walk order, of a least-area diagram with letter labels and proper
arcs, gives an O-equivalent copy with letter labels and a pocket region with a relator cell inside,
two cells outside, the inverse complement cycle `s_1 t_1 s_2 t_2`, sides of word norm at most `ε`,
and both cycles following their boundaries. -/
theorem copyRegion_of_pinchSection (hpinch : CellPocketPinchSectionInput.{u, w, v} D eps W)
    (hlea : X.LeastArea) (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) :
    ∃ X' : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      ∃ (P : PocketRegion X') (C : RelatorCell X'.toCombMap X'.outerFace W)
        (i' j' : Fin X'.rCellCount) (s₁ s₂ : List X'.toCombMap.Dart)
        (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j')),
        C ∈ X'.relatorCells ∧ C.face ∈ P.faces ∧
          (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
          invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps ∧
          P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary := by
  obtain ⟨X', i', j', K', hE, hlabel', hsimple⟩ := hpinch X i j hlea hlabel K hK hfirst hsecond
  obtain ⟨P, C, hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout, -⟩ :=
    K'.exists_pocketRegion_of_simple hsimple
  exact ⟨X', hE, hlabel', P, C, i', j', K'.firstSide, K'.secondSide, K'.firstArc, K'.secondArc,
    hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout⟩

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchSectionStatement_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.copyRegion_of_pinchSection

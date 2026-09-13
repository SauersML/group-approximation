import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapRose
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# The wrap rose at a positive side bound

A model test for `PocketPinchLabelledPosStatement` (`Estimating/OsinPocketPinchPositive.lean`).  The
three-petal rose `OsinPocketWrapRose.wrapDiagram` refutes the pinch at `ε = 0`
(`OsinPocketWrapRose.pocketPinchWrapRefutation`).  At `ε ≥ 1` the conclusion of the pinch holds on
the rose itself.  The face set `{R}` of the relator cell `R = [5]` has source `Π`, kept cell `R`,
first side `[5]`, an empty second side and empty arcs, and it is a simple pocket face set in the
positions `0` and `1`: its cycle is the single loop `[5]`, whose reversal `4` lies in `κ`.

* `rescueK eps heps`: that pocket face set, for `1 ≤ eps`.
* `rescueK_simple`: it is simple.
* `wrapRoseRescue`: for every `ε ≥ 1`, every pocket face set of the rose in the positions `0` and
  `1` has an O-equivalent copy, the rose itself, with a simple pocket face set in the same
  positions.

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseRescue

open OsinPocketWrapRose
open OsinPocketPinchedTwoGonModel (G gx gy D)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

/-- The face set `{R}`. -/
def rescueFaces : Finset wrapDiagram.toCombMap.Face := {face 3}

theorem face_mem_rescueFaces_iff (i : Fin 4) : face i ∈ rescueFaces ↔ i = 3 :=
  Finset.mem_singleton.trans (face_eq_iff i 3)

theorem rescueBoundaryDart_iff (d : Fin 6) :
    IsBoundaryDart wrapDiagram.toCombMap rescueFaces d ↔ d ∈ ([5] : List (Fin 6)) := by
  change (M.faceOf d ∈ ({face 3} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 3} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The one boundary dart of `{R}`. -/
def rescueCycle : BoundaryCycle wrapDiagram.toCombMap rescueFaces where
  cycle := ([5] : List (Fin 6))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := List.nodup_singleton _
  cycle_mem_iff := fun d => (rescueBoundaryDart_iff d).symm

/-- The empty arc of `Π` at position `0`. -/
def rescueSourceArc : Embedded.CyclicArc (Embedded.cellDarts wrapDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem rescueSourceArc_darts : rescueSourceArc.darts = [] :=
  rfl

/-- The empty arc of the exterior boundary at position `0`. -/
def rescueTargetArc : Embedded.CyclicArc (Embedded.outerDarts wrapDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem rescueTargetArc_darts : rescueTargetArc.darts = [] :=
  rfl

/-- The cycle of `{R}` is the first side `[5]`, with empty arcs and an empty second side. -/
theorem rescue_decomposition :
    (rescueCycle : BoundaryCycle wrapDiagram.toCombMap rescueFaces).cycle =
      ([5] : List wrapDiagram.toCombMap.Dart) ++
        Embedded.invDarts wrapDiagram rescueSourceArc.darts ++ [] ++ rescueTargetArc.darts := by
  rw [rescueSourceArc_darts, rescueTargetArc_darts]
  rfl

/-- The first side `[5]` has norm at most `1`, since its label is a letter. -/
theorem rescue_side_norm {eps : ℕ} (heps : 1 ≤ eps) :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord wrapDiagram ([5] : List wrapDiagram.toCombMap.Dart))) ≤ eps :=
  (PocketFaceSet.wordNorm_dartWord_le_length wrapDiagram_letters _).trans (by simpa using heps)

/-- **The pocket face set `{R}`** at a side bound `ε ≥ 1`, with source `Π` and kept cell `R`. -/
noncomputable def rescueK (eps : ℕ) (heps : 1 ≤ eps) : PocketFaceSet D eps wrapDiagram 0 1 where
  faces := rescueFaces
  outerFace_not_mem := fun h => absurd ((face_mem_rescueFaces_iff 2).mp h) (by decide)
  source := 0
  source_not_mem := fun h => absurd ((face_mem_rescueFaces_iff 1).mp h) (by decide)
  kept := ⟨1, by decide⟩
  kept_mem := (face_mem_rescueFaces_iff 3).mpr rfl
  sourceArc := rescueSourceArc
  targetArc := rescueTargetArc
  firstSide := [5]
  secondSide := []
  boundary := rescueCycle
  decomposition := rescue_decomposition
  firstSide_length_le := by simpa using heps
  secondSide_length_le := Nat.zero_le _
  firstSide_norm_le := rescue_side_norm heps
  secondSide_norm_le := wrap_empty_side_norm.trans (Nat.zero_le _)
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- **`{R}` is simple**: its cycle is the single loop `[5]`, and the reversal `4` is not in it. -/
theorem rescueK_simple (eps : ℕ) (heps : 1 ≤ eps) : (rescueK eps heps).Simple :=
  (⟨List.cons_ne_nil _ _, List.IsChain.singleton _, vertexOf_eq _ _, List.nodup_singleton _,
      fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        decide⟩ :
    IsSimpleClosedWalk wrapDiagram.toCombMap ([5] : List wrapDiagram.toCombMap.Dart))

/-- **The wrap rose at a positive side bound** (model test).  For every `ε ≥ 1`, every pocket face
set of the rose in the positions `0` and `1` has an O-equivalent copy with a simple pocket face set
in the same positions: the rose itself, with `{R}`. -/
def WrapRoseRescue : Prop :=
  ∀ eps : ℕ, 1 ≤ eps → ∀ _K : PocketFaceSet D eps wrapDiagram 0 1,
    ∃ (X' : DiscDiagram.{0, 0, 0} wrapW) (K' : PocketFaceSet D eps X' 0 1),
      Nonempty (OEquivalentDiscDiagram wrapDiagram X') ∧ K'.Simple

theorem wrapRoseRescue : WrapRoseRescue := by
  intro eps heps _K
  exact ⟨wrapDiagram, rescueK eps heps, ⟨OEquivalentDiscDiagram.refl _⟩, rescueK_simple eps heps⟩

#audit_axioms rescueBoundaryDart_iff
#audit_axioms rescueCycle
#audit_axioms rescue_decomposition
#audit_axioms rescue_side_norm
#audit_axioms rescueK
#audit_axioms rescueK_simple
#audit_closed_axioms wrapRoseRescue

end GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseRescue

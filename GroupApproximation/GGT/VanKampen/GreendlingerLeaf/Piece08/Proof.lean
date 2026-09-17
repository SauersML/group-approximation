import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetRegionsProved
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.Absorb
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 08: a pocket face set with a proper source arc

Target: `OsinSectionPocketFaceSetProperSectionStatement` (`Estimating/OsinPocketPinchSection`),
the face set between two distinct exterior regions of one cell to one section, as a
`PocketFaceSet` in walk order of an O-equivalent copy with letter labels, whose source arc `t_1`
is shorter than the boundary of its source cell.

## Mathematical proof

Fix the data `Delta`, `cuts`, least area, the family `S`, the cell `i`, the section `j` and two
distinct exterior regions `a ≠ b` of `i` to `j`.  The proved producer
`sectionPocketFaceSetInput_of_keptCell sectionPocketKeptCell` gives an O-equivalent copy `X'` with
letter labels and a pocket face set `K` in walk order, `∂K = s_1 t_1^{-1} s_2 t_2`.  Let `p` be
the face of the source cell `Π`.  Since `|t_1| ≤ |∂Π|`:

* **Case A** (`|t_1| < |∂Π|`).  `K` itself is the witness.
* **Case B** (`|t_1| = |∂Π|`, and some relator cell `k` has its face outside `F ∪ {p}`, where
  `F = K.faces`).  Absorb `Π` into the pocket (`Piece08/Absorb.lean`, `absorbSource`): the face
  set `F ∪ {p}`, source `k`, empty source arc, the same sides and target arc.
  - Its boundary darts are exactly `s_1 s_2 t_2`.  As `t_1` is full, `invDarts t_1` is the set of
    darts whose reverse lies in `p`.  A dart of `s_1 s_2 t_2` is a boundary dart of `F` outside
    `invDarts t_1` (the cycle has no repeats), so its reverse is neither in `F` nor in `p`.  A
    boundary dart `d` of `F ∪ {p}` is not in `p`: otherwise `alpha d ∈ invDarts t_1`, a boundary
    dart of `F`, so `alpha d` has its face in `F`, against `d` being a boundary dart.  So `d` is a
    boundary dart of `F`, and not in `invDarts t_1` since its reverse is not in `p`.
  - The cycle is nonempty: a face set missing the exterior face and containing `p` has a
    boundary dart, else it is closed under `alpha` and `sigma` and by connectivity of the planar
    map contains the exterior face.
  - It is a closed walk: `invDarts t_1` is a closed walk, since the first dart `alpha x` of the
    reversed arc (`x` the last dart of `t_1`) starts at the vertex of `facePerm x = y`, the first
    dart of `t_1`, where the reversed arc ends.  Cutting a closed stretch out of a closed walk
    leaves a closed walk (`Piece08/Walk.lean`).
  - The empty source arc is proper, as every face boundary is nonempty.
  - Sides, bounds and the target arc are unchanged, so all length, norm and position fields
    carry over.
* **Case C** (`|t_1| = |∂Π|`, and every relator cell lies in `F ∪ {p}`).  The pocket reads
  `s_1 s_2 t_2` around every relator cell of `X'`.  This case is not closed here.  The producer's
  conclusion forgets the two regions `a`, `b`, whose contiguity arcs on `∂Π` are what make `t_1`
  proper in Osin's argument (Lemma 9.7(b)).  The sides may already have length `ε`, so the trims
  of `Estimating/OsinPocketArcTrim` do not apply.  The case is isolated as the residual input
  `FullSourceLakeInput`.

## What is proved here

* `properInput_of_fullSourceLake`: Cases A and B, pointwise in the parameters, from the residual
  Case C.
* `proof_of_fullSourceLake`: the target statement from the uniform residual
  `OsinFullSourceLakeStatement`.

The unconditional endpoint `Piece08.proof` needs Case C.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

universe u w v

open Embedded HullSC WordMetric
open scoped Classical

section Residual

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Residual Case C.**  The proper face set, when the producer's pocket face set has a full
source arc and every relator cell lies in the pocket or is the source cell. -/
def FullSourceLakeInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  ∀ X' : DiscDiagram.{u, w, v} W,
                    Nonempty (OEquivalentDiscDiagram S.diagram X') →
                      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) →
                      ∀ K : PocketFaceSet D eps X' (cuts.cut j.castSucc) (cuts.cut j.succ),
                        K.ClosedWalk →
                          K.sourceArc.length = (cellDarts X' K.source).length →
                          (∀ k : Fin X'.rCellCount,
                            (cell X' k).face ∈ insert (cell X' K.source).face K.faces) →
                  ∃ X'' : DiscDiagram.{u, w, v} W,
                    Nonempty (OEquivalentDiscDiagram S.diagram X'') ∧
                      (∀ d, (symmetricLabelAlphabet D).IsLetter (X''.label d)) ∧
                      ∃ K' : PocketFaceSet D eps X'' (cuts.cut j.castSucc) (cuts.cut j.succ),
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X'' K'.source).length

/-- **Cases A and B.**  The proper face set producer from the residual Case C. -/
theorem properInput_of_fullSourceLake (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda)))
    (hlake : FullSourceLakeInput.{u, w, v} D lambda c eps W) :
    SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X', hE, hlabel, K, hK⟩ := sectionPocketFaceSetInput_of_keptCell.{u, w, v}
    sectionPocketKeptCell.{u, w, v} D lambda c eps W Delta cuts hlea S i j a ha b hb hne hja hjb
  rcases Nat.lt_or_eq_of_le K.sourceArc.length_le with hlt | hfull
  · exact ⟨X', hE, hlabel, K, hK, hlt⟩
  · by_cases hall : ∀ k : Fin X'.rCellCount,
        (cell X' k).face ∈ insert (cell X' K.source).face K.faces
    · exact hlake Delta cuts hlea S i j a ha b hb hne hja hjb X' hE hlabel K hK hfull hall
    · obtain ⟨k, hk⟩ := not_forall.mp hall
      exact ⟨X', hE, hlabel, absorbSource K hfull k hk, closedWalk_absorbSource K hK hfull k hk,
        absorbSource_sourceArc_lt K hfull k hk⟩

end Residual

/-- **Residual Case C, uniformly in the parameters**, with the quantifier prefix of the target. -/
def OsinFullSourceLakeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              FullSourceLakeInput.{u, w, v} D lambda c eps W

/-- **The target from the residual Case C.** -/
theorem proof_of_fullSourceLake (hlake : OsinFullSourceLakeStatement.{u, w, v}) :
    OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hl1 hl2 hc hm1 hm2
  obtain ⟨eps0, heps⟩ := hlake D hhyp lambda c mu hl1 hl2 hc hm1 hm2
  refine ⟨eps0, fun eps he => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps eps he
  exact ⟨rho0, hrho0, fun rho hr W hW =>
    properInput_of_fullSourceLake D lambda c eps W (hrho rho hr W hW)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.properInput_of_fullSourceLake
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.proof_of_fullSourceLake

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

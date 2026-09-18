import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.Cases
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 10: one step of the section pinch at an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`)
is the `hstep` residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

A case split on the rose configuration `P10ChordLift.AllNonFirstTurnsCrossed K`
(`GreendlingerLeaf/P10ChordLift/Predicate`), at the larger of the two thresholds for `ε` and for `ρ`.

* Some non-first turn is not crossed: the sub-leaf `P10ChordLift` splits the pocket at that turn.
* Every non-first turn is crossed: the rose case `P10ChordLift.RoseStepStatement`.

* `NonRoseStepStatement`: the step outside the rose configuration.

The case assembly is not declared here: this module imports the live case assembly
`GreendlingerLeaf/Piece10Live/Cases`, which provides `Piece10.proof_of_cases` (over
`P10ChordLift.NonRoseStepStatement`, definitionally equal to `NonRoseStepStatement` below) and
`Piece10.proof_of_rose` (non-rose case closed by `P10ChordLift.proof`).  The former duplicate
`proof_of_cases` of this module was removed (lane gl-imports-02).

## Status: no unconditional `Piece10.proof`

The former endpoint `Piece10.proof := proof_of_cases P10ChordLift.proof P10Rose.rose` cited
`P10Rose.rose`, declared nowhere on disk (its module `P10Rose/Proof` was the dead filter route and
has been deleted), so it was removed rather than restated.  The rose case is still open.  The live
conditional endpoints are

* `Piece10.proof_of_extremalJunction` (`P10RoseExtremalTrim/Reduction`), from
  `P10RoseExtremalTrim.RoseExtremalJunctionStatement`, used by `GreendlingerLeaf/AssemblyResidual`;
* `Piece10.proof_of_extremalCore` (`Piece10Live/RegionMoveCore`), from
  `P10RegionMove.RoseExtremalCoreStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

open Embedded Surgery.MapCollapse

/-- **The outer-pinch step outside the rose configuration.**  `PocketOuterPinchStepSectionStatement`
under the extra hypothesis that some non-first turn of the boundary cycle is crossed by no other
passage. -/
def NonRoseStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                  ¬Unpinched X.toCombMap K.faces →
                  ¬ P10ChordLift.AllNonFirstTurnsCrossed K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.NonRoseStepStatement

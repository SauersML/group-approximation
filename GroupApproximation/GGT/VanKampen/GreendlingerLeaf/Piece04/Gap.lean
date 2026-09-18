import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the remaining gap

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4, Cases 1 and 2 on class words.  The reduction
of `Piece04.Reduction` proves `OsinLemma94ClassCaseGapSpanStatement` from the one residual
`GapSpanResidualStatement` of this module, which is the conjunction of two open branches.

* `OsinLemma94ClassCaseOneRCellStatement` (module `OsinLemma94ClassSameCell`): the source and
  target classes are arcs `p`, `q` of one relator cell `Π`, the face walk reads `X T Y S`, and no
  rotation `q B p A` of `Π` has `X B = 1` or `Y A = 1`.  The argument of the side-level
  `osinLemma94CaseOneSameCell` encloses a subdiagram by the loop `X B` or `Y A` and contradicts least
  area or dart minimality.  On class words the windows `p`, `q` contain gap words, whose darts are not
  on the face walk, so that surgery does not transfer.
* `ClassFullWordDiffKindStatement` (below): the classes have different kinds, the target is not a
  cutting path, the pair is full-word (`a = 0`, `a' = |w_s|`, `b' = 0`, `b = |w_t|`), and both
  connectors have length exactly `ε - 1`.  Here the side-level short pair must take `[0, 1]` in the
  first side of the source class and `[|w_t| - 1, |w_t|]` in the last side of the target class (or
  symmetrically at the end pair).  One of its connectors is a connector of `C`, of length `ε - 1`.  The
  other is bounded only by `ε + 1` through the triangle inequality, while the region insertion
  (`RealizedSectionFamily.false_of_quadrilateral_face`) needs length at most `ε`.  All other
  different-kind pairs are refuted in `Piece04.DiffKind`.

* `ClassFullWordDiffKindStatement`: the full-word different-kind branch, with the quantifiers of
  `OsinLemma94ClassCaseGapSpanStatement`.
* `GapSpanResidualStatement`: the two branches together.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The full-word different-kind branch of GapSpan (residual).**  The quantifiers are those of
`OsinLemma94ClassCaseGapSpanStatement`: no backwards class-word pair with no endpoint inside a gap,
not single-side, with classes of different kinds and a non-cutting target, whose segments are the
whole class words and whose connectors both have length `ε - 1`. -/
def ClassFullWordDiffKindStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
                      (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k)
                        (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) eps),
                      C.b' < C.b → ¬ Q.GapEndpoint k C → ¬ Q.SingleSidePair k C →
                      Q.classKind k C.target ≠ .cutting →
                      Q.classKind k C.source ≠ Q.classKind k C.target →
                      C.a = 0 → C.a' = (Q.word k C.source).length → C.b' = 0 →
                      C.b = (Q.word k C.target).length → C.startConnector.length + 1 = eps →
                      C.endConnector.length + 1 = eps → False

/-- **The remaining gap of piece 04.**  The relator-cell branch and the full-word different-kind
branch of GapSpan. -/
def GapSpanResidualStatement : Prop :=
  OsinLemma94ClassCaseOneRCellStatement.{u, w, v} ∧ ClassFullWordDiffKindStatement.{u, w, v}

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

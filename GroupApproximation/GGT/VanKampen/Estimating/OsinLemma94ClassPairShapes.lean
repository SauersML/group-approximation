import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSection
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 on class words: the shapes of a connector pair

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2.  A class word of
`OsinLemma94ClassPolygons` is its side words with the gap words between them
(`OsinLemma94ClassPolygons.word_eq`), and a gap is a closed path of value one off the face walk of
the polygon.  A connector pair on the class words (`OsinLemma94ClassCasesInput`) falls into one of
three shapes:

* `SingleSidePair`: the source segment lies inside one side word of the source class and the
  target segment inside one side word of the target class.  These pairs transfer to side-level
  connector pairs (module `OsinLemma94ClassPairTransfer`), refuted by the side-level Case 1 and
  Case 2.
* `GapEndpoint`: some endpoint lies strictly inside a gap.  Its vertex is a vertex of the cell or
  of `∂Δ` inside a bubble, on no side.
* neither: the source or the target segment crosses a side boundary with no endpoint inside a
  gap, so it spans a gap, or it splits across sides (the split-target shape).

* `SideAt Q k i s off`: side `s` sits in class `i` after the prefix `L1` of its class sides, and
  `off` is the length of the class word before side `s`.
* `InGap Q k i x`: position `x` of class word `i` lies strictly inside the gap after some side.
* `GapEndpoint`, `SingleSidePair`: the shapes above.
* `OsinLemma94ClassCaseGapEndpointStatement` (residual): no backwards class-word pair has an
  endpoint inside a gap.
* `OsinLemma94ClassCaseGapSpanStatement` (residual): no backwards class-word pair is of the third
  shape, gap-spanning or split.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Side `s` sits in class `i` at offset `off`.**  The class sides read `L1 ++ s :: L2`, and
`off` is the length of the class word before side `s`: the side words of `L1` with their gaps. -/
def SideAt (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i s off : ℕ) : Prop :=
  ∃ L1 L2 : List ℕ, Q.classSides k i = L1 ++ s :: L2 ∧
    off = (L1.flatMap fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t)).length

/-- **Position `x` of class word `i` lies strictly inside a gap**: after the word of some side `s`
of the class and before the end of the gap after `s`. -/
def InGap (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i x : ℕ) : Prop :=
  ∃ s off, Q.SideAt k i s off ∧ off + (P.word k s).length < x ∧
    x < off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length

/-- **A class-word connector pair with an endpoint strictly inside a gap.** -/
def GapEndpoint (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) : Prop :=
  Q.InGap k C.source C.a ∨ Q.InGap k C.source C.a' ∨ Q.InGap k C.target C.b ∨
    Q.InGap k C.target C.b'

/-- **A single-side class-word connector pair**: the source segment `[a, a']` lies inside the word
of one side of the source class, and the target positions `b`, `b'` inside the word of one side of
the target class. -/
def SingleSidePair (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) : Prop :=
  (∃ s off, Q.SideAt k C.source s off ∧ off ≤ C.a ∧ C.a' ≤ off + (P.word k s).length) ∧
    ∃ t off, Q.SideAt k C.target t off ∧ off ≤ C.b ∧ off ≤ C.b' ∧
      C.b ≤ off + (P.word k t).length ∧ C.b' ≤ off + (P.word k t).length

end OsinLemma94ClassPolygons

/-- **Cases 1 and 2 of Lemma 9.4 on class words, at a gap endpoint (residual).**  At the parameters
of Lemma 9.4, for `ρ` large, with clause (b) of Lemma 9.7 below the number of relator cells in scope:
no backwards connector pair on the class words has an endpoint strictly inside a gap. -/
def OsinLemma94ClassCaseGapEndpointStatement : Prop :=
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
                      C.b' < C.b → Q.GapEndpoint k C → False

/-- **Cases 1 and 2 of Lemma 9.4 on class words, spanning or split (residual).**  The quantifiers
are those of `OsinLemma94ClassCaseGapEndpointStatement`: no backwards connector pair on the class
words that is not single-side and has no endpoint inside a gap. -/
def OsinLemma94ClassCaseGapSpanStatement : Prop :=
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
                      C.b' < C.b → ¬ Q.GapEndpoint k C → ¬ Q.SingleSidePair k C → False

end GroupApproximation.GGT.VanKampen

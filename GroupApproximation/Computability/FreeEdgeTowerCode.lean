import GroupApproximation.Computability.RawTransformPrimrec

/-!
# Finite codes for free-edge HNN towers

This file is the syntactic counterpart of
`Higman.InjectedCompilerTower`.  A finite list of pairs `(sourceWord,
targetWord)` determines one HNN-presentation layer: adjoin one stable generator
and, for each pair, append the relator

    t sourceWord t⁻¹ targetWord⁻¹.

Iterating that operation gives literal finite codes for the `tau`, `d`, and
`sigma` layers.  A fourth iteration with pairs `(w,w)` attaches a central HNN
detector last.  These definitions make no semantic injectivity claim; those
are precisely the explicit free-evaluation obligations isolated by
`ExplicitFreeEdge.Data`.
-/

namespace GroupApproximation
namespace FreeEdgeTowerCode

open PresentationCodes RawTransform
open RawTransformPrimrec

/-- A raw word in the concrete finite-presentation encoding. -/
abbrev RawWord : Type := List (ℕ × Bool)

/-- The new stable generator is placed immediately after the old alphabet. -/
def stableIndex (c : PresentationCode) : ℕ := genCount c

/-- A source/target pair contributes the HNN relator
`t source t⁻¹ target⁻¹`.  Old words are normalized before the alphabet is
enlarged, so the total modulo convention of `PresentationCode` does not change
their meaning. -/
def edgeRelator (c : PresentationCode) (p : RawWord × RawWord) : RawWord :=
  [(stableIndex c, true)] ++ normWord c p.1 ++
    [(stableIndex c, false)] ++ invWord (normWord c p.2)

/-- Adjoin one stable generator and finitely many HNN conjugation relators. -/
def edgeCode (c : PresentationCode) (edges : List (RawWord × RawWord)) :
    PresentationCode :=
  (c.1 + 1,
    c.2.map (normWord c) ++ edges.map (edgeRelator c))

@[simp] theorem edgeCode_genCount (c : PresentationCode)
    (edges : List (RawWord × RawWord)) :
    genCount (edgeCode c edges) = genCount c + 1 := by
  simp [edgeCode, genCount]

@[simp] theorem edgeCode_relators (c : PresentationCode)
    (edges : List (RawWord × RawWord)) :
    (edgeCode c edges).2 =
      c.2.map (normWord c) ++ edges.map (edgeRelator c) := rfl

/-- The three inner compiler layers in their intended order. -/
def threeStageCode (c : PresentationCode)
    (tauEdges dEdges sigmaEdges : List (RawWord × RawWord)) : PresentationCode :=
  edgeCode (edgeCode (edgeCode c tauEdges) dEdges) sigmaEdges

@[simp] theorem threeStageCode_genCount (c : PresentationCode)
    (tauEdges dEdges sigmaEdges : List (RawWord × RawWord)) :
    genCount (threeStageCode c tauEdges dEdges sigmaEdges) = genCount c + 3 := by
  simp [threeStageCode]

/-- Turn a finite word list into identity edge pairs, so the new stable letter
centralizes those words. -/
def centralEdges (words : List RawWord) : List (RawWord × RawWord) :=
  words.map fun w => (w, w)

/-- The corrected ordering at code level: build all three inner layers first,
then attach the central detector as the outermost HNN edge. -/
def detectorLastCode (c : PresentationCode)
    (tauEdges dEdges sigmaEdges : List (RawWord × RawWord))
    (detectorWords : List RawWord) : PresentationCode :=
  edgeCode (threeStageCode c tauEdges dEdges sigmaEdges)
    (centralEdges detectorWords)

@[simp] theorem detectorLastCode_genCount (c : PresentationCode)
    (tauEdges dEdges sigmaEdges : List (RawWord × RawWord))
    (detectorWords : List RawWord) :
    genCount (detectorLastCode c tauEdges dEdges sigmaEdges detectorWords) =
      genCount c + 4 := by
  simp [detectorLastCode]

/-! ## Computability of one edge -/

theorem primrec_stableIndex :
    Primrec (fun c : PresentationCode => stableIndex c) :=
  primrec_genCount

theorem primrec_edgeRelator :
    Primrec₂ (fun (c : PresentationCode) (p : RawWord × RawWord) =>
      edgeRelator c p) := by
  have hstablePos : Primrec (fun c : PresentationCode =>
      [(stableIndex c, true)]) :=
    Primrec₂.comp Primrec.list_cons
      (Primrec.pair primrec_stableIndex (Primrec.const true))
      (Primrec.const [])
  have hstableNeg : Primrec (fun c : PresentationCode =>
      [(stableIndex c, false)]) :=
    Primrec₂.comp Primrec.list_cons
      (Primrec.pair primrec_stableIndex (Primrec.const false))
      (Primrec.const [])
  have hsource : Primrec (fun a : PresentationCode × (RawWord × RawWord) =>
      normWord a.1 a.2.1) :=
    primrec_normWord.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have htarget : Primrec (fun a : PresentationCode × (RawWord × RawWord) =>
      normWord a.1 a.2.2) :=
    primrec_normWord.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.comp Primrec.list_append (hstablePos.comp Primrec.fst)
    (Primrec₂.comp Primrec.list_append hsource
      (Primrec₂.comp Primrec.list_append (hstableNeg.comp Primrec.fst)
        (primrec_invWord.comp htarget)))

/-- Computing one finite HNN presentation layer is primitive recursive. -/
theorem primrec_edgeCode :
    Primrec₂ (fun (c : PresentationCode) (edges : List (RawWord × RawWord)) =>
      edgeCode c edges) := by
  have hnormalized : Primrec (fun c : PresentationCode =>
      c.2.map (normWord c)) := primrec_leftWords
  have hedgeRelators : Primrec
      (fun a : PresentationCode × List (RawWord × RawWord) =>
        a.2.map (edgeRelator a.1)) :=
    Primrec.list_map Primrec.snd primrec_edgeRelator
  exact Primrec.pair
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (Primrec₂.comp Primrec.list_append (hnormalized.comp Primrec.fst)
      hedgeRelators)

/-- The code-level HNN constructor is computable. -/
theorem computable_edgeCode :
    Computable (fun a : PresentationCode × List (RawWord × RawWord) =>
      edgeCode a.1 a.2) :=
  primrec_edgeCode.to_comp

end FreeEdgeTowerCode
end GroupApproximation

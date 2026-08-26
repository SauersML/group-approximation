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

open PresentationCodes RawTransform CoprodCode
open GroupApproximation.RawWord
open RawTransformPrimrec

/-- A raw word in the concrete finite-presentation encoding. -/
abbrev Raw : Type := List (ℕ × Bool)

/-- The new stable generator is placed immediately after the old alphabet. -/
def stableIndex (c : PresentationCode) : ℕ := genCount c

/-- A source/target pair contributes the HNN relator
`t source t⁻¹ target⁻¹`.  Old words are normalized before the alphabet is
enlarged, so the total modulo convention of `PresentationCode` does not change
their meaning. -/
def edgeRelator (c : PresentationCode) (p : Raw × Raw) : Raw :=
  [(stableIndex c, true)] ++ normWord c p.1 ++
    [(stableIndex c, false)] ++ invWord (normWord c p.2)

/-- Adjoin one stable generator and finitely many HNN conjugation relators. -/
def edgeCode (c : PresentationCode) (edges : List (Raw × Raw)) :
    PresentationCode :=
  (c.1 + 1,
    c.2.map (normWord c) ++ edges.map (edgeRelator c))

@[simp] theorem edgeCode_genCount (c : PresentationCode)
    (edges : List (Raw × Raw)) :
    genCount (edgeCode c edges) = genCount c + 1 := by
  simp [edgeCode, genCount]

@[simp] theorem edgeCode_relators (c : PresentationCode)
    (edges : List (Raw × Raw)) :
    (edgeCode c edges).2 =
      c.2.map (normWord c) ++ edges.map (edgeRelator c) := rfl

/-- Adjoin one stable generator for every member of a finite edge family. -/
def multiEdgeCode (c : PresentationCode)
    (layers : List (List (Raw × Raw))) : PresentationCode :=
  layers.foldl edgeCode c

@[simp] theorem multiEdgeCode_nil (c : PresentationCode) :
    multiEdgeCode c [] = c := rfl

@[simp] theorem multiEdgeCode_cons (c : PresentationCode)
    (edges : List (Raw × Raw)) (layers : List (List (Raw × Raw))) :
    multiEdgeCode c (edges :: layers) =
      multiEdgeCode (edgeCode c edges) layers := rfl

/-- The inner compiler: the whole `tau_j` family, then `d`, then `sigma`. -/
def threeStageCode (c : PresentationCode)
    (tauLayers : List (List (Raw × Raw)))
    (dEdges sigmaEdges : List (Raw × Raw)) : PresentationCode :=
  edgeCode (edgeCode (multiEdgeCode c tauLayers) dEdges) sigmaEdges

@[simp] theorem multiEdgeCode_genCount (c : PresentationCode)
    (layers : List (List (Raw × Raw))) :
    genCount (multiEdgeCode c layers) = genCount c + layers.length := by
  induction layers generalizing c with
  | nil => simp
  | cons edges layers ih =>
      rw [multiEdgeCode_cons, ih, edgeCode_genCount]
      rw [List.length_cons]
      omega

@[simp] theorem threeStageCode_genCount (c : PresentationCode)
    (tauLayers : List (List (Raw × Raw)))
    (dEdges sigmaEdges : List (Raw × Raw)) :
    genCount (threeStageCode c tauLayers dEdges sigmaEdges) =
      genCount c + tauLayers.length + 2 := by
  simp [threeStageCode, Nat.add_assoc]

/-- Turn a finite word list into identity edge pairs, so the new stable letter
centralizes those words. -/
def centralEdges (words : List Raw) : List (Raw × Raw) :=
  words.map fun w => (w, w)

/-- The corrected ordering at code level: build all three inner layers first,
then attach the central detector as the outermost HNN edge. -/
def detectorLastCode (c : PresentationCode)
    (tauLayers : List (List (Raw × Raw))) (dEdges sigmaEdges : List (Raw × Raw))
    (detectorWords : List Raw) : PresentationCode :=
  edgeCode (threeStageCode c tauLayers dEdges sigmaEdges)
    (centralEdges detectorWords)

@[simp] theorem detectorLastCode_genCount (c : PresentationCode)
    (tauLayers : List (List (Raw × Raw))) (dEdges sigmaEdges : List (Raw × Raw))
    (detectorWords : List Raw) :
    genCount (detectorLastCode c tauLayers dEdges sigmaEdges detectorWords) =
      genCount c + tauLayers.length + 3 := by
  simp [detectorLastCode, Nat.add_assoc]

/-! ## Computability of one edge -/

theorem primrec_stableIndex :
    Primrec (fun c : PresentationCode => stableIndex c) :=
  primrec_genCount

theorem primrec_edgeRelator :
    Primrec₂ (fun (c : PresentationCode) (p : Raw × Raw) =>
      edgeRelator c p) := by
  change Primrec (fun a : PresentationCode × (Raw × Raw) =>
    edgeRelator a.1 a.2)
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
  have hnorm : Primrec (fun a : PresentationCode × Raw =>
      normWord a.1 a.2) := primrec_normWord
  have hsource : Primrec (fun a : PresentationCode × (Raw × Raw) =>
      normWord a.1 a.2.1) :=
    hnorm.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have htarget : Primrec (fun a : PresentationCode × (Raw × Raw) =>
      normWord a.1 a.2.2) :=
    hnorm.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  have happend : Primrec (fun a : Raw × Raw => a.1 ++ a.2) :=
    Primrec.list_append
  refine (happend.comp
    (Primrec.pair (hstablePos.comp Primrec.fst)
      (happend.comp
        (Primrec.pair hsource
          (happend.comp
            (Primrec.pair (hstableNeg.comp Primrec.fst)
              (primrec_invWord.comp htarget))))))).of_eq ?_
  intro a
  simp [edgeRelator, List.append_assoc]

/-- Computing one finite HNN presentation layer is primitive recursive. -/
theorem primrec_edgeCode :
    Primrec₂ (fun (c : PresentationCode) (edges : List (Raw × Raw)) =>
      edgeCode c edges) := by
  change Primrec (fun a : PresentationCode × List (Raw × Raw) =>
    edgeCode a.1 a.2)
  have hnormalized : Primrec (fun c : PresentationCode =>
      c.2.map (normWord c)) := primrec_leftWords
  have hedge : Primrec (fun a : PresentationCode × (Raw × Raw) =>
      edgeRelator a.1 a.2) := primrec_edgeRelator
  have hedgeRelator : Primrec
      (fun a : (PresentationCode × List (Raw × Raw)) × (Raw × Raw) =>
        edgeRelator a.1.1 a.2) :=
    hedge.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hedgeRelators : Primrec
      (fun a : PresentationCode × List (Raw × Raw) =>
        a.2.map (edgeRelator a.1)) :=
    Primrec.list_map Primrec.snd hedgeRelator
  have happend : Primrec (fun a : List Raw × List Raw => a.1 ++ a.2) :=
    Primrec.list_append
  exact Primrec.pair
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (happend.comp
      (Primrec.pair (hnormalized.comp Primrec.fst) hedgeRelators))

/-- The code-level HNN constructor is computable. -/
theorem computable_edgeCode :
    Computable (fun a : PresentationCode × List (Raw × Raw) =>
      edgeCode a.1 a.2) :=
  primrec_edgeCode.to_comp

/-! ## The complete primitive-recursive compiler -/

/-- The finite syntactic input for the four edges. -/
abbrev TowerInput : Type :=
  PresentationCode ×
    (List (List (Raw × Raw)) ×
      (List (Raw × Raw) ×
        (List (Raw × Raw) × List Raw)))

/-- Compile a packed input by the fixed `tau`, `d`, `sigma`, detector-last
sequence. -/
def compile (x : TowerInput) : PresentationCode :=
  detectorLastCode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem primrec_centralEdges :
    Primrec (fun words : List Raw => centralEdges words) :=
  Primrec.list_map Primrec.id (Primrec.pair Primrec.snd Primrec.snd)

set_option maxHeartbeats 800000 in
/-- Iterating the one-edge code constructor over a finite family is primitive
recursive. -/
theorem primrec_multiEdgeCode :
    Primrec₂ (fun (c : PresentationCode)
      (layers : List (List (Raw × Raw))) => multiEdgeCode c layers) := by
  change Primrec (fun a : PresentationCode × List (List (Raw × Raw)) =>
    multiEdgeCode a.1 a.2)
  have hedgeCode : Primrec
      (fun a : PresentationCode × List (Raw × Raw) => edgeCode a.1 a.2) :=
    primrec_edgeCode
  have hstep : Primrec₂
      (fun (z : (PresentationCode × List (List (Raw × Raw))) × PresentationCode)
        (edges : List (Raw × Raw)) => edgeCode z.2 edges) := by
    exact (hedgeCode.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  have hfold : Primrec
      (fun a : PresentationCode × List (List (Raw × Raw)) =>
        a.2.foldl edgeCode a.1) :=
    Primrec.list_foldl Primrec.snd Primrec.fst hstep
  exact hfold

/-- The full four-edge raw presentation compiler is primitive recursive. -/
theorem primrec_compile : Primrec compile := by
  have hedgeCode : Primrec
      (fun a : PresentationCode × List (Raw × Raw) => edgeCode a.1 a.2) :=
    primrec_edgeCode
  have hmultiEdgeCode : Primrec
      (fun a : PresentationCode × List (List (Raw × Raw)) =>
        multiEdgeCode a.1 a.2) := primrec_multiEdgeCode
  have hTau : Primrec (fun x : TowerInput => multiEdgeCode x.1 x.2.1) :=
    hmultiEdgeCode.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hD : Primrec (fun x : TowerInput =>
      edgeCode (multiEdgeCode x.1 x.2.1) x.2.2.1) :=
    hedgeCode.comp
      (Primrec.pair hTau
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hSigma : Primrec (fun x : TowerInput =>
      threeStageCode x.1 x.2.1 x.2.2.1 x.2.2.2.1) :=
    hedgeCode.comp
      (Primrec.pair hD
        (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hDetector : Primrec (fun x : TowerInput =>
      centralEdges x.2.2.2.2) :=
    primrec_centralEdges.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact hedgeCode.comp (Primrec.pair hSigma hDetector)

theorem computable_compile : Computable compile := primrec_compile.to_comp

/-! ## Deliberately separate semantic obligations -/

/-- The word-level obligation connecting the computed presentation to a
particular honest group-theoretic tower.  This is data to be proved from
`HNNPresentation.equivPres`; it is not built into the raw compiler. -/
def SemanticEquivalence (x : TowerInput) (HonestTower : Type)
    [Group HonestTower] : Prop :=
  Nonempty (Carrier (compile x) ≃* HonestTower)

/-- The code after the three inner edges, before the detector is attached. -/
def innerCode (x : TowerInput) : PresentationCode :=
  threeStageCode x.1 x.2.1 x.2.2.1 x.2.2.2.1

/-- A numbered generator in the compiled presentation. -/
def compiledGenerator (x : TowerInput) (i : ℕ) : Carrier (compile x) :=
  PresentedGroup.of (letterOf (compile x) i)

/-- A raw word evaluated in the compiled presentation. -/
def compiledWord (x : TowerInput) (w : Raw) : Carrier (compile x) :=
  PresentedGroup.mk _ (wordOf (compile x) w)

/-- The normalized detector payload actually inserted into the outer edge. -/
def detectorPayloadWord (x : TowerInput)
    (i : Fin x.2.2.2.2.length) : Raw :=
  normWord (innerCode x) (x.2.2.2.2.get i)

/-- Marked semantic data for the computed tower.  Besides a group
equivalence, it records the images of every original generator, the whole
`tau_j` stable-letter family, the `d`, `sigma`, and detector stable letters,
and every detector payload word.  These fields are the exact
compatibility needed to transport the outer detector theorem through the
finite presentation; a bare abstract equivalence would not suffice. -/
structure MarkedSemanticData (x : TowerInput) (HonestTower : Type)
    [Group HonestTower]
    (baseGenerator : Fin (genCount x.1) → HonestTower)
    (tauStable : Fin x.2.1.length → HonestTower)
    (dStable sigmaStable detectorStable : HonestTower)
    (detectorPayload : Fin x.2.2.2.2.length → HonestTower) where
  equiv : Carrier (compile x) ≃* HonestTower
  original_generator : ∀ i : Fin (genCount x.1),
    equiv (compiledGenerator x i) = baseGenerator i
  tau_stable : ∀ i : Fin x.2.1.length,
    equiv (compiledGenerator x (genCount x.1 + i)) = tauStable i
  d_stable :
    equiv (compiledGenerator x (genCount x.1 + x.2.1.length)) = dStable
  sigma_stable :
    equiv (compiledGenerator x (genCount x.1 + x.2.1.length + 1)) = sigmaStable
  detector_stable :
    equiv (compiledGenerator x (genCount x.1 + x.2.1.length + 2)) = detectorStable
  detector_payload : ∀ i : Fin x.2.2.2.2.length,
    equiv (compiledWord x (detectorPayloadWord x i)) = detectorPayload i

/-- The marked semantic-equivalence obligation. -/
def MarkedSemanticEquivalence (x : TowerInput) (HonestTower : Type)
    [Group HonestTower]
    (baseGenerator : Fin (genCount x.1) → HonestTower)
    (tauStable : Fin x.2.1.length → HonestTower)
    (dStable sigmaStable detectorStable : HonestTower)
    (detectorPayload : Fin x.2.2.2.2.length → HonestTower) : Prop :=
  Nonempty (MarkedSemanticData x HonestTower baseGenerator tauStable dStable
    sigmaStable detectorStable detectorPayload)

/-- Marked compatibility contains, in particular, the bare equivalence needed
for invariant transport. -/
theorem semanticEquivalence_of_marked (x : TowerInput) (HonestTower : Type)
    [Group HonestTower]
    (baseGenerator : Fin (genCount x.1) → HonestTower)
    (tauStable : Fin x.2.1.length → HonestTower)
    (dStable sigmaStable detectorStable : HonestTower)
    (detectorPayload : Fin x.2.2.2.2.length → HonestTower)
    (h : MarkedSemanticEquivalence x HonestTower baseGenerator tauStable dStable
      sigmaStable detectorStable detectorPayload) :
    SemanticEquivalence x HonestTower := by
  rcases h with ⟨h⟩
  exact ⟨h.equiv⟩

/-- The analytic obligation needed on the positive branch.  It is stated
separately so that no code-level computability theorem can silently assume an
MF permanence result for an asymmetric HNN edge. -/
def MFPermanence (x : TowerInput) : Prop :=
  IsOperatorMF (Carrier x.1) → IsOperatorMF (Carrier (compile x))

end FreeEdgeTowerCode
end GroupApproximation

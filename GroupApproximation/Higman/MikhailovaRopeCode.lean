import GroupApproximation.Higman.RopeTrick
import GroupApproximation.Computability.DirectProductCode

/-!
# Finite syntax for the Mikhailova rope compiler

`MikhailovaRopeCompiler` constructs an actual `FPOvergroup`, while
`RopeTrick` proves finite presentability through a manifest presentation with
the following three syntactic steps:

1. adjoin a stable letter centralizing finitely many cutting words;
2. take the direct product with the finitely presented source;
3. adjoin the outer rope letter with the two marked relation families.

The first and third steps are instances of `FreeEdgeTowerCode.edgeCode`; the
middle step is `DirectProductCode.productCode`.  This file composes those raw
constructors and proves the resulting transformation primitive recursive.

No claim is made here that arbitrary raw input describes the group-level
Mikhailova witness.  Establishing that marked semantic identification requires
the concrete word data supplied by a caller; it is not smuggled into the
computability theorem as a structure, hypothesis inhabitant, or literature
assumption.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRopeCode

open PresentationCodes
open FreeEdgeTowerCode DirectProductCode RawTransformPrimrec

/-- A raw word in the concrete finite-presentation encoding. -/
abbrev Raw : Type := List (ℕ × Bool)

/-- Finite raw input for the rope presentation:

* a code for the benign witness ambient;
* a code for the source group;
* finitely many words generating the cutting subgroup;
* marked pairs `(sourceWord, ambientLift)`.

The last list is intentionally explicit: the syntactic compiler neither
assumes nor manufactures a marked embedding. -/
abbrev Input : Type :=
  PresentationCode ×
    (PresentationCode × (List Raw × List (Raw × Raw)))

/-- The first HNN layer, centralizing the displayed cutting generators. -/
def firstStageCode (ambient : PresentationCode) (cuttingWords : List Raw) :
    PresentationCode :=
  edgeCode ambient (centralEdges cuttingWords)

/-- The direct-product base of the outer rope layer. -/
def outerBaseCode (ambient source : PresentationCode)
    (cuttingWords : List Raw) : PresentationCode :=
  productCode (firstStageCode ambient cuttingWords) source

/-- Conjugate an ambient word by the inverse of the first stable letter, in
the convention `t⁻¹ w t` used by `Rope.gammaConj`. -/
def firstStableConjugate (ambient : PresentationCode) (w : Raw) : Raw :=
  (stableIndex ambient, false) ::
    (leftWord ambient w ++ [(stableIndex ambient, true)])

/-- The `A` edge contributed by one marked source/ambient pair.  It spells
`e g e⁻¹ = g x`. -/
def ropeAEdge (ambient gamma source : PresentationCode)
    (marked : Raw × Raw) : Raw × Raw :=
  (leftWord gamma (leftWord ambient marked.2),
    leftWord gamma (leftWord ambient marked.2) ++
      rightWord gamma source marked.1)

/-- The `B` edge contributed by one marked source/ambient pair.  It spells
`e (t⁻¹ g t) e⁻¹ = t⁻¹ g t`. -/
def ropeBEdge (ambient gamma : PresentationCode)
    (marked : Raw × Raw) : Raw × Raw :=
  (leftWord gamma (firstStableConjugate ambient marked.2),
    leftWord gamma (firstStableConjugate ambient marked.2))

/-- The finite edge family for the outer rope letter. -/
def ropeEdges (ambient gamma source : PresentationCode)
    (marked : List (Raw × Raw)) : List (Raw × Raw) :=
  marked.map (ropeAEdge ambient gamma source) ++
    marked.map (ropeBEdge ambient gamma)

/-- **The raw finite-presentation compiler matching the rope construction's
three syntactic steps.** -/
def compile (x : Input) : PresentationCode :=
  let ambient := x.1
  let source := x.2.1
  let cuttingWords := x.2.2.1
  let marked := x.2.2.2
  let gamma := firstStageCode ambient cuttingWords
  edgeCode (productCode gamma source)
    (ropeEdges ambient gamma source marked)

@[simp] theorem firstStageCode_genCount (ambient : PresentationCode)
    (cuttingWords : List Raw) :
    genCount (firstStageCode ambient cuttingWords) = genCount ambient + 1 := by
  simp [firstStageCode]

@[simp] theorem outerBaseCode_genCount (ambient source : PresentationCode)
    (cuttingWords : List Raw) :
    genCount (outerBaseCode ambient source cuttingWords) =
      genCount ambient + 1 + genCount source := by
  simp [outerBaseCode, Nat.add_assoc]

@[simp] theorem compile_genCount (x : Input) :
    genCount (compile x) = genCount x.1 + 1 + genCount x.2.1 + 1 := by
  simp [compile, firstStageCode, Nat.add_assoc]

/-! ## Primitive recursiveness -/

theorem primrec_firstStageCode :
    Primrec (fun a : PresentationCode × List Raw =>
      firstStageCode a.1 a.2) := by
  have hedge : Primrec (fun a : PresentationCode × List (Raw × Raw) =>
      edgeCode a.1 a.2) := primrec_edgeCode
  exact hedge.comp
    (Primrec.pair Primrec.fst (primrec_centralEdges.comp Primrec.snd))

theorem primrec_firstStableConjugate :
    Primrec (fun a : PresentationCode × Raw =>
      firstStableConjugate a.1 a.2) := by
  have hstableNeg : Primrec (fun a : PresentationCode × Raw =>
      (stableIndex a.1, false)) :=
    Primrec.pair (primrec_stableIndex.comp Primrec.fst) (Primrec.const false)
  have hstablePos : Primrec (fun a : PresentationCode × Raw =>
      [(stableIndex a.1, true)]) :=
    Primrec₂.comp Primrec.list_cons
      (Primrec.pair (primrec_stableIndex.comp Primrec.fst) (Primrec.const true))
      (Primrec.const [])
  have hnormalized : Primrec (fun a : PresentationCode × Raw =>
      leftWord a.1 a.2) :=
    primrec_leftWord
  have htail : Primrec (fun a : PresentationCode × Raw =>
      leftWord a.1 a.2 ++ [(stableIndex a.1, true)]) :=
    Primrec₂.comp Primrec.list_append hnormalized hstablePos
  have hall : Primrec (fun a : PresentationCode × Raw =>
      (stableIndex a.1, false) ::
        (leftWord a.1 a.2 ++ [(stableIndex a.1, true)])) :=
    Primrec₂.comp Primrec.list_cons hstableNeg htail
  exact hall.of_eq fun _ => rfl

/-! The parameter pack used by one outer rope edge.  Naming these packs keeps
the primitive-recursive composition proofs below small enough for Lean to
elaborate each one independently. -/
abbrev RopeParameters : Type :=
  (PresentationCode × PresentationCode) × PresentationCode

abbrev RopeEdgeInput : Type := RopeParameters × (Raw × Raw)

abbrev RopeEdgesInput : Type := RopeParameters × List (Raw × Raw)

/-! Mapping over parameters containing three full presentation codes makes the
generic `Primrec.list_map` proof normalize the encodings of three nested
relator lists.  An outer rope edge only reads the first natural-number field
of each code.  We therefore perform the map over this exact finite index pack
and compose with the primitive-recursive projection from full codes. -/
abbrev RopeIndexParameters : Type := (ℕ × ℕ) × ℕ

abbrev RopeIndexEdgeInput : Type := RopeIndexParameters × (Raw × Raw)

abbrev RopeIndexEdgesInput : Type :=
  RopeIndexParameters × List (Raw × Raw)

def presentationSkeleton (n : ℕ) : PresentationCode := (n, [])

/-! ## The literal rank-three input shell

The semantic bridge always uses the free group on three generators as its
source.  Consequently a caller does not need to manufacture a source
presentation or an arbitrary marked list: it only supplies the three ambient
words spelling the images of those generators.  This shell is the concrete
finite datum that the effective Higman/Mikhailova lane must produce. -/

/-- Ambient representatives of the three marked source generators. -/
abbrev RankThreeWords : Type := Raw × (Raw × Raw)

/-- The remaining effective data for the rank-three rope code: an ambient
finite presentation, its finite cutting list, and three ambient marked words. -/
abbrev RankThreeInputData : Type :=
  PresentationCode × (List Raw × RankThreeWords)

/-- The positive one-letter raw word naming generator `i`. -/
def rankThreeGeneratorWord (i : ℕ) : Raw := [(i, true)]

/-- Pair the three free source generators with their supplied ambient words. -/
def rankThreeMarked (words : RankThreeWords) : List (Raw × Raw) :=
  [(rankThreeGeneratorWord 0, words.1),
    (rankThreeGeneratorWord 1, words.2.1),
    (rankThreeGeneratorWord 2, words.2.2)]

/-- Assemble the exact raw input consumed by `compile`, with the relator-free
rank-three source presentation filled in canonically. -/
def rankThreeInput (d : RankThreeInputData) : Input :=
  (d.1, (presentationSkeleton 3, (d.2.1, rankThreeMarked d.2.2)))

/-- The rank-three finite-presentation compiler after canonical input
assembly. -/
def compileRankThree (d : RankThreeInputData) : PresentationCode :=
  compile (rankThreeInput d)

def ropeIndexParameters (p : RopeParameters) : RopeIndexParameters :=
  ((p.1.1.1, p.1.2.1), p.2.1)

def indexedRopeParameters (p : RopeIndexParameters) : RopeParameters :=
  ((presentationSkeleton p.1.1, presentationSkeleton p.1.2),
    presentationSkeleton p.2)

def ropeAEdgeIndexed (p : RopeIndexParameters) (marked : Raw × Raw) :
    Raw × Raw :=
  ropeAEdge (presentationSkeleton p.1.1) (presentationSkeleton p.1.2)
    (presentationSkeleton p.2) marked

def ropeBEdgeIndexed (p : RopeIndexParameters) (marked : Raw × Raw) :
    Raw × Raw :=
  ropeBEdge (presentationSkeleton p.1.1) (presentationSkeleton p.1.2) marked

def ropeAEdgesIndexed (p : RopeIndexParameters)
    (marked : List (Raw × Raw)) : List (Raw × Raw) :=
  marked.map (ropeAEdgeIndexed p)

def ropeBEdgesIndexed (p : RopeIndexParameters)
    (marked : List (Raw × Raw)) : List (Raw × Raw) :=
  marked.map (ropeBEdgeIndexed p)

theorem primrec_presentationSkeleton : Primrec presentationSkeleton :=
  Primrec.pair Primrec.id (Primrec.const [])

theorem primrec_rankThreeGeneratorWord : Primrec rankThreeGeneratorWord :=
  Primrec.list_cons.comp
    (Primrec.pair Primrec.id (Primrec.const true)) (Primrec.const [])

theorem primrec_rankThreeMarked : Primrec rankThreeMarked := by
  have hzero : Primrec (fun words : RankThreeWords =>
      (rankThreeGeneratorWord 0, words.1)) :=
    Primrec.pair (Primrec.const (rankThreeGeneratorWord 0)) Primrec.fst
  have hone : Primrec (fun words : RankThreeWords =>
      (rankThreeGeneratorWord 1, words.2.1)) :=
    Primrec.pair (Primrec.const (rankThreeGeneratorWord 1))
      (Primrec.fst.comp Primrec.snd)
  have htwo : Primrec (fun words : RankThreeWords =>
      (rankThreeGeneratorWord 2, words.2.2)) :=
    Primrec.pair (Primrec.const (rankThreeGeneratorWord 2))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.comp Primrec.list_cons hzero
    (Primrec₂.comp Primrec.list_cons hone
      (Primrec₂.comp Primrec.list_cons htwo (Primrec.const [])))

theorem primrec_rankThreeInput : Primrec rankThreeInput := by
  have hambient : Primrec (fun d : RankThreeInputData => d.1) := Primrec.fst
  have hcutting : Primrec (fun d : RankThreeInputData => d.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hwords : Primrec (fun d : RankThreeInputData => d.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.pair hambient
    (Primrec.pair (Primrec.const (presentationSkeleton 3))
      (Primrec.pair hcutting (primrec_rankThreeMarked.comp hwords)))

theorem primrec_ropeIndexParameters : Primrec ropeIndexParameters :=
  Primrec.pair
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.fst.comp Primrec.snd)

theorem primrec_indexedRopeParameters : Primrec indexedRopeParameters := by
  have hambient : Primrec (fun p : RopeIndexParameters =>
      presentationSkeleton p.1.1) :=
    primrec_presentationSkeleton.comp (Primrec.fst.comp Primrec.fst)
  have hgamma : Primrec (fun p : RopeIndexParameters =>
      presentationSkeleton p.1.2) :=
    primrec_presentationSkeleton.comp (Primrec.snd.comp Primrec.fst)
  have hsource : Primrec (fun p : RopeIndexParameters =>
      presentationSkeleton p.2) :=
    primrec_presentationSkeleton.comp Primrec.snd
  exact Primrec.pair (Primrec.pair hambient hgamma) hsource

theorem primrec_leftWord_packed :
    Primrec (fun a : PresentationCode × Raw => leftWord a.1 a.2) :=
  primrec_leftWord

theorem primrec_ropeAAmbientWord :
    Primrec (fun a : RopeEdgeInput => leftWord a.1.1.1 a.2.2) :=
  primrec_leftWord_packed.comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_ropeAWord :
    Primrec (fun a : RopeEdgeInput =>
      leftWord a.1.1.2 (leftWord a.1.1.1 a.2.2)) :=
  primrec_leftWord_packed.comp
    (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      primrec_ropeAAmbientWord)

theorem primrec_ropeASourceWord :
    Primrec (fun a : RopeEdgeInput =>
      rightWord a.1.1.2 a.1.2 a.2.1) :=
  primrec_rightWord.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))

theorem primrec_ropeAProductWord :
    Primrec (fun a : RopeEdgeInput =>
      leftWord a.1.1.2 (leftWord a.1.1.1 a.2.2) ++
        rightWord a.1.1.2 a.1.2 a.2.1) :=
  Primrec₂.comp Primrec.list_append primrec_ropeAWord primrec_ropeASourceWord

theorem primrec_ropeAEdge :
    Primrec (fun a : RopeEdgeInput =>
      ropeAEdge a.1.1.1 a.1.1.2 a.1.2 a.2) :=
  Primrec.pair primrec_ropeAWord primrec_ropeAProductWord

theorem primrec_ropeBConjugate :
    Primrec (fun a : RopeEdgeInput =>
      firstStableConjugate a.1.1.1 a.2.2) :=
  primrec_firstStableConjugate.comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_ropeBWord :
    Primrec (fun a : RopeEdgeInput =>
      leftWord a.1.1.2 (firstStableConjugate a.1.1.1 a.2.2)) :=
  primrec_leftWord_packed.comp
    (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      primrec_ropeBConjugate)

theorem primrec_ropeBEdge :
    Primrec (fun a : RopeEdgeInput =>
      ropeBEdge a.1.1.1 a.1.1.2 a.2) :=
  Primrec.pair primrec_ropeBWord primrec_ropeBWord

theorem primrec_ropeAEdgeIndexed :
    Primrec (fun a : RopeIndexEdgeInput =>
      ropeAEdgeIndexed a.1 a.2) :=
  primrec_ropeAEdge.comp
    (Primrec.pair
      (primrec_indexedRopeParameters.comp Primrec.fst)
      Primrec.snd)

theorem primrec_ropeBEdgeIndexed :
    Primrec (fun a : RopeIndexEdgeInput =>
      ropeBEdgeIndexed a.1 a.2) :=
  primrec_ropeBEdge.comp
    (Primrec.pair
      (primrec_indexedRopeParameters.comp Primrec.fst)
      Primrec.snd)

theorem primrec_ropeAEdgeIndexedForList :
    Primrec₂ (fun (a : RopeIndexEdgesInput) (marked : Raw × Raw) =>
      ropeAEdgeIndexed a.1 marked) :=
  primrec_ropeAEdgeIndexed.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      Primrec.snd)

theorem primrec_ropeBEdgeIndexedForList :
    Primrec₂ (fun (a : RopeIndexEdgesInput) (marked : Raw × Raw) =>
      ropeBEdgeIndexed a.1 marked) :=
  primrec_ropeBEdgeIndexed.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      Primrec.snd)

theorem primrec_ropeAEdgesIndexed :
    Primrec (fun a : RopeIndexEdgesInput =>
      ropeAEdgesIndexed a.1 a.2) :=
  Primrec.list_map Primrec.snd primrec_ropeAEdgeIndexedForList

theorem primrec_ropeBEdgesIndexed :
    Primrec (fun a : RopeIndexEdgesInput =>
      ropeBEdgesIndexed a.1 a.2) :=
  Primrec.list_map Primrec.snd primrec_ropeBEdgeIndexedForList

theorem primrec_ropeAEdges :
    Primrec (fun a : RopeEdgesInput =>
      a.2.map (ropeAEdge a.1.1.1 a.1.1.2 a.1.2)) := by
  have hindexed : Primrec (fun a : RopeEdgesInput =>
      ropeAEdgesIndexed (ropeIndexParameters a.1) a.2) :=
    primrec_ropeAEdgesIndexed.comp
      (Primrec.pair
        (primrec_ropeIndexParameters.comp Primrec.fst)
        Primrec.snd)
  exact hindexed.of_eq fun _ => rfl

theorem primrec_ropeBEdges :
    Primrec (fun a : RopeEdgesInput =>
      a.2.map (ropeBEdge a.1.1.1 a.1.1.2)) := by
  have hindexed : Primrec (fun a : RopeEdgesInput =>
      ropeBEdgesIndexed (ropeIndexParameters a.1) a.2) :=
    primrec_ropeBEdgesIndexed.comp
      (Primrec.pair
        (primrec_ropeIndexParameters.comp Primrec.fst)
        Primrec.snd)
  exact hindexed.of_eq fun _ => rfl

theorem primrec_ropeEdges :
    Primrec (fun a : RopeEdgesInput =>
      ropeEdges a.1.1.1 a.1.1.2 a.1.2 a.2) := by
  exact Primrec₂.comp Primrec.list_append primrec_ropeAEdges primrec_ropeBEdges

/-- The complete raw Mikhailova-rope syntax transformation is primitive
recursive. -/
theorem primrec_compile : Primrec compile := by
  have hambient : Primrec (fun x : Input => x.1) := Primrec.fst
  have hsource : Primrec (fun x : Input => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcutting : Primrec (fun x : Input => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hmarked : Primrec (fun x : Input => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hgamma : Primrec (fun x : Input =>
      firstStageCode x.1 x.2.2.1) :=
    primrec_firstStageCode.comp (Primrec.pair hambient hcutting)
  have hbase : Primrec (fun x : Input =>
      productCode (firstStageCode x.1 x.2.2.1) x.2.1) :=
    primrec_productCode.comp (Primrec.pair hgamma hsource)
  have hedges : Primrec (fun x : Input =>
      ropeEdges x.1 (firstStageCode x.1 x.2.2.1) x.2.1 x.2.2.2) :=
    primrec_ropeEdges.comp
      (Primrec.pair
        (Primrec.pair (Primrec.pair hambient hgamma) hsource)
        hmarked)
  have hedgeCode : Primrec (fun a : PresentationCode × List (Raw × Raw) =>
      edgeCode a.1 a.2) := primrec_edgeCode
  exact hedgeCode.comp (Primrec.pair hbase hedges)

/-- **Computable finite output suitable for the code field of a future
`MFCompiler`.**  Its semantic truth table remains a separate theorem. -/
theorem computable_compile : Computable compile :=
  primrec_compile.to_comp

/-- Canonical rank-three input assembly followed by the rope compiler is
primitive recursive. -/
theorem primrec_compileRankThree : Primrec compileRankThree :=
  primrec_compile.comp primrec_rankThreeInput

theorem computable_rankThreeInput : Computable rankThreeInput :=
  primrec_rankThreeInput.to_comp

theorem computable_compileRankThree : Computable compileRankThree :=
  primrec_compileRankThree.to_comp

end MikhailovaRopeCode

namespace MikhailovaRopeCompiler

/-- The concrete finite syntax consumed by the code-level companion to the
group-level Mikhailova rope construction. -/
abbrev FiniteSyntaxInput := MikhailovaRopeCode.Input

/-- The finite-presentation transformation attached to the actual compiler
namespace.  This is an abbreviation of the assumption-free raw compiler. -/
abbrev finiteSyntax : FiniteSyntaxInput → PresentationCodes.PresentationCode :=
  MikhailovaRopeCode.compile

theorem computable_finiteSyntax : Computable finiteSyntax :=
  MikhailovaRopeCode.computable_compile

/-- The reduced effective input still owed by the upstream marked-embedding
construction. -/
abbrev RankThreeFiniteSyntaxInput := MikhailovaRopeCode.RankThreeInputData

/-- Canonical assembly of the source code and its three marked generators. -/
abbrev rankThreeFiniteSyntaxInput :
    RankThreeFiniteSyntaxInput → FiniteSyntaxInput :=
  MikhailovaRopeCode.rankThreeInput

/-- The actual finite code emitted from reduced rank-three input data. -/
abbrev rankThreeFiniteSyntax :
    RankThreeFiniteSyntaxInput → PresentationCodes.PresentationCode :=
  MikhailovaRopeCode.compileRankThree

theorem computable_rankThreeFiniteSyntaxInput :
    Computable rankThreeFiniteSyntaxInput :=
  MikhailovaRopeCode.computable_rankThreeInput

theorem computable_rankThreeFiniteSyntax :
    Computable rankThreeFiniteSyntax :=
  MikhailovaRopeCode.computable_compileRankThree

end MikhailovaRopeCompiler
end Higman
end GroupApproximation

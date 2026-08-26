import GroupApproximation.Computability.FreeEdgeTowerSemantics

/-!
# Iterating the raw free-edge semantics

`FreeEdgeTowerSemantics.edgeCodeEquiv` identifies one computed edge with an
honest HNN extension over the group presented at the preceding stage.  To
iterate that result, the preceding presentation equivalence has to be carried
through the next pair of associated free subgroups.  This file supplies that
transport without adding any algebraic assumption.

The only inputs retained at each stage are the two injectivity proofs for the
displayed source and target evaluations.  In particular, no MF permanence or
compiler-correctness hypothesis is hidden in the iteration layer.
-/

namespace GroupApproximation
namespace FreeEdgeTowerIteration

open HNNExtension
open Higman ExplicitFreeEdge
open HNNCongr
open PresentationCodes FreeEdgeTowerCode
open FreeEdgeTowerSemantics

variable {X G H : Type} [Group G] [Group H]

/-- Transport explicitly embedded free edge groups across an equivalence of
bases. -/
def transportData (e : G ≃* H) (E : Data X G) : Data X H where
  source := e.toMonoidHom.comp E.source
  target := e.toMonoidHom.comp E.target
  source_injective := e.injective.comp E.source_injective
  target_injective := e.injective.comp E.target_injective

@[simp] theorem transportData_source (e : G ≃* H) (E : Data X G) :
    (transportData e E).source = e.toMonoidHom.comp E.source := rfl

@[simp] theorem transportData_target (e : G ≃* H) (E : Data X G) :
    (transportData e E).target = e.toMonoidHom.comp E.target := rfl

/-- An equivalence of bases carries the explicit source subgroup onto the
transported source subgroup. -/
theorem mem_sourceSubgroup_transportData_iff (e : G ≃* H) (E : Data X G)
    (g : G) :
    g ∈ sourceSubgroup E ↔ e g ∈ sourceSubgroup (transportData e E) := by
  simp only [sourceSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨w, Subgroup.mem_top w, rfl⟩
  · rintro ⟨w, -, hw⟩
    refine ⟨w, Subgroup.mem_top w, ?_⟩
    apply e.injective
    simpa [transportData] using hw

/-- Transporting the edge data preserves the canonical word-by-word edge
identification. -/
theorem transportData_intertwines (e : G ≃* H) (E : Data X G) :
    Intertwines (edgeEquiv E) (edgeEquiv (transportData e E)) e
      (mem_sourceSubgroup_transportData_iff e E) := by
  intro g hg
  let a : sourceSubgroup E := ⟨g, hg⟩
  let w : FreeGroup X := (sourceEquiv E).symm a
  have hsource : E.source w = g := by
    rw [← coe_sourceEquiv]
  have horiginal :
      (⟨g, hg⟩ : sourceSubgroup E) = sourceElement E w := by
    apply Subtype.ext
    change g = E.source w
    exact hsource.symm
  have htransported :
      (⟨e g, (mem_sourceSubgroup_transportData_iff e E g).1 hg⟩ :
          sourceSubgroup (transportData e E)) =
        sourceElement (transportData e E) w := by
    apply Subtype.ext
    change e g = (transportData e E).source w
    simpa [transportData] using congrArg e hsource.symm
  rw [htransported, horiginal]
  rw [coe_edgeEquiv_sourceElement, coe_edgeEquiv_sourceElement]
  rfl

/-- HNN extension commutes with transport of an explicitly embedded free
edge across an equivalence of bases. -/
noncomputable def transportExtensionEquiv (e : G ≃* H) (E : Data X G) :
    Extension E ≃* Extension (transportData e E) :=
  HNNCongr.congrEquiv (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E)

@[simp] theorem transportExtensionEquiv_of (e : G ≃* H) (E : Data X G)
    (g : G) :
    transportExtensionEquiv e E (of g) = of (e g) := by
  exact HNNCongr.congrHom_of (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E) g

@[simp] theorem transportExtensionEquiv_t (e : G ≃* H) (E : Data X G) :
    transportExtensionEquiv e E (t : Extension E) =
      (t : Extension (transportData e E)) := by
  exact HNNCongr.congrHom_t (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E)

/-! ## A dependent chain of computed edges -/

/-- The exact two freeness obligations for one raw edge layer. -/
structure EdgeFreeness (c : PresentationCode)
    (edges : List (Raw × Raw)) : Prop where
  source : Function.Injective (sourceEval c edges)
  target : Function.Injective (targetEval c edges)

/-- Freeness obligations for a whole raw edge program.  The tail is indexed by
the code produced by the preceding edge, so it is impossible to state a later
edge in the wrong base group. -/
inductive ChainFreeness : (c : PresentationCode) →
    List (List (Raw × Raw)) → Prop
  | nil (c) : ChainFreeness c []
  | cons {c edges layers} : EdgeFreeness c edges →
      ChainFreeness (edgeCode c edges) layers →
      ChainFreeness c (edges :: layers)

/-- A computed presentation together with an honest, iterated free-edge HNN
tower presenting it. -/
structure SemanticStage (c : PresentationCode) where
  Honest : Type
  group : Group Honest
  equiv : Carrier c ≃* Honest

attribute [instance] SemanticStage.group

/-- Before any edge, the presented base is its own honest realization. -/
def SemanticStage.base (c : PresentationCode) : SemanticStage c where
  Honest := Carrier c
  group := inferInstance
  equiv := MulEquiv.refl _

/-- Add one raw edge to an already honest tower.  The one-edge equivalence is
followed by transport of that HNN extension across the preceding stage
equivalence. -/
noncomputable def SemanticStage.addEdge {c : PresentationCode}
    (S : SemanticStage c) (edges : List (Raw × Raw))
    (h : EdgeFreeness c edges) : SemanticStage (edgeCode c edges) where
  Honest := Extension (transportData S.equiv
    (edgeData c edges h.source h.target))
  group := inferInstance
  equiv := (edgeCodeEquiv c edges h.source h.target).trans
    (transportExtensionEquiv S.equiv
      (edgeData c edges h.source h.target))

/-- Iterate honest edge semantics from an arbitrary already-realized stage. -/
noncomputable def buildFrom {c : PresentationCode} (S : SemanticStage c) :
    (layers : List (List (Raw × Raw))) → ChainFreeness c layers →
      SemanticStage (multiEdgeCode c layers)
  | [], .nil _ => S
  | edges :: layers, .cons h hs =>
      buildFrom (S.addEdge edges h) layers hs

/-- The honest iterated HNN tower attached to a raw finite edge program. -/
noncomputable def build (c : PresentationCode)
    (layers : List (List (Raw × Raw)))
    (h : ChainFreeness c layers) : SemanticStage (multiEdgeCode c layers) :=
  buildFrom (SemanticStage.base c) layers h

/-! ## The literal tau/d/sigma/detector program -/

/-- All compiler edges in their actual order: every `tau_j`, then `d`, then
`sigma`, and finally the central detector. -/
def compilerLayers (x : TowerInput) : List (List (Raw × Raw)) :=
  x.2.1 ++ [x.2.2.1, x.2.2.2.1, centralEdges x.2.2.2.2]

theorem multiEdgeCode_append (c : PresentationCode)
    (xs ys : List (List (Raw × Raw))) :
    multiEdgeCode c (xs ++ ys) = multiEdgeCode (multiEdgeCode c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons edges xs ih =>
      exact ih (edgeCode c edges)

/-- Folding the literal four-part edge program is definitionally the packed
compiler after only the standard fold-append reassociation. -/
theorem multiEdgeCode_compilerLayers (x : TowerInput) :
    multiEdgeCode x.1 (compilerLayers x) = compile x := by
  rw [compilerLayers, multiEdgeCode_append]
  rfl

/-- An honest HNN realization of the complete computed compiler output. -/
noncomputable def compilerStage (x : TowerInput)
    (h : ChainFreeness x.1 (compilerLayers x)) : SemanticStage (compile x) := by
  rw [← multiEdgeCode_compilerLayers x]
  exact build x.1 (compilerLayers x) h

/-- The complete honest tower type produced from the stage-by-stage freeness
proofs. -/
abbrev HonestCompilerTower (x : TowerInput)
    (h : ChainFreeness x.1 (compilerLayers x)) : Type :=
  (compilerStage x h).Honest

/-- **Full marked semantics for the finite compiler.**

The honest carrier is the iterated HNN tower built above.  Every marked value
is the image of the literal raw generator or detector word under the resulting
equivalence; consequently this theorem records the whole `tau_j` family and
the `d`, `sigma`, and outer detector letters without a numbering convention
left implicit. -/
noncomputable def compilerMarkedData (x : TowerInput)
    (h : ChainFreeness x.1 (compilerLayers x)) :
    MarkedSemanticData x (HonestCompilerTower x h)
      (fun i => (compilerStage x h).equiv (compiledGenerator x i))
      (fun i => (compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + i)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length + 1)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length + 2)))
      (fun i => (compilerStage x h).equiv
        (compiledWord x (detectorPayloadWord x i))) where
  equiv := (compilerStage x h).equiv
  original_generator _ := rfl
  tau_stable _ := rfl
  d_stable := rfl
  sigma_stable := rfl
  detector_stable := rfl
  detector_payload _ := rfl

/-- The packed marked-equivalence proposition is discharged solely by the
stage-indexed freeness proofs. -/
theorem markedSemanticEquivalence_of_chainFreeness (x : TowerInput)
    (h : ChainFreeness x.1 (compilerLayers x)) :
    MarkedSemanticEquivalence x (HonestCompilerTower x h)
      (fun i => (compilerStage x h).equiv (compiledGenerator x i))
      (fun i => (compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + i)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length + 1)))
      ((compilerStage x h).equiv
        (compiledGenerator x (genCount x.1 + x.2.1.length + 2)))
      (fun i => (compilerStage x h).equiv
        (compiledWord x (detectorPayloadWord x i))) :=
  ⟨compilerMarkedData x h⟩

end FreeEdgeTowerIteration
end GroupApproximation

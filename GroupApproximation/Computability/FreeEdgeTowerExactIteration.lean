import GroupApproximation.Computability.FreeEdgeTowerExactIterationCore
import GroupApproximation.Computability.FreeEdgeTowerIteration

/-!
# Iterating exact subgroup-equivalence edges

`FreeEdgeTowerIteration.ChainFreeness` is the convenient specialization in
which every displayed edge family is a free basis on both sides.  It is too
strong for the detector-last compiler: the final stable letter centralizes an
arbitrary finitely generated subgroup, and the displayed generators of that
subgroup need not be free.

`FreeEdgeTowerExactIterationCore` iterates the exact one-edge semantics.  This
file proves that a central edge has exact semantics with no freeness hypothesis
and applies that fact to the final detector layer.
-/

namespace GroupApproximation
namespace FreeEdgeTowerExactIteration

open HNNExtension
open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics
open FreeEdgeTowerIteration

noncomputable section

/-! ## The free-tuple specialization -/

/-- The older freeness datum induces the exact subgroup equivalence used by
the HNN presentation. -/
noncomputable def edgeEquivalenceOfFreeness (c : PresentationCode)
    (edges : List (Raw × Raw)) (h : EdgeFreeness c edges) :
    EdgeEquivalence c edges where
  equiv := presentedEdgeEquiv c edges h.source h.target
  generator := presentedEdgeEquiv_gen c edges h.source h.target

/-- Every free-tuple chain has an exact edge chain.  The result is stated in
`Nonempty`, so induction on the proposition-valued freeness certificate never
attempts to eliminate proof data into `Type`. -/
theorem ExactChain.nonempty_ofChainFreeness : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → ChainFreeness c layers →
      Nonempty (ExactChain c layers)
  | _, [], .nil _ => ⟨.nil _⟩
  | _, _ :: _, .cons h rest => by
      obtain ⟨tail⟩ := nonempty_ofChainFreeness rest
      exact ⟨.cons (edgeEquivalenceOfFreeness _ _ h) tail⟩

/-- Chosen exact semantics induced by a free-tuple chain. -/
noncomputable def ExactChain.ofChainFreeness {c : PresentationCode}
    {layers : List (List (Raw × Raw))} (h : ChainFreeness c layers) :
    ExactChain c layers :=
  Classical.choice (ExactChain.nonempty_ofChainFreeness h)

/-! ## Central edges require no freeness -/

/-- A central edge has identical source and target word families. -/
theorem central_sourceWord_eq_targetWord (c : PresentationCode)
    (words : List Raw) :
    sourceWord c (centralEdges words) = targetWord c (centralEdges words) := by
  funext i
  simp [sourceWord, targetWord, centralEdges]

/-- Hence the generated source and target subgroups of a central edge are
literally equal. -/
theorem central_srcSub_eq_tgtSub (c : PresentationCode) (words : List Raw) :
    HNNPresentation.srcSub (codeRels c) (sourceWord c (centralEdges words)) =
      HNNPresentation.tgtSub (codeRels c)
        (targetWord c (centralEdges words)) := by
  rw [← central_sourceWord_eq_targetWord c words]
  rfl

/-- The exact identity equivalence for a centralizing HNN layer. -/
noncomputable def centralEdgeEquivalence (c : PresentationCode)
    (words : List Raw) : EdgeEquivalence c (centralEdges words) where
  equiv := MulEquiv.subgroupCongr (central_srcSub_eq_tgtSub c words)
  generator := by
    intro i
    change HNNPresentation.srcGen (codeRels c)
        (sourceWord c (centralEdges words)) i =
      HNNPresentation.tgtGen (codeRels c)
        (targetWord c (centralEdges words)) i
    simp only [HNNPresentation.srcGen, HNNPresentation.tgtGen,
      central_sourceWord_eq_targetWord]

/-- One central layer is an exact edge chain without any independence or
freeness hypothesis on its payload words. -/
noncomputable def singletonCentral (c : PresentationCode) (words : List Raw) :
    ExactChain c [centralEdges words] :=
  .cons (centralEdgeEquivalence c words) (.nil _)

/-- Append an arbitrary central detector to an already exact chain. -/
noncomputable def ExactChain.appendCentral {c : PresentationCode}
    {layers : List (List (Raw × Raw))} (h : ExactChain c layers)
    (words : List Raw) :
    ExactChain c (layers ++ [centralEdges words]) :=
  h.append (singletonCentral (multiEdgeCode c layers) words)

/-! ## The detector-last compiler -/

/-- The genuine inner obligations: the `tau` family, followed by `d` and
`sigma`, but not the central detector. -/
def innerCompilerLayers (x : TowerInput) : List (List (Raw × Raw)) :=
  x.2.1 ++ [x.2.2.1, x.2.2.2.1]

theorem innerCompilerLayers_append_detector (x : TowerInput) :
    innerCompilerLayers x ++ [centralEdges x.2.2.2.2] = compilerLayers x := by
  simp [innerCompilerLayers, compilerLayers, List.append_assoc]

/-- **The detector layer is no longer an obligation.**  Exact semantics for
the inner `tau/d/sigma` chain extend unconditionally to exact semantics for the
whole detector-last compiler. -/
noncomputable def compilerChainOfInner (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x)) :
    ExactChain x.1 (compilerLayers x) := by
  rw [← innerCompilerLayers_append_detector x]
  exact h.appendCentral x.2.2.2.2

/-- Equality of presentation codes transports their presented groups by an
explicit equivalence. -/
def codeCarrierEquiv {c d : PresentationCode} (h : c = d) :
    Carrier c ≃* Carrier d := by
  subst d
  exact MulEquiv.refl _

/-- Transport a numbered generator index along equality of presentation
codes. -/
def codeGeneratorIndex {c d : PresentationCode} (h : c = d) :
    Fin (genCount c) → Fin (genCount d) := by
  subst d
  exact id

@[simp] theorem codeGeneratorIndex_val {c d : PresentationCode}
    (h : c = d) (i : Fin (genCount c)) :
    (codeGeneratorIndex h i : ℕ) = i := by
  subst d
  rfl

@[simp] theorem codeCarrierEquiv_generator {c d : PresentationCode}
    (h : c = d) (i : Fin (genCount c)) :
    codeCarrierEquiv h (PresentedGroup.of i) =
      PresentedGroup.of (codeGeneratorIndex h i) := by
  subst d
  rfl

/-- The original coded group embeds in the complete detector-last finite
presentation as soon as the genuine inner edge equivalences are supplied. -/
noncomputable def compilerEmbedding (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x)) :
    Carrier x.1 →* Carrier (compile x) :=
  (codeCarrierEquiv (multiEdgeCode_compilerLayers x)).toMonoidHom.comp
    (compilerChainOfInner x h).embedding

/-- The explicit output-generator index carrying a numbered generator of the
input presentation through every compiler layer. -/
def compilerMarkedIndex (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x))
    (i : Fin (genCount x.1)) : Fin (genCount (compile x)) :=
  codeGeneratorIndex (multiEdgeCode_compilerLayers x)
    ((compilerChainOfInner x h).markedIndex i)

@[simp] theorem compilerMarkedIndex_val (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x))
    (i : Fin (genCount x.1)) :
    (compilerMarkedIndex x h i : ℕ) = i := by
  unfold compilerMarkedIndex
  rw [codeGeneratorIndex_val, ExactChain.markedIndex_val]

/-- Literal one-letter word spelling the image of an input generator in the
emitted finite presentation. -/
def compilerMarkedWord (x : TowerInput)
    (i : Fin (genCount x.1)) : Raw :=
  [((i : ℕ), true)]

theorem compilerEmbedding_injective (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x)) :
    Function.Injective (compilerEmbedding x h) :=
  (codeCarrierEquiv (multiEdgeCode_compilerLayers x)).injective.comp
    (compilerChainOfInner x h).embedding_injective

/-- The compiler embedding is marked: every input generator is sent to its
explicit numbered generator in the emitted finite presentation. -/
theorem compilerEmbedding_generator (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x))
    (i : Fin (genCount x.1)) :
    compilerEmbedding x h (PresentedGroup.of i) =
      PresentedGroup.of (compilerMarkedIndex x h i) := by
  unfold compilerEmbedding compilerMarkedIndex
  change codeCarrierEquiv (multiEdgeCode_compilerLayers x)
      ((compilerChainOfInner x h).embedding (PresentedGroup.of i)) =
    PresentedGroup.of
      (codeGeneratorIndex (multiEdgeCode_compilerLayers x)
        ((compilerChainOfInner x h).markedIndex i))
  rw [(compilerChainOfInner x h).embedding_generator]
  exact codeCarrierEquiv_generator (multiEdgeCode_compilerLayers x)
    ((compilerChainOfInner x h).markedIndex i)

/-- Evaluating the emitted one-letter mark gives exactly the image under the
compiler embedding. -/
theorem compilerEmbedding_eq_compiledWord (x : TowerInput)
    (h : ExactChain x.1 (innerCompilerLayers x))
    (i : Fin (genCount x.1)) :
    compilerEmbedding x h (PresentedGroup.of i) =
      compiledWord x (compilerMarkedWord x i) := by
  rw [compilerEmbedding_generator]
  unfold compiledWord compilerMarkedWord
  rw [RawWord.wordOf_pos]
  have hi : letterOf (compile x) (i : ℕ) =
      compilerMarkedIndex x h i := by
    have hil : (i : ℕ) < genCount (compile x) := by
      rw [← compilerMarkedIndex_val x h i]
      exact (compilerMarkedIndex x h i).isLt
    apply Fin.ext
    exact (RawWord.letterOf_val_of_lt (compile x)
      hil).trans
        (compilerMarkedIndex_val x h i).symm
  rw [hi]
  rfl

end

end FreeEdgeTowerExactIteration
end GroupApproximation

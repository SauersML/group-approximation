import GroupApproximation.Computability.FreeEdgeTowerExactEdge

/-!
# Exact subgroup-equivalence edge chains

This is the exact counterpart of `FreeEdgeTowerIteration.ChainFreeness`.
Instead of requiring the displayed source and target tuples to be free, each
layer carries precisely the subgroup equivalence used by the HNN extension.
-/

namespace GroupApproximation
namespace FreeEdgeTowerExactIteration

open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics

noncomputable section

/-- Exact subgroup-equivalence data for a dependent chain of raw HNN layers. -/
inductive ExactChain : (c : PresentationCode) →
    List (List (Raw × Raw)) → Type
  | nil (c) : ExactChain c []
  | cons {c edges layers} : EdgeEquivalence c edges →
      ExactChain (edgeCode c edges) layers →
      ExactChain c (edges :: layers)

namespace ExactChain

/-- The final numbered generator reached from an original numbered generator.
Every edge appends its stable letter, so this is also a computable marking of
the original finite alphabet in the final presentation. -/
def markedIndex : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → ExactChain c layers →
      Fin (genCount c) → Fin (genCount (multiEdgeCode c layers))
  | _, [], .nil _, i => i
  | _, _ :: _, .cons _ tail, i =>
      tail.markedIndex (letterOf _ i)

/-- Adding HNN stable letters never renumbers an existing generator. -/
@[simp] theorem markedIndex_val : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → (h : ExactChain c layers) →
      ∀ i : Fin (genCount c), (h.markedIndex i : ℕ) = i
  | _, [], .nil _, i => rfl
  | c, edges :: _, .cons _ tail, i => by
      change (tail.markedIndex (letterOf (edgeCode c edges) i) : ℕ) = i
      rw [tail.markedIndex_val]
      apply RawWord.letterOf_val_of_lt
      rw [edgeCode_genCount]
      omega

/-- The homomorphism from the original presentation into the final computed
presentation. -/
noncomputable def embedding : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → ExactChain c layers →
      Carrier c →* Carrier (multiEdgeCode c layers)
  | _, [], .nil _ => MonoidHom.id _
  | _, _ :: _, .cons E tail => tail.embedding.comp E.oldHom

/-- Every exact edge chain preserves the original group. -/
theorem embedding_injective : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → (h : ExactChain c layers) →
      Function.Injective h.embedding
  | _, [], .nil _ => Function.injective_id
  | _, _ :: _, .cons E tail =>
      tail.embedding_injective.comp E.oldHom_injective

/-- The chain embedding sends every original generator to its explicit final
marked generator. -/
theorem embedding_generator : {c : PresentationCode} →
    {layers : List (List (Raw × Raw))} → (h : ExactChain c layers) →
      ∀ i : Fin (genCount c),
        h.embedding (PresentedGroup.of i) = PresentedGroup.of (h.markedIndex i)
  | _, [], .nil _, i => rfl
  | _, _ :: _, .cons E tail, i => by
      change tail.embedding (E.oldHom (PresentedGroup.of i)) =
        PresentedGroup.of (tail.markedIndex (letterOf _ i))
      rw [E.oldHom_generator]
      exact tail.embedding_generator (letterOf _ i)

/-- Concatenate two dependent exact chains. -/
noncomputable def append : {c : PresentationCode} →
    {left right : List (List (Raw × Raw))} →
    ExactChain c left → ExactChain (multiEdgeCode c left) right →
      ExactChain c (left ++ right)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons E rest, tail => .cons E (rest.append tail)

end ExactChain

end


end FreeEdgeTowerExactIteration
end GroupApproximation

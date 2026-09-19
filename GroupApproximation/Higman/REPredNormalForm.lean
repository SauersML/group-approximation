import Mathlib.Computability.RE
import Mathlib.Computability.PartrecCode

/-!
# Recursively enumerable predicates in search form

Pinned Mathlib's `REPred` API is one-directional.  It has
`WordProblemRE.rePred_exists_eq_true` in this repository --- an existential
over a `Primcodable` type with a computable `Bool` matrix is recursively
enumerable --- and nothing going the other way.  That asymmetry blocks
*chaining*: a hypothesis of the form `REPred p` cannot be fed into any
construction that needs a certificate, because there is no way to extract one.

It bites concretely in this lane.  `Higman.RelatorRE` proves that a group
presented by an enumerable relator set is recursively presented, but it asks
for the relators as a `Primrec₂` search; and `Higman.BridgeRecursive` has to
consume a `Higman.RecursivePresentation`, whose word-problem field is a bare
`REPred`.  Without the converse the two cannot be composed.

The converse is Kleene's normal form, and Mathlib has every ingredient:
`Nat.Partrec.Code.exists_code`, `Nat.Partrec.Code.evaln_complete` and
`Nat.Partrec.Code.primrec_evaln`.  A predicate is recursively enumerable
exactly when it is the projection of a primitive-recursive relation, the
bounding parameter being the number of steps of the universal machine.
-/

namespace GroupApproximation
namespace Higman

open Nat.Partrec

/-- **Kleene normal form for `REPred`.**  A recursively enumerable predicate is
a primitive-recursive search.  This is the converse of
`WordProblemRE.rePred_exists_eq_true`, and pinned Mathlib does not have it. -/
theorem exists_primrec_of_rePred {α : Type} [Primcodable α] {p : α → Prop}
    (hp : REPred p) :
    ∃ f : α → ℕ → Bool, Primrec₂ f ∧ ∀ a, p a ↔ ∃ n, f a n = true := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hp
  have hdom : ∀ a : α, (Code.eval c (Encodable.encode a)).Dom ↔ p a := by
    intro a
    rw [hc]
    simp [Encodable.encodek, Part.assert]
  refine ⟨fun a n ↦ decide (Code.evaln n c (Encodable.encode a) ≠ (none : Option ℕ)), ?_, ?_⟩
  · have h1 : Primrec fun x : α × ℕ ↦ Code.evaln x.2 c (Encodable.encode x.1) :=
      Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c))
          (Primrec.encode.comp Primrec.fst))
    exact (PrimrecPred.not (Primrec.eq.comp h1 (Primrec.const (none : Option ℕ)))).decide
  · intro a
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 ((hdom a).2 ha)
      obtain ⟨k, hk⟩ := Code.evaln_complete.1 hx
      refine ⟨k, ?_⟩
      rw [Option.mem_def] at hk
      simp [hk]
    · rintro ⟨k, hk⟩
      rw [decide_eq_true_iff] at hk
      refine (hdom a).1 (Part.dom_iff_mem.2 ?_)
      rcases hopt : Code.evaln k c (Encodable.encode a) with _ | x
      · exact (hk hopt).elim
      · exact ⟨x, Code.evaln_sound (Option.mem_def.2 hopt)⟩

/-- The same, packaged as the hypothesis `Higman.RelatorRE` consumes. -/
theorem exists_search_of_rePred {α : Type} [Primcodable α] {p : α → Prop}
    (hp : REPred p) :
    ∃ f : α → ℕ → Bool, Primrec₂ f ∧ REPred fun a ↦ ∃ n, f a n = true := by
  obtain ⟨f, hf, hspec⟩ := exists_primrec_of_rePred hp
  exact ⟨f, hf, hp.of_eq hspec⟩

end Higman
end GroupApproximation

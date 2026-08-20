import GroupApproximation.Higman.RecursivePresentationBridge

/-!
# Enumerating relator sets

`Higman.RelatorRE` asks for a relator set in the form "membership is a
primitive-recursive search over `ℕ`".  The relator sets that actually arise are
built two ways: as unions (a construction adds relators to those of its base),
and as the image of a computably-indexed family (the stable-letter relators of
an HNN extension, one for each generator of the associated subgroup).  This
file supplies both, together with the re-indexing that lets a search over any
`Primcodable` type be presented as a search over `ℕ`.

Membership in an indexed family is itself a search rather than a decision,
because equality in a free group is tested through the repository's deletion
certificates (`Computability.applySteps`); that costs nothing, since the
certificate simply grows by one component.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  Re-indexing a search -/

/-- A search over any `Primcodable` type is a search over `ℕ`. -/
theorem search_reindex {α β : Type} [Primcodable α] [Primcodable β] [Inhabited β]
    (g : α → β → Bool) (hg : Primrec₂ g) :
    ∃ f : α → ℕ → Bool, Primrec₂ f ∧
      ∀ a, (∃ b, g a b = true) ↔ ∃ n, f a n = true := by
  refine ⟨fun a n ↦ g a ((Encodable.decode (α := β) n).getD default), ?_, ?_⟩
  · exact hg.comp Primrec.fst
      (Primrec.option_getD.comp
        (Primrec.decode.comp Primrec.snd) (Primrec.const default))
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨Encodable.encode b, by simpa using hb⟩
    · rintro ⟨n, hn⟩
      exact ⟨_, hn⟩

/-! ## 2.  Unions -/

/-- The union of two enumerable relator sets is enumerable. -/
theorem search_union {S T : Set (FreeGroup ℕ)}
    {fS fT : RawWord → ℕ → Bool} (hS : Primrec₂ fS) (hT : Primrec₂ fT)
    (hSspec : ∀ v : RawWord, freeEval v ∈ S ↔ ∃ n, fS v n = true)
    (hTspec : ∀ v : RawWord, freeEval v ∈ T ↔ ∃ n, fT v n = true) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      ∀ v : RawWord, freeEval v ∈ S ∪ T ↔ ∃ n, f v n = true := by
  refine ⟨fun v n ↦ fS v n || fT v n, ?_, ?_⟩
  · exact Primrec.or.comp hS hT
  · intro v
    constructor
    · rintro (hv | hv)
      · obtain ⟨n, hn⟩ := (hSspec v).1 hv
        exact ⟨n, by simp [hn]⟩
      · obtain ⟨n, hn⟩ := (hTspec v).1 hv
        exact ⟨n, by simp [hn]⟩
    · rintro ⟨n, hn⟩
      rcases Bool.or_eq_true_iff.1 hn with h | h
      · exact Or.inl ((hSspec v).2 ⟨n, h⟩)
      · exact Or.inr ((hTspec v).2 ⟨n, h⟩)

/-! ## 3.  A computably indexed family -/

/-- Membership in the image of an indexed family of raw words, as a search:
the index, and a deletion certificate witnessing the free-group equality. -/
theorem mem_range_iff_search (r : ℕ → RawWord) (v : RawWord) :
    freeEval v ∈ Set.range (fun i ↦ freeEval (r i)) ↔
      ∃ p : ℕ × List ℕ,
        Computability.applySteps (r p.1 ++ invRaw v) p.2 = some [] := by
  constructor
  · rintro ⟨i, hi⟩
    have h1 : freeEval (r i ++ invRaw v) = 1 := by
      unfold freeEval
      rw [evalRaw_append, evalRaw_invRaw]
      show evalRaw FreeGroup.of (r i) * (evalRaw FreeGroup.of v)⁻¹ = 1
      rw [mul_inv_eq_one]
      exact hi
    obtain ⟨is, his⟩ := (freeEval_eq_one_iff _).1 h1
    exact ⟨(i, is), his⟩
  · rintro ⟨⟨i, is⟩, his⟩
    refine ⟨i, ?_⟩
    have h1 : freeEval (r i ++ invRaw v) = 1 :=
      (freeEval_eq_one_iff _).2 ⟨is, his⟩
    unfold freeEval at h1
    rw [evalRaw_append, evalRaw_invRaw, mul_inv_eq_one] at h1
    exact h1

/-- The search of `mem_range_iff_search` is primitive recursive when the family
is. -/
theorem primrec_rangeSearch {r : ℕ → RawWord} (hr : Primrec r) :
    Primrec₂ fun (v : RawWord) (p : ℕ × List ℕ) ↦
      decide (Computability.applySteps (r p.1 ++ invRaw v) p.2 = some []) := by
  refine (Primrec.eq.comp ?_ (Primrec.const (some []))).decide
  refine Computability.primrec_applySteps.comp ?_
    (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_append.comp
    (hr.comp (Primrec.fst.comp Primrec.snd))
    (primrec_invRaw.comp Primrec.fst)

end Higman
end GroupApproximation

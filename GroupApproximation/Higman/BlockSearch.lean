import GroupApproximation.Higman.BlockWordProblem

/-!
# (B1) as one unbounded search

`Higman.BlockWordProblem` reduces recursive enumerability of
`{w | evalRaw pcGen w = 1}` to a conjunction, over a list computed from `w`,
of instances of `AdianRabinWordProblem.wordProblemPred`.  This file turns that
conjunction into a **single existential over a `Primcodable` type with a
`Bool` matrix** --- the shape `WordProblemRE.rePred_exists_eq_true` consumes.

The move is certificate merging, not a closure property of `REPred`.  Mathlib's
`REPred` API has no conjunction lemma; but
`WordProblemRE.wordProblemPred_iff_exists` presents each conjunct as
`∃ p : SearchData, searchCheck _ p = true`, so a conjunction of finitely many of
them is one existential over a *lookup list* pairing each block with its
certificate.

The lookup-list shape is chosen over the more obvious "list of certificates in
the same order, zipped" for a reason that is about the next step, not about
elegance: `∀ a ∈ L, …` and `∃ q ∈ ps, …` are both primitive recursive over
`Primcodable` types (`PrimrecRel.forall_mem_list`, `PrimrecRel.exists_mem_list`),
whereas pinned Mathlib has no `Primrec` fact for `List.zip`.  So this shape is
the one whose matrix can actually be proved computable; see
`Higman.BlockComputable`.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem
open GroupApproximation.WordProblemRE

/-! ## 1.  Merging witnesses along a list -/

/-- **A finite family of existentials is one existential over a lookup list.**
No induction: the list is `l.attach.map`, with the witness chosen at each
element. -/
theorem forall_mem_exists_iff_exists_lookup {α β : Type} (l : List α)
    (P : α → β → Bool) :
    (∀ a ∈ l, ∃ b : β, P a b = true) ↔
      ∃ ps : List (α × β), ∀ a ∈ l, ∃ q ∈ ps, q.1 = a ∧ P a q.2 = true := by
  classical
  constructor
  · intro h
    refine ⟨l.attach.map fun x ↦ (x.1, Classical.choose (h x.1 x.2)), ?_⟩
    intro a ha
    refine ⟨(a, Classical.choose (h a ha)), ?_, rfl,
      Classical.choose_spec (h a ha)⟩
    exact List.mem_map.2 ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩
  · rintro ⟨ps, hps⟩ a ha
    obtain ⟨q, -, -, hq2⟩ := hps a ha
    exact ⟨q.2, hq2⟩

/-! ## 2.  The search space and the search predicate -/

/-- The search space: a lookup list pairing blocks with search certificates. -/
abbrev BlockData : Type := List (PresentationCode × SearchData)

/-- **The search predicate.**  Every block of `w` has a certificate in the
lookup list. -/
def BlockSolves (w : RawWord) (ps : BlockData) : Prop :=
  ∀ c ∈ blockList w, ∃ q ∈ ps,
    q.1 = c ∧ searchCheck (c, blockWord w c) q.2 = true

instance blockSolves_decidable (w : RawWord) (ps : BlockData) :
    Decidable (BlockSolves w ps) := by
  unfold BlockSolves
  infer_instance

/-- The matrix of the search, as a `Bool`. -/
def blockCheck (w : RawWord) (ps : BlockData) : Bool :=
  decide (BlockSolves w ps)

theorem blockCheck_eq_true_iff (w : RawWord) (ps : BlockData) :
    blockCheck w ps = true ↔ BlockSolves w ps :=
  decide_eq_true_iff

/-! ## 3.  Triviality is one unbounded search -/

theorem evalRaw_pcGen_eq_one_iff_blockCheck (w : RawWord) :
    evalRaw pcGen w = 1 ↔ ∃ ps : BlockData, blockCheck w ps = true := by
  have h1 : evalRaw pcGen w = 1 ↔
      ∀ c ∈ blockList w, wordProblemPred (c, blockWord w c) :=
    evalRaw_pcGen_eq_one_iff_wordProblem w
  have h2 : (∀ c ∈ blockList w, wordProblemPred (c, blockWord w c)) ↔
      ∀ c ∈ blockList w, ∃ p : SearchData,
        searchCheck (c, blockWord w c) p = true :=
    forall_congr' fun c => imp_congr_right fun _ =>
      wordProblemPred_iff_exists (c, blockWord w c)
  rw [h1, h2]
  refine (forall_mem_exists_iff_exists_lookup (blockList w)
    (fun c p ↦ searchCheck (c, blockWord w c) p)).trans ?_
  constructor
  · rintro ⟨ps, hps⟩
    exact ⟨ps, (blockCheck_eq_true_iff w ps).2 hps⟩
  · rintro ⟨ps, hps⟩
    exact ⟨ps, (blockCheck_eq_true_iff w ps).1 hps⟩

end Higman
end GroupApproximation

import GroupApproximation.GGT.DGOProposition414BalancedSplit

/-!
# Broken-component sets and their greedy chord assignments

For each half of the balanced split, the broken set is not additional data: it
is the finite subset of original distinguished components which fail to remain
isolated in that half.  This file forms that subset, chooses the chord partner
whose existence is supplied by `exists_chord_partner_firstHalf` (or its wrapped
analogue), proves partner injectivity, and constructs the greedy interval
index.  The two halves are then combined into the exact
`TwoHalfGreedyFamilyIndex` used by the interval surgery.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The distinguished indices whose components fail to stay isolated in one
half. -/
noncomputable def brokenSet (I : Finset ℕ) (survives : ℕ → Prop) : Finset ℕ :=
  by
    classical
    exact I.filter fun s => ¬ survives s

theorem mem_brokenSet_iff {I : Finset ℕ} {survives : ℕ → Prop} {s : ℕ} :
    s ∈ brokenSet I survives ↔ s ∈ I ∧ ¬ survives s := by
  classical
  simp [brokenSet]

/-- One half's broken components, their injective chord partners, and the
resulting greedy connector-interval index. -/
structure BrokenHalfAssignment (I : Finset ℕ) (survives : ℕ → Prop)
    (pos : ℕ → ℕ) (chordLength : ℕ) where
  partner : ℕ → ℕ
  partner_lt : ∀ s ∈ brokenSet I survives, partner s < chordLength
  partner_injective : Set.InjOn partner (↑(brokenSet I survives) : Set ℕ)
  index : GreedyHalfFamilyIndex (brokenSet I survives) pos partner chordLength

/-- Construct one half assignment from the exact output of the isolation
argument: every broken source has a chord component connected to it, and
distinct sources are separated along the arc. -/
theorem exists_brokenHalfAssignment
    (D : RelGenSet G Λ) (halfBase : G)
    (half : List (RelLetter G Λ)) (I : Finset ℕ)
    (survives : ℕ → Prop) (lam : ℕ → Λ) (pos : ℕ → ℕ)
    (chordLength : ℕ) (chordPos : ℕ → ℕ)
    (hpos : Set.InjOn pos (↑I : Set ℕ))
    (hsep : ∀ s ∈ brokenSet I survives, ∀ t ∈ brokenSet I survives,
      pos s ≠ pos t →
      ¬ Connected D.fam (lam s) halfBase half (pos s) (pos t))
    (hexists : ∀ s ∈ brokenSet I survives, ∃ y : ℕ,
      y < chordLength ∧ IsCompStart (lam s) half (chordPos y) ∧
      Connected D.fam (lam s) halfBase half (pos s) (chordPos y)) :
    Nonempty (BrokenHalfAssignment I survives pos chordLength) := by
  classical
  let B := brokenSet I survives
  have hposB : Set.InjOn pos (↑B : Set ℕ) := by
    intro s hs t ht heq
    apply hpos
    · exact (mem_brokenSet_iff.mp hs).1
    · exact (mem_brokenSet_iff.mp ht).1
    · exact heq
  let partner : ℕ → ℕ := fun s =>
    if hs : s ∈ B then Classical.choose (hexists s hs) else 0
  have hpartner : ∀ s ∈ B,
      partner s < chordLength ∧
      IsCompStart (lam s) half (chordPos (partner s)) ∧
      Connected D.fam (lam s) halfBase half (pos s)
        (chordPos (partner s)) := by
    intro s hs
    simpa [partner, hs] using Classical.choose_spec (hexists s hs)
  have hfullInj : Set.InjOn (fun s => chordPos (partner s)) (↑B : Set ℕ) :=
    chordPartner_injOn D halfBase half B lam pos
      (fun s => chordPos (partner s)) hposB hsep
      (fun s hs => (hpartner s hs).2.1)
      (fun s hs => (hpartner s hs).2.2)
  have hinj : Set.InjOn partner (↑B : Set ℕ) := by
    intro s hs t ht heq
    apply hfullInj hs ht
    change chordPos (partner s) = chordPos (partner t)
    rw [heq]
  have hrange : ∀ s ∈ B, partner s < chordLength := by
    intro s hs
    exact (hpartner s hs).1
  obtain ⟨index⟩ := exists_greedyHalfFamilyIndex B pos partner chordLength
    hposB hinj hrange
  exact ⟨{
    partner := partner
    partner_lt := hrange
    partner_injective := hinj
    index := index
  }⟩

/-- The two broken sets and partner assignments obtained independently from
the two balanced halves. -/
structure TwoHalfBrokenAssignment (firstI secondI : Finset ℕ)
    (firstSurvives secondSurvives : ℕ → Prop)
    (firstPos secondPos : ℕ → ℕ) (chordLength : ℕ) where
  first : BrokenHalfAssignment firstI firstSurvives firstPos chordLength
  second : BrokenHalfAssignment secondI secondSurvives secondPos chordLength

namespace TwoHalfBrokenAssignment

/-- The two constructed half indices form the common two-half greedy index. -/
def index {firstI secondI : Finset ℕ}
    {firstSurvives secondSurvives : ℕ → Prop}
    {firstPos secondPos : ℕ → ℕ} {chordLength : ℕ}
    (A : TwoHalfBrokenAssignment firstI secondI firstSurvives secondSurvives
      firstPos secondPos chordLength) :
    TwoHalfGreedyFamilyIndex
      (brokenSet firstI firstSurvives) (brokenSet secondI secondSurvives)
      firstPos A.first.partner secondPos A.second.partner chordLength where
  first := A.first.index
  second := A.second.index

end TwoHalfBrokenAssignment

end DGOProposition414
end GGT
end GroupApproximation

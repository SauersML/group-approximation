import GroupApproximation.GGT.DGOLemma421Diagram
import GroupApproximation.GGT.DGOLemma421OrderedBridge

/-!
# Ordered occurrence matches for DGO Lemma 4.21(b)

The finite-absorption part of the proof selects matched peripheral components
on both words.  This module names the strictly smaller order interface needed
to finish the diagram: each selected occurrence is increasing, no peripheral
rank lies between adjacent selections, and the selected starts satisfy the
coset identity.  The two no-intermediate clauses give both separator families
through the diagram lemmas, so the resulting payload is exactly the ordered
block consumed by `DGOLemma421b`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Ordered peripheral occurrences together with the cross-word start-coset
matches required by the final DGO diagram argument. -/
structure DGO421OrderedOccurrenceMatch
    (D : RelGenSet G Λ) (p q : List (RelLetter G Λ)) (K : ℕ) where
  pOccurrence : ℕ → Fin (peripheralPositions p).card
  qOccurrence : ℕ → Fin (peripheralPositions q).card
  label : ℕ → Λ
  pLabel : ∀ t : ℕ, t < K →
    (peripheralOccurrence p (pOccurrence t)).label = label t
  qLabel : ∀ t : ℕ, t < K →
    (peripheralOccurrence q (qOccurrence t)).label = label t
  pStrict : ∀ t : ℕ, t + 1 < K →
    (pOccurrence t).val < (pOccurrence (t + 1)).val
  pNoIntermediate : ∀ t : ℕ, t + 1 < K →
    ∀ z : Fin (peripheralPositions p).card,
      (pOccurrence t).val < z.val →
      z.val < (pOccurrence (t + 1)).val → False
  qStrict : ∀ t : ℕ, t + 1 < K →
    (qOccurrence t).val < (qOccurrence (t + 1)).val
  qNoIntermediate : ∀ t : ℕ, t + 1 < K →
    ∀ z : Fin (peripheralPositions q).card,
      (qOccurrence t).val < z.val →
      z.val < (qOccurrence (t + 1)).val → False
  cosetMatch : ∀ t : ℕ, t < K →
    (vertex (1 : G) p
      (peripheralOccurrence p (pOccurrence t)).pos)⁻¹ *
      vertex (1 : G) q
        (peripheralOccurrence q (qOccurrence t)).pos ∈ D.fam (label t)

/-- The ordered occurrence interface assembles the exact natural-indexed
ordered block payload. -/
noncomputable def DGO421OrderedOccurrenceMatch.toPayload
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)} {K : ℕ}
    (hpW1 : WWord.IsWOne p) (hpW3 : WWord.IsWThree D p)
    (hqW1 : WWord.IsWOne q) (hqW3 : WWord.IsWThree D q)
    (O : DGO421OrderedOccurrenceMatch D p q K) :
    DGO421OrderedBlockPayload D p q K := by
  let ip : ℕ → ℕ := fun t =>
    (peripheralOccurrence p (O.pOccurrence t)).pos
  let kp : ℕ → ℕ := fun t => ip t + 1
  let iq : ℕ → ℕ := fun t =>
    (peripheralOccurrence q (O.qOccurrence t)).pos
  let kq : ℕ → ℕ := fun t => iq t + 1
  refine
    { ip := ip
      kp := kp
      iq := iq
      kq := kq
      lam := O.label
      pcomp := ?_
      qcomp := ?_
      psep := ?_
      qsep := ?_
      cosetMatch := ?_ }
  · intro t ht
    have hcomp := PeripheralOccurrence.isComp hpW3 (O.pOccurrence t)
    rw [O.pLabel t ht] at hcomp
    simpa [ip, kp] using hcomp
  · intro t ht
    have hcomp := PeripheralOccurrence.isComp hqW3 (O.qOccurrence t)
    rw [O.qLabel t ht] at hcomp
    simpa [iq, kq] using hcomp
  · intro t ht
    have hsep := oppositeContiguity_of_noIntermediateRank hpW1 hpW3
      (iq := ip) (kq := kp) (lam := O.label) (fun s hs => by
        have hcomp := PeripheralOccurrence.isComp hpW3 (O.pOccurrence s)
        rw [O.pLabel s hs] at hcomp
        simpa [ip, kp] using hcomp)
      O.pOccurrence (fun s hs => by rfl)
      O.pStrict O.pNoIntermediate t ht
    simpa [ip, kp] using hsep
  · intro t ht
    have hsep := oppositeContiguity_of_noIntermediateRank hqW1 hqW3
      (iq := iq) (kq := kq) (lam := O.label) (fun s hs => by
        have hcomp := PeripheralOccurrence.isComp hqW3 (O.qOccurrence s)
        rw [O.qLabel s hs] at hcomp
        simpa [iq, kq] using hcomp)
      O.qOccurrence (fun s hs => by rfl)
      O.qStrict O.qNoIntermediate t ht
    simpa [iq, kq] using hsep
  · intro t ht
    simpa [ip, iq] using O.cosetMatch t ht

/-! ## Trivial-group model -/

private def orderedMatchTrivialRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

private def orderedMatchTrivialWord : List (RelLetter PUnit Unit) :=
  [RelLetter.comp () ()]

/-- The one-component trivial model satisfies the ordered occurrence
interface.  Both no-intermediate fields are vacuous at `K = 1`, while the
start-coset equation is the identity in the top peripheral subgroup. -/
theorem DGO421OrderedOccurrenceMatch.trivialModel :
    Nonempty (DGO421OrderedOccurrenceMatch orderedMatchTrivialRelGenSet
      orderedMatchTrivialWord orderedMatchTrivialWord 1) := by
  have hcard : (peripheralPositions orderedMatchTrivialWord).card = 1 := by
    simp [orderedMatchTrivialWord, peripheralPositions]
  let occ : ℕ → Fin (peripheralPositions orderedMatchTrivialWord).card :=
    fun _ => ⟨0, by rw [hcard]; omega⟩
  refine ⟨
    { pOccurrence := occ
      qOccurrence := occ
      label := fun _ => ()
      pLabel := by
        intro t ht
        have ht0 : t = 0 := by omega
        subst t
        rfl
      qLabel := by
        intro t ht
        have ht0 : t = 0 := by omega
        subst t
        rfl
      pStrict := by
        intro t ht
        omega
      pNoIntermediate := by
        intro t ht z hz1 hz2
        omega
      qStrict := by
        intro t ht
        omega
      qNoIntermediate := by
        intro t ht z hz1 hz2
        omega
      cosetMatch := by
        intro t ht
        simp [orderedMatchTrivialRelGenSet, orderedMatchTrivialWord, occ] }⟩

end OsinComponents
end GGT
end GroupApproximation

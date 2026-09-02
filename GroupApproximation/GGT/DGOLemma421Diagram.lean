import GroupApproximation.GGT.DGOLemma421Components
import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.Algebra.HyperbolicGroup

/-!
# The two diagram interfaces in DGO Lemma 4.21

This module isolates the two elementary diagram facts used after the uniform
isolated-component estimate.  Reversing the fourth side needs the relative
base to be closed under inversion.  Once two opposite components are indexed
by successive peripheral ranks, their separator is the base-edge-or-trivial
path printed in Lemma 4.21(b).  The first statement is the exact admissibility
interface of the reversal construction; the second is the order step in the
four-gon diagram.  Both are independent of Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The symmetry assumption on the relative base needed to read `revWord` as a
word over the same relative alphabet.  This is the `X = X⁻¹` convention in
Dahmani--Guirardel--Osin's Section 4. -/
def DGO421BaseSymmetric (D : RelGenSet G Λ) : Prop :=
  ∀ x ∈ D.base, x⁻¹ ∈ D.base

/-- Base symmetry makes every reversed letter admissible, so every reversed
word is admissible.  This is the letter-bookkeeping step before the four-gon
is formed in the proof of DGO Lemma 4.21. -/
theorem isLetter_revWord_of_DGO421BaseSymmetric
    (D : RelGenSet G Λ) (hbase : DGO421BaseSymmetric D)
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a) :
    ∀ a ∈ revWord word, D.IsLetter a := by
  exact isLetter_of_mem_revWord D hbase hlet

/-- If the opposite-side peripheral ranks are successive, the corresponding
components have the separator required by Lemma 4.21(b).  The component
endpoints are reduced to singleton endpoints by (W3), and the separator itself
is the ordered-occurrence lemma from the preceding diagram paragraph. -/
theorem oppositeContiguity_of_rankSuccessor
    {D : RelGenSet G Λ} {q : List (RelLetter G Λ)} {K : ℕ}
    (hW1 : WWord.IsWOne q) (hW3 : WWord.IsWThree D q)
    {iq kq : ℕ → ℕ} {lam : ℕ → Λ}
    (hcomp : ∀ t : ℕ, t < K →
      IsComp (lam t) q (iq t) (kq t))
    (occ : ℕ → Fin (peripheralPositions q).card)
    (hocc : ∀ t : ℕ, t < K →
      (peripheralOccurrence q (occ t)).pos = iq t)
    (hrank : ∀ t : ℕ, t + 1 < K →
      (occ (t + 1)).val = (occ t).val + 1) :
    ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial q (kq t) (iq (t + 1)) := by
  intro t ht
  have hnextLt : (occ (t + 1)).val < (peripheralPositions q).card :=
    (occ (t + 1)).isLt
  have hsucc : (occ t).val + 1 < (peripheralPositions q).card := by
    have hrank' := hrank t ht
    omega
  have hsep := PeripheralOccurrence.baseEdgeOrTrivial_succ hW1 (occ t) hsucc
  have hocc_eq :
      (⟨(occ t).val + 1, hsucc⟩ : Fin (peripheralPositions q).card) =
        occ (t + 1) := by
    apply Fin.ext
    exact (hrank t ht).symm
  have hpos_t := hocc t (by omega)
  have hpos_next := hocc (t + 1) (by omega)
  have hend : kq t = iq t + 1 :=
    isComp_succ_of_isWThree hW3 (hcomp t (by omega))
  rw [hocc_eq, hpos_t, hpos_next] at hsep
  rw [hend]
  exact hsep

/-! ## Model tests -/

private def dgo421TrivialUnitRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

/-- The trivial group with one peripheral subgroup satisfies the base-symmetry
interface, so the reversal theorem has a genuine admissible model. -/
theorem DGO421BaseSymmetric_trivialModel :
    DGO421BaseSymmetric dgo421TrivialUnitRelGenSet := by
  intro x hx
  simp [dgo421TrivialUnitRelGenSet]

private def dgo421TrivialWord : List (RelLetter PUnit Bool) :=
  WWord.hullShape () () ()

private noncomputable def dgo421TrivialOccurrence (t : ℕ) :
    Fin (peripheralPositions dgo421TrivialWord).card :=
  ⟨t % 2, by
    have hcard : (peripheralPositions dgo421TrivialWord).card = 2 := by
      simp [dgo421TrivialWord, WWord.hullShape, peripheralPositions]
    rw [hcard]
    exact Nat.mod_lt t (by omega)⟩

private noncomputable def dgo421TrivialStart (t : ℕ) : ℕ :=
  (peripheralOccurrence dgo421TrivialWord
    (dgo421TrivialOccurrence t)).pos

/-- The two peripheral letters in Hull's three-letter model word have a
successive-rank separator.  This tests the opposite-side contiguity theorem
at `K = 2`, where its separator clause is non-vacuous. -/
theorem oppositeContiguity_of_rankSuccessor_trivialModel :
    ∀ t : ℕ, t + 1 < 2 →
      BaseEdgeOrTrivial dgo421TrivialWord
        (dgo421TrivialStart t + 1) (dgo421TrivialStart (t + 1)) := by
  let D : RelGenSet PUnit Bool :=
    { base := Set.univ
      fam := fun _ => ⊤
      symmetricGenerating := by
        have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
        rw [Finset.coe_univ] at h
        simpa only [Set.univ_union] using h }
  have hW1 : WWord.IsWOne dgo421TrivialWord := by
    exact WWord.isWOne_hullShape () () ()
  have hW3 : WWord.IsWThree D dgo421TrivialWord := by
    exact WWord.isWThree_hullShape D () () ()
  let occ : ℕ → Fin (peripheralPositions dgo421TrivialWord).card :=
    dgo421TrivialOccurrence
  let iq : ℕ → ℕ := dgo421TrivialStart
  let kq : ℕ → ℕ := fun t => dgo421TrivialStart t + 1
  let lam : ℕ → Bool := fun t =>
    (peripheralOccurrence dgo421TrivialWord (occ t)).label
  have hcomp : ∀ t : ℕ, t < 2 →
      IsComp (lam t) dgo421TrivialWord (iq t) (kq t) := by
    intro t ht
    have hread := (peripheralOccurrence dgo421TrivialWord (occ t)).read
    have hsingle := isComp_singleton_of_isWThree_read hW3 hread
    simpa [lam, iq, kq, occ, dgo421TrivialStart] using hsingle
  have hocc : ∀ t : ℕ, t < 2 →
      (peripheralOccurrence dgo421TrivialWord (occ t)).pos = iq t := by
    intro t ht
    rfl
  have hrank : ∀ t : ℕ, t + 1 < 2 →
      (occ (t + 1)).val = (occ t).val + 1 := by
    intro t ht
    have ht0 : t = 0 := by omega
    subst t
    simp [occ, dgo421TrivialOccurrence]
  intro t ht
  exact oppositeContiguity_of_rankSuccessor hW1 hW3 hcomp occ hocc hrank t ht

end OsinComponents
end GGT
end GroupApproximation

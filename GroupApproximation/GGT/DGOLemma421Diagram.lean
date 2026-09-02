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

/-- Reversal admissibility for every admissible relative word.  This is the
same letter condition used when the fourth side of the DGO four-gon is read
backwards. -/
def DGO421ReversalAdmissibility (D : RelGenSet G Λ) : Prop :=
  ∀ (word : List (RelLetter G Λ)),
    (∀ a ∈ word, D.IsLetter a) →
      ∀ a ∈ revWord word, D.IsLetter a

/-- Base symmetry makes every reversed letter admissible, so every reversed
word is admissible.  This is the letter-bookkeeping step before the four-gon
is formed in the proof of DGO Lemma 4.21. -/
theorem isLetter_revWord_of_DGO421BaseSymmetric
    (D : RelGenSet G Λ) (hbase : DGO421BaseSymmetric D)
    {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a) :
    ∀ a ∈ revWord word, D.IsLetter a := by
  exact isLetter_of_mem_revWord D hbase hlet

/-- Reversal admissibility is equivalent to inversion closure of the relative
base.  The forward direction tests the one-letter word `[base x]`; peripheral
letters are already closed under inversion inside their subgroups. -/
theorem dgo421ReversalAdmissibility_iff_baseSymmetric
    (D : RelGenSet G Λ) :
    DGO421ReversalAdmissibility D ↔ DGO421BaseSymmetric D := by
  constructor
  · intro h x hx
    have hlet : ∀ a ∈ ([RelLetter.base x] : List (RelLetter G Λ)),
        D.IsLetter a := by
      intro a ha
      have ha' : a = RelLetter.base x := List.eq_of_mem_singleton ha
      rw [ha']
      exact hx
    have hrev := h [RelLetter.base x] hlet
      (RelLetter.base x⁻¹) (by simp [revWord, invLetter])
    exact hrev
  · intro h word hlet
    exact isLetter_revWord_of_DGO421BaseSymmetric D h hlet

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

/-- A strictly increasing block with no peripheral rank between adjacent
entries has rank difference one.  This is the finite-order argument used to
turn an ordered block of opposite components into consecutive components. -/
omit [Group G] in
theorem rankSuccessor_of_noIntermediate
    {q : List (RelLetter G Λ)} {K : ℕ}
    (occ : ℕ → Fin (peripheralPositions q).card)
    (hstrict : ∀ t : ℕ, t + 1 < K →
      (occ t).val < (occ (t + 1)).val)
    (hno : ∀ t : ℕ, t + 1 < K →
      ∀ z : Fin (peripheralPositions q).card,
        (occ t).val < z.val → z.val < (occ (t + 1)).val → False) :
    ∀ t : ℕ, t + 1 < K →
      (occ (t + 1)).val = (occ t).val + 1 := by
  intro t ht
  have hlt := hstrict t ht
  by_contra hne
  have hgap : (occ t).val + 1 < (occ (t + 1)).val := by omega
  have hbound : (occ t).val + 1 < (peripheralPositions q).card := by
    exact lt_of_lt_of_le hgap (Nat.le_of_lt (occ (t + 1)).isLt)
  let z : Fin (peripheralPositions q).card :=
    ⟨(occ t).val + 1, hbound⟩
  exact hno t ht z (by dsimp [z]; omega) (by dsimp [z]; exact hgap)

/-- The no-intermediate-rank form of opposite contiguity.  Once the matched
opposite occurrences are ordered and exhaust the ranks between each pair,
the separator in Lemma 4.21(b) follows from the preceding successor lemma. -/
theorem oppositeContiguity_of_noIntermediateRank
    {D : RelGenSet G Λ} {q : List (RelLetter G Λ)} {K : ℕ}
    (hW1 : WWord.IsWOne q) (hW3 : WWord.IsWThree D q)
    {iq kq : ℕ → ℕ} {lam : ℕ → Λ}
    (hcomp : ∀ t : ℕ, t < K →
      IsComp (lam t) q (iq t) (kq t))
    (occ : ℕ → Fin (peripheralPositions q).card)
    (hocc : ∀ t : ℕ, t < K →
      (peripheralOccurrence q (occ t)).pos = iq t)
    (hstrict : ∀ t : ℕ, t + 1 < K →
      (occ t).val < (occ (t + 1)).val)
    (hno : ∀ t : ℕ, t + 1 < K →
      ∀ z : Fin (peripheralPositions q).card,
        (occ t).val < z.val → z.val < (occ (t + 1)).val → False) :
    ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial q (kq t) (iq (t + 1)) := by
  apply oppositeContiguity_of_rankSuccessor hW1 hW3 hcomp occ hocc
  exact rankSuccessor_of_noIntermediate occ hstrict hno

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

/-- The asymmetric relative alphabet on `Additive ℤ` has a symmetric union
because its peripheral subgroup is top, but its base is not inversion closed.
So reversal admissibility genuinely fails without the base-symmetry field. -/
private def dgo421AsymmetricAdditiveRelGenSet :
    RelGenSet (Multiplicative (ZMod 3)) Unit where
  base := {0, 1}
  fam := fun _ => ⊤
  symmetricGenerating := by
    constructor
    · intro x hx
      right
      simp
    · have hunion : ({0, 1} : Set (Multiplicative (ZMod 3))) ∪
          (⋃ _ : Unit,
            ((⊤ : Subgroup (Multiplicative (ZMod 3))) :
              Set (Multiplicative (ZMod 3)))) = Set.univ := by
        ext x
        simp
      rw [hunion]
      exact Subgroup.closure_univ

/-- The asymmetric model refutes reversal admissibility, so the equivalence
above is not a vacuous restatement of the union symmetry of `RelGenSet`. -/
theorem dgo421ReversalAdmissibility_asymmetricModel :
    ¬ DGO421ReversalAdmissibility dgo421AsymmetricAdditiveRelGenSet := by
  intro h
  have hbase := (dgo421ReversalAdmissibility_iff_baseSymmetric
    dgo421AsymmetricAdditiveRelGenSet).mp h
  have hone : (1 : Multiplicative (ZMod 3)) ∈
      dgo421AsymmetricAdditiveRelGenSet.base := by
    simp [dgo421AsymmetricAdditiveRelGenSet]
  have hinv := hbase 1 hone
  norm_num [dgo421AsymmetricAdditiveRelGenSet] at hinv

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

/-- In the two-rank model there is no intermediate peripheral rank, so the
no-intermediate version proves the same non-vacuous separator clause. -/
theorem oppositeContiguity_of_noIntermediateRank_trivialModel :
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
  have hstrict : ∀ t : ℕ, t + 1 < 2 →
      (occ t).val < (occ (t + 1)).val := by
    intro t ht
    have ht0 : t = 0 := by omega
    subst t
    simp [occ, dgo421TrivialOccurrence]
  have hno : ∀ t : ℕ, t + 1 < 2 →
      ∀ z : Fin (peripheralPositions dgo421TrivialWord).card,
        (occ t).val < z.val → z.val < (occ (t + 1)).val → False := by
    intro t ht z hz1 hz2
    have ht0 : t = 0 := by omega
    subst t
    have hcard : (peripheralPositions dgo421TrivialWord).card = 2 := by
      simp [dgo421TrivialWord, WWord.hullShape, peripheralPositions]
    rw [hcard] at z
    omega
  intro t ht
  exact oppositeContiguity_of_noIntermediateRank hW1 hW3 hcomp occ hocc
    hstrict hno t ht

end OsinComponents
end GGT
end GroupApproximation

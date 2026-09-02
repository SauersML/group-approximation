import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Ordered blocks for the final step of DGO Lemma 4.21(b)

The counting argument in `DGOLemma421Proof` gives a finite block of matched
source components.  The remaining DGO argument orders the target components
and makes the separators explicit.  This module records that ordered-block
payload and proves its direct conversion to the natural-indexed conclusion of
`DGOLemma421b`.  The payload is local to fixed words and a fixed `K`, so it is
strictly smaller than the full lemma and identifies the missing order argument.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Ordered component data for fixed fellow-travelling words.  The guards
`t < K` and `t + 1 < K` match the natural-indexed conclusion in the statement
of DGO Lemma 4.21(b). -/
structure DGO421OrderedBlockPayload
    (D : RelGenSet G Λ) (p q : List (RelLetter G Λ)) (K : ℕ) where
  ip : ℕ → ℕ
  kp : ℕ → ℕ
  iq : ℕ → ℕ
  kq : ℕ → ℕ
  lam : ℕ → Λ
  pcomp : ∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)
  qcomp : ∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)
  psep : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial p (kp t) (ip (t + 1))
  qsep : ∀ t : ℕ, t + 1 < K →
    BaseEdgeOrTrivial q (kq t) (iq (t + 1))
  cosetMatch : ∀ t : ℕ, t < K →
    (vertex (1 : G) p (ip t))⁻¹ * vertex (1 : G) q (iq t) ∈ D.fam (lam t)

/-- An ordered block payload is exactly the final witness package required by
the natural-indexed form of Lemma 4.21(b). -/
theorem DGO421OrderedBlockPayload.toStartCosetWitness
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)} {K : ℕ}
    (W : DGO421OrderedBlockPayload D p q K) :
    ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Λ),
      (∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)) ∧
      (∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial p (kp t) (ip (t + 1))) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial q (kq t) (iq (t + 1))) ∧
      (∀ t : ℕ, t < K →
        (vertex (1 : G) p (ip t))⁻¹ * vertex (1 : G) q (iq t) ∈ D.fam (lam t)) := by
  exact ⟨W.ip, W.kp, W.iq, W.kq, W.lam,
    W.pcomp, W.qcomp, W.psep, W.qsep, W.cosetMatch⟩

/-! ## Trivial-group model -/

private def orderedBridgeTrivialRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

private def orderedBridgeTrivialWord : List (RelLetter PUnit Unit) :=
  [RelLetter.comp () 1]

/-- The one-component trivial-group model supplies an ordered payload at
`K = 1`; both separator clauses are vacuous and the start-coset match is the
identity element of the top peripheral subgroup. -/
theorem DGO421OrderedBlockPayload.trivialModel :
    Nonempty (DGO421OrderedBlockPayload orderedBridgeTrivialRelGenSet
      orderedBridgeTrivialWord orderedBridgeTrivialWord 1) := by
  let hcomp : IsComp () orderedBridgeTrivialWord 0 1 := by
    refine ⟨by omega, by simp [orderedBridgeTrivialWord], ?_, ?_, ?_⟩
    · intro t ht0 ht1 ht
      have ht' : t = 0 := by omega
      subst ht'
      rfl
    · intro t ht
      omega
    · intro ht
      simp [orderedBridgeTrivialWord] at ht
  let W : DGO421OrderedBlockPayload orderedBridgeTrivialRelGenSet
      orderedBridgeTrivialWord orderedBridgeTrivialWord 1 :=
    { ip := fun _ => 0
      kp := fun _ => 1
      iq := fun _ => 0
      kq := fun _ => 1
      lam := fun _ => ()
      pcomp := by
        intro t ht
        simpa [orderedBridgeTrivialWord] using hcomp
      qcomp := by
        intro t ht
        simpa [orderedBridgeTrivialWord] using hcomp
      psep := by
        intro t ht
        omega
      qsep := by
        intro t ht
        omega
      cosetMatch := by
        intro t ht
        simp [orderedBridgeTrivialRelGenSet, orderedBridgeTrivialWord] }
  exact ⟨W⟩

end OsinComponents
end GGT
end GroupApproximation

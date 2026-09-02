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
    (D : RelGenSet G Λ) (vp vq : G)
    (p q : List (RelLetter G Λ)) (K : ℕ) where
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
    (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)

/-- An ordered block payload is exactly the final witness package required by
the natural-indexed form of Lemma 4.21(b). -/
theorem DGO421OrderedBlockPayload.toStartCosetWitness
    {D : RelGenSet G Λ} {vp vq : G} {p q : List (RelLetter G Λ)} {K : ℕ}
    (W : DGO421OrderedBlockPayload D vp vq p q K) :
    ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Λ),
      (∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)) ∧
      (∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial p (kp t) (ip (t + 1))) ∧
      (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial q (kq t) (iq (t + 1))) ∧
      (∀ t : ℕ, t < K →
        (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t)) := by
  exact ⟨W.ip, W.kp, W.iq, W.kq, W.lam,
    W.pcomp, W.qcomp, W.psep, W.qsep, W.cosetMatch⟩

/-- The order data still missing after the finite-absorption certificate has
been constructed.  It supplies the target component starts and ends, both
separator clauses, and the start-coset identity on the certificate's whole
matched block.  No polygon or counting hypotheses occur in this local record.
-/
structure DGO421FiniteAbsorptionOrderData
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    (cert : DGO421FiniteAbsorptionCertificate D p q N M K) where
  qIndex : ℕ → ℕ
  qEnd : ℕ → ℕ
  qComponent : ∀ (t : ℕ) (ht : t < K),
    IsComp (cert.label (cert.blockIndex ⟨t, ht⟩)) q
      (qIndex t) (qEnd t)
  pSeparator : ∀ (t : ℕ) (ht : t + 1 < K),
    BaseEdgeOrTrivial p
      (cert.source (cert.blockIndex ⟨t,
        Nat.lt_trans (Nat.lt_succ_self t) ht⟩) + 1)
      (cert.source (cert.blockIndex ⟨t + 1, ht⟩))
  qSeparator : ∀ (t : ℕ) (_ : t + 1 < K),
    BaseEdgeOrTrivial q (qEnd t) (qIndex (t + 1))
  cosetMatch : ∀ (t : ℕ) (ht : t < K),
    (vertex (1 : G) p (cert.source (cert.blockIndex ⟨t, ht⟩)))⁻¹ *
        vertex (1 : G) q (qIndex t) ∈
      D.fam (cert.label (cert.blockIndex ⟨t, ht⟩))

/-- The finite certificate and its order data assemble into the ordered-block
payload.  This is the precise local reduction of the DGO minimality argument:
only `DGO421FiniteAbsorptionOrderData` remains to be constructed. -/
noncomputable def DGO421FiniteAbsorptionOrderData.toPayload
    {D : RelGenSet G Λ} {p q : List (RelLetter G Λ)}
    {N M K : ℕ}
    {cert : DGO421FiniteAbsorptionCertificate D p q N M K}
    (O : DGO421FiniteAbsorptionOrderData cert) (hK : 0 < K) :
    DGO421OrderedBlockPayload D (1 : G) (1 : G) p q K := by
  let first : Fin K := ⟨0, hK⟩
  let blockAt : ℕ → Fin N := fun t =>
    if ht : t < K then cert.blockIndex ⟨t, ht⟩ else cert.blockIndex first
  let indexAt : ℕ → ℕ := fun t =>
    if ht : t < K then O.qIndex t else O.qIndex 0
  let endAt : ℕ → ℕ := fun t =>
    if ht : t < K then O.qEnd t else O.qEnd 0
  let ipAt : ℕ → ℕ := fun t => cert.source (blockAt t)
  let kpAt : ℕ → ℕ := fun t => cert.source (blockAt t) + 1
  let lamAt : ℕ → Λ := fun t => cert.label (blockAt t)
  refine
    { ip := ipAt
      kp := kpAt
      iq := indexAt
      kq := endAt
      lam := lamAt
      pcomp := ?_
      qcomp := ?_
      psep := ?_
      qsep := ?_
      cosetMatch := ?_ }
  · intro t ht
    exact cert.source_comp (blockAt t)
  · intro t ht
    simpa [lamAt, indexAt, endAt, blockAt, ht] using O.qComponent t ht
  · intro t ht
    have ht0 : t < K := by omega
    simpa [kpAt, ipAt, blockAt, ht0, ht] using O.pSeparator t ht
  · intro t ht
    have ht0 : t < K := by omega
    simpa [endAt, indexAt, blockAt, ht0, ht] using O.qSeparator t ht
  · intro t ht
    simpa [ipAt, indexAt, lamAt, blockAt, ht] using O.cosetMatch t ht

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
      (1 : PUnit) (1 : PUnit)
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
      (1 : PUnit) (1 : PUnit)
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

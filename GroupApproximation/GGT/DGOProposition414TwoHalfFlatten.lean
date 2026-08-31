import GroupApproximation.GGT.DGOProposition414Assembly

/-!
# Flattening the two DGO half-families

The component surgery for DGO Proposition 4.14 is performed independently on
the two sides of the cutting chord.  `TwoHalfAuxiliaryCycleFamily` and
`TwoHalfChargingConfiguration` retain that honest disjoint-union indexing,
whereas `AuxiliaryCycleFamilyCertificate`, the input of the quadratic
subdivision assembly, uses one `Fin k` family.

This file closes that indexing boundary.  It also concatenates the two actual
partner traversals.  Concatenation can add one jump across the join, so a chord
length `L` is conservatively recorded as `2L+1`; the resulting quadratic
certificate follows from the two half-family quadratic bounds without any
monotonicity assumption.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Concatenating two traversals whose entries lie in `[0,L]` costs at most
the sum of their internal traversal costs and one additional jump of size
`L`. -/
theorem chordTraversalCost_append_le {xs ys : List ℕ} {L : ℕ}
    (hxs : ∀ x ∈ xs, x ≤ L) (hys : ∀ y ∈ ys, y ≤ L) :
    chordTraversalCost (xs ++ ys) ≤
      chordTraversalCost xs + chordTraversalCost ys + L := by
  induction xs with
  | nil =>
      simp [chordTraversalCost]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp [chordTraversalCost]
          | cons y ys =>
              have hx : x ≤ L := hxs x (by simp)
              have hy : y ≤ L := hys y (by simp)
              have hdist : Nat.dist x y ≤ L := by
                rcases le_total x y with hxy | hyx
                · rw [Nat.dist_eq_sub_of_le hxy]
                  omega
                · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
                  omega
              simp only [List.singleton_append, chordTraversalCost]
              omega
      | cons y ys' =>
          have htail := ih (fun z hz => hxs z (by simp [hz]))
          simpa only [List.cons_append, chordTraversalCost, Nat.add_assoc] using
            Nat.add_le_add_left htail (Nat.dist x y)

/-- The two independently greedy partner lists have one combined quadratic
traversal certificate.  The `2L+1` enlargement absorbs both internal `L²`
bounds and the single join jump. -/
theorem twoHalf_traversal_quadratic
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {L : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ L) :
    ChordPartnerQuadraticTraversalBound (2 * L + 1)
      (index.first.partners ++ index.second.partners) := by
  have hfirstUpper : ∀ x ∈ index.first.partners, x ≤ L := by
    intro x hx
    exact le_of_lt (index.first.partner_lt x hx)
  have hsecondUpper : ∀ x ∈ index.second.partners, x ≤ L := by
    intro x hx
    exact le_of_lt (index.second.partner_lt x hx)
  have happ := chordTraversalCost_append_le hfirstUpper hsecondUpper
  have hfirst := index.first.traversal
  have hsecond := index.second.traversal
  unfold ChordPartnerQuadraticTraversalBound at hfirst hsecond ⊢
  calc
    chordTraversalCost (index.first.partners ++ index.second.partners) ≤
        chordTraversalCost index.first.partners +
          chordTraversalCost index.second.partners + L := happ
    _ ≤ L * L + L * L + L := by omega
    _ ≤ (2 * L + 1) * (2 * L + 1) := by nlinarith

/-- **Flatten two charged half-families into the certificate consumed by the
quadratic Proposition 4.14 assembly.**

All geometric data are preserved: every child is one of the original two
half-family children, every original component keeps its charging owner and
radius, and the partner list is the concatenation of the two actual greedy
lists.  The only change is the canonical equivalence
`Fin p ⊕ Fin q ≃ Fin (p+q)` and the harmless `2L+1` traversal scale proved
above. -/
noncomputable def auxiliaryCycleFamilyCertificate_of_twoHalf
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {L : ℕ}
    (index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ L)
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (n : ℕ) (v : G) (word : List (RelLetter G Λ)) (cut : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (C : TwoHalfChargingConfiguration D hsymm b hδ A I lam
      (fun s => (OsinComponents.vertex v word (cut s))⁻¹ *
        OsinComponents.vertex v word (cut (s + 1))))
    (hcountLower : n ≤ (∑ j, A.firstSides j) + ∑ j, A.secondSides j)
    (hcountUpper : (∑ j, A.firstSides j) + ∑ j, A.secondSides j ≤
      n + 6 * ((2 * L + 1) * (2 * L + 1)))
    (hfirstSmall : ∀ j, 5 * A.firstSides j ≤ 4 * n)
    (hsecondSmall : ∀ j, 5 * A.secondSides j ≤ 4 * n) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n v word cut I lam := by
  let e : (Fin index.first.pieceCount ⊕ Fin index.second.pieceCount) ≃
      Fin (index.first.pieceCount + index.second.pieceCount) := finSumFinEquiv
  let side : Fin index.first.pieceCount ⊕ Fin index.second.pieceCount → ℕ :=
    Sum.elim A.firstSides A.secondSides
  let child : ∀ q : Fin index.first.pieceCount ⊕ Fin index.second.pieceCount,
      AuxiliaryCycleCertificate D (b : ℝ) (side q) := fun q => by
    cases q with
    | inl j => exact A.firstChildren j
    | inr j => exact A.secondChildren j
  have hsum :
      (∑ j : Fin (index.first.pieceCount + index.second.pieceCount),
          side (e.symm j)) =
        (∑ j, A.firstSides j) + ∑ j, A.secondSides j := by
    calc
      (∑ j : Fin (index.first.pieceCount + index.second.pieceCount),
          side (e.symm j)) =
          ∑ q : Fin index.first.pieceCount ⊕ Fin index.second.pieceCount,
            side q := Equiv.sum_comp e.symm side
      _ = (∑ j, A.firstSides j) + ∑ j, A.secondSides j := by
        rw [Fintype.sum_sum_type]
        simp [side]
  refine
    { k := index.first.pieceCount + index.second.pieceCount
      childSides := fun j => side (e.symm j)
      chordLength := 2 * L + 1
      partners := index.first.partners ++ index.second.partners
      children := fun j => child (e.symm j)
      owner := fun s => e (C.owner s)
      originalRadius := fun j s => C.radius (e.symm j) s
      original_mem := ?_
      charge := ?_
      count_lower := ?_
      count_upper := ?_
      child_small := ?_
      traversal := twoHalf_traversal_quadratic index }
  · intro s hs
    simpa [e] using C.original_mem s hs
  · intro j
    have hj : j = e (e.symm j) := (e.apply_symm_apply j).symm
    generalize hq : e.symm j = q
    cases q with
    | inl i =>
        have hji : j = e (Sum.inl i) := by simpa [hq] using hj
        subst j
        change
          (∑ s ∈ I,
            if e (C.owner s) = e (Sum.inl i) then
              C.radius (Sum.inl i) s else 0) ≤
            ∑ t ∈ (A.firstChildren i).target,
              (A.firstChildren i).radius D hsymm b hδ t
        simp_rw [e.injective.eq_iff]
        exact C.firstCharge i
    | inr i =>
        have hji : j = e (Sum.inr i) := by simpa [hq] using hj
        subst j
        change
          (∑ s ∈ I,
            if e (C.owner s) = e (Sum.inr i) then
              C.radius (Sum.inr i) s else 0) ≤
            ∑ t ∈ (A.secondChildren i).target,
              (A.secondChildren i).radius D hsymm b hδ t
        simp_rw [e.injective.eq_iff]
        exact C.secondCharge i
  · rw [hsum]
    exact hcountLower
  · intro _
    rw [hsum]
    exact hcountUpper
  · intro j
    generalize hq : e.symm j = q
    cases q with
    | inl i => simpa [side, hq] using hfirstSmall i
    | inr i => simpa [side, hq] using hsecondSmall i

end DGOProposition414
end GGT
end GroupApproximation

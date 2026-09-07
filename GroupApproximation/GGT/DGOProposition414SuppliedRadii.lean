import GroupApproximation.GGT.DGOProposition414DistributedSlots

/-!
# Charging the component surgery with supplied child radii

The geometric factor placement does not depend on the additive least-cost
function. This module adds any valid radii supplied for the actual child
components, with no duplicated charge. General quasi-geodesic child witnesses
can therefore use the existing factorization and slot-disjointness proofs.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

namespace SuppliedChildRadii

variable {D : RelGenSet G Λ} {b : ℝ}
variable {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
variable {chordLength : ℕ}
variable {index : TwoHalfGreedyFamilyIndex I₁ I₂
  pos₁ partner₁ pos₂ partner₂ chordLength}
variable {A : TwoHalfAuxiliaryCycleFamily D b index}

/-- A supplied radius at an optional geometric factor slot. -/
def optionalRadius
    (rho : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) → ℕ → ℕ)
    {lam : Λ} : Option (TwoHalfTargetSlot A lam) → ℕ
  | none => 0
  | some X => rho X.child X.targetIndex

private theorem optionalSpan_mem
    (rho : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) → ℕ → ℕ)
    (hrho : ∀ q t, t ∈ twoHalfChildTarget A q →
      twoHalfChildSpan A q t ∈ D.relBall (twoHalfChildLabel A q t) (rho q t))
    {lam : Λ} (o : Option (TwoHalfTargetSlot A lam)) :
    optionalTargetSlotSpan o ∈ D.relBall lam (optionalRadius rho o) := by
  cases o with
  | none => exact one_mem_relBall D lam 0
  | some X =>
      have h := hrho X.child X.targetIndex X.target_mem
      simpa only [optionalTargetSlotSpan, optionalRadius, X.label_eq] using h

private theorem signedSpan_mem
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (rho : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) → ℕ → ℕ)
    (hrho : ∀ q t, t ∈ twoHalfChildTarget A q →
      twoHalfChildSpan A q t ∈ D.relBall (twoHalfChildLabel A q t) (rho q t))
    {lam : Λ} (inverted : Prop) (o : Option (TwoHalfTargetSlot A lam)) :
    signedOptionalTargetSlotSpan inverted o ∈ D.relBall lam (optionalRadius rho o) := by
  classical
  by_cases h : inverted
  · simp only [signedOptionalTargetSlotSpan, h, ↓reduceIte]
    exact relBall_inv D lam hsymm (optionalSpan_mem rho hrho o)
  · simpa only [signedOptionalTargetSlotSpan, h, ↓reduceIte] using
      optionalSpan_mem rho hrho o

private theorem sum_packet
    (rho : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) → ℕ → ℕ)
    {lam : Λ} (o : Option (TwoHalfTargetSlot A lam)) :
    (∑ q, ∑ t ∈ targetSlotPacket q o, rho q t) = optionalRadius rho o := by
  classical
  cases o with
  | none => simp [targetSlotPacket, optionalRadius]
  | some X =>
      have hterm : ∀ q,
          (∑ t ∈ targetSlotPacket q (some X), rho q t) =
            if q = X.child then rho q X.targetIndex else 0 := by
        intro q
        by_cases h : q = X.child
        · subst q
          simp [targetSlotPacket]
        · simp [targetSlotPacket, h, Ne.symm h]
      simp only [hterm]
      simp [optionalRadius]

private theorem packet_subset
    {lam : Λ}
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (o : Option (TwoHalfTargetSlot A lam)) :
    targetSlotPacket q o ⊆ twoHalfChildTarget A q := by
  classical
  cases o with
  | none => simp [targetSlotPacket]
  | some X =>
      by_cases h : X.child = q
      · subst q
        simpa [targetSlotPacket] using X.target_mem
      · simp [targetSlotPacket, h]

end SuppliedChildRadii

/-- The same distributed geometric factors charge any valid child witnesses.
The only metric operations are multiplication, inversion and monotonicity of
relative balls; no additive cost or quasigeodesic comparison is used. -/
theorem TwoHalfDistributedFactorPlacement.exists_witness_of_suppliedRadii
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index}
    {I : Finset ℕ} {lam : ℕ → Λ} {span : ℕ → G}
    (E : TwoHalfDistributedFactorPlacement D hsymm b hδ A I lam span)
    (rho : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) → ℕ → ℕ)
    (hrho : ∀ q t, t ∈ twoHalfChildTarget A q →
      twoHalfChildSpan A q t ∈ D.relBall (twoHalfChildLabel A q t) (rho q t)) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I, span s ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ ∑ q, ∑ t ∈ twoHalfChildTarget A q, rho q t := by
  classical
  let packet := fun q s =>
    (targetSlotPacket q (E.leftSlot s) ∪ targetSlotPacket q (E.middleSlot s)) ∪
      targetSlotPacket q (E.rightSlot s)
  have hsubset : ∀ q s, packet q s ⊆ twoHalfChildTarget A q := by
    intro q s
    exact Finset.union_subset
      (Finset.union_subset (SuppliedChildRadii.packet_subset q (E.leftSlot s))
        (SuppliedChildRadii.packet_subset q (E.middleSlot s)))
      (SuppliedChildRadii.packet_subset q (E.rightSlot s))
  refine ⟨fun s => ∑ q, ∑ t ∈ packet q s, rho q t, ?_, ?_⟩
  · intro s hs
    have hleft := SuppliedChildRadii.signedSpan_mem hsymm rho hrho
      (E.leftInverted s) (E.leftSlot s)
    have hmiddle := SuppliedChildRadii.signedSpan_mem hsymm rho hrho
      (E.middleInverted s) (E.middleSlot s)
    have hright := SuppliedChildRadii.signedSpan_mem hsymm rho hrho
      (E.rightInverted s) (E.rightSlot s)
    have hproduct := relBall_mul D (lam s) hleft
      (relBall_mul D (lam s) hmiddle hright)
    rw [E.factorization s hs]
    have hradius : (∑ q, ∑ t ∈ packet q s, rho q t) =
        SuppliedChildRadii.optionalRadius rho (E.leftSlot s) +
          SuppliedChildRadii.optionalRadius rho (E.middleSlot s) +
          SuppliedChildRadii.optionalRadius rho (E.rightSlot s) := by
      calc
        (∑ q, ∑ t ∈ packet q s, rho q t) =
            ∑ q, ((∑ t ∈ targetSlotPacket q (E.leftSlot s), rho q t) +
              (∑ t ∈ targetSlotPacket q (E.middleSlot s), rho q t) +
              ∑ t ∈ targetSlotPacket q (E.rightSlot s), rho q t) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_union (E.slots_disjoint q s hs).2,
            Finset.sum_union (E.slots_disjoint q s hs).1]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            SuppliedChildRadii.sum_packet rho (E.leftSlot s),
            SuppliedChildRadii.sum_packet rho (E.middleSlot s),
            SuppliedChildRadii.sum_packet rho (E.rightSlot s)]
    dsimp only
    rw [hradius]
    simpa only [mul_assoc, Nat.add_assoc] using hproduct
  · rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro q _
    have hpair : (I : Set ℕ).PairwiseDisjoint (packet q) := by
      intro s hs t ht hne
      exact E.sources_disjoint q s t hs ht hne
    have hunion : I.biUnion (packet q) ⊆ twoHalfChildTarget A q := by
      intro t ht
      obtain ⟨s, _hs, hts⟩ := Finset.mem_biUnion.mp ht
      exact hsubset q s hts
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hunion (by omega)

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.TwoHalfDistributedFactorPlacement.exists_witness_of_suppliedRadii

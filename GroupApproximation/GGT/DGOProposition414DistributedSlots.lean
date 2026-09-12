import GroupApproximation.GGT.DGOProposition414PacketCharging

/-!
# Distributed target slots for DGO Proposition 4.14

The three factors of a surviving-side or broken-component factorization need
not belong to one auxiliary child.  This module records each factor at its
actual child and target-side index, and turns those distributed geometric
slots into the child-by-source packets used by the charging matrix.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The label carried by a side of one child. -/
def twoHalfChildLabel
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D b index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (t : ℕ) : Λ :=
  match q with
  | Sum.inl j => (A.firstChildren j).label t
  | Sum.inr j => (A.secondChildren j).label t

/-- The group element represented by a side of one child. -/
def twoHalfChildSpan
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D b index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (t : ℕ) : G :=
  match q with
  | Sum.inl j => (A.firstChildren j).sideSpan t
  | Sum.inr j => (A.secondChildren j).sideSpan t

/-- One actual target side, retaining both its child and its local index. -/
structure TwoHalfTargetSlot
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D b index) (lam : Λ) where
  child : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)
  targetIndex : ℕ
  target_mem : targetIndex ∈ twoHalfChildTarget A child
  label_eq : twoHalfChildLabel A child targetIndex = lam

namespace TwoHalfTargetSlot

noncomputable def radius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ}
    (X : TwoHalfTargetSlot A lam) : ℕ :=
  twoHalfChildRadius D hsymm b hδ A X.child X.targetIndex

theorem span_mem_radius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ}
    (X : TwoHalfTargetSlot A lam) :
    twoHalfChildSpan A X.child X.targetIndex ∈
      D.relBall lam (X.radius D hsymm b hδ) := by
  generalize hchild : X.child = q
  cases q with
  | inl j =>
      have ht : X.targetIndex ∈ (A.firstChildren j).target := by
        simpa [twoHalfChildTarget, hchild] using X.target_mem
      have hl : (A.firstChildren j).label X.targetIndex = lam := by
        simpa [twoHalfChildLabel, hchild] using X.label_eq
      have hmem := AuxiliaryCycleCertificate.sideSpan_mem_radius D hsymm b hδ
        (A.firstChildren j) X.targetIndex ht
      simpa only [twoHalfChildSpan, TwoHalfTargetSlot.radius,
        twoHalfChildRadius, hchild, hl] using hmem
  | inr j =>
      have ht : X.targetIndex ∈ (A.secondChildren j).target := by
        simpa [twoHalfChildTarget, hchild] using X.target_mem
      have hl : (A.secondChildren j).label X.targetIndex = lam := by
        simpa [twoHalfChildLabel, hchild] using X.label_eq
      have hmem := AuxiliaryCycleCertificate.sideSpan_mem_radius D hsymm b hδ
        (A.secondChildren j) X.targetIndex ht
      simpa only [twoHalfChildSpan, TwoHalfTargetSlot.radius,
        twoHalfChildRadius, hchild, hl] using hmem

end TwoHalfTargetSlot

/-- The singleton packet occupied by an optional slot in a specified child. -/
def targetSlotPacket
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)) :
    Option (TwoHalfTargetSlot A lam) → Finset ℕ
  | none => ∅
  | some X => if X.child = q then {X.targetIndex} else ∅

/-- An absent geometric factor is the identity. -/
def optionalTargetSlotSpan
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ} :
    Option (TwoHalfTargetSlot A lam) → G
  | none => 1
  | some X => twoHalfChildSpan A X.child X.targetIndex

/-- A geometric factor may be read in the direction opposite to its child
side.  DGO's relative metric is symmetric, so the same target-side charge
bounds either orientation. -/
noncomputable def signedOptionalTargetSlotSpan
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (inverted : Prop) (o : Option (TwoHalfTargetSlot A lam)) : G := by
  classical
  exact if inverted then (optionalTargetSlotSpan o)⁻¹
    else optionalTargetSlotSpan o

/-- An absent geometric factor contributes radius zero. -/
noncomputable def optionalTargetSlotRadius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ} :
    Option (TwoHalfTargetSlot A lam) → ℕ
  | none => 0
  | some X => X.radius D hsymm b hδ

private theorem optionalTargetSlotSpan_mem
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ}
    (o : Option (TwoHalfTargetSlot A lam)) :
    optionalTargetSlotSpan o ∈
      D.relBall lam (optionalTargetSlotRadius D hsymm b hδ o) := by
  cases o with
  | none => simpa [optionalTargetSlotSpan, optionalTargetSlotRadius] using
      one_mem_relBall D lam 0
  | some X => exact X.span_mem_radius D hsymm b hδ

private theorem signedOptionalTargetSlotSpan_mem
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ}
    (inverted : Prop) (o : Option (TwoHalfTargetSlot A lam)) :
    signedOptionalTargetSlotSpan inverted o ∈
      D.relBall lam (optionalTargetSlotRadius D hsymm b hδ o) := by
  classical
  by_cases hinv : inverted
  · simp only [signedOptionalTargetSlotSpan, hinv, ↓reduceIte]
    exact relBall_inv D lam hsymm
      (optionalTargetSlotSpan_mem D hsymm b hδ o)
  · simpa only [signedOptionalTargetSlotSpan, hinv, ↓reduceIte] using
      optionalTargetSlotSpan_mem D hsymm b hδ o

private theorem sum_targetSlotPacket_radius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index} {lam : Λ}
    (o : Option (TwoHalfTargetSlot A lam)) :
    (∑ q, ∑ t ∈ targetSlotPacket q o,
      twoHalfChildRadius D hsymm b hδ A q t) =
        optionalTargetSlotRadius D hsymm b hδ o := by
  classical
  cases o with
  | none => simp [targetSlotPacket, optionalTargetSlotRadius]
  | some X =>
      rw [Fintype.sum_sum_type]
      cases hchild : X.child with
      | inl j =>
          simp only [targetSlotPacket, hchild, Sum.inl.injEq,
            Sum.inl_ne_inr, ↓reduceIte, Finset.sum_empty,
            optionalTargetSlotRadius, TwoHalfTargetSlot.radius]
          rw [Finset.sum_const_zero, add_zero]
          calc
            (∑ x, ∑ t ∈ if j = x then {X.targetIndex} else ∅,
                twoHalfChildRadius D hsymm b hδ A (Sum.inl x) t) =
                ∑ x, if j = x then
                  twoHalfChildRadius D hsymm b hδ A (Sum.inl x)
                    X.targetIndex else 0 := by
              apply Finset.sum_congr rfl
              intro x _hx
              by_cases h : j = x <;> simp [h]
            _ = _ := by
              rw [Finset.sum_ite_eq Finset.univ j,
                if_pos (Finset.mem_univ j)]
      | inr j =>
          simp only [targetSlotPacket, hchild, Sum.inr.injEq,
            Sum.inr_ne_inl, ↓reduceIte, Finset.sum_empty,
            optionalTargetSlotRadius, TwoHalfTargetSlot.radius]
          rw [Finset.sum_const_zero, zero_add]
          calc
            (∑ x, ∑ t ∈ if j = x then {X.targetIndex} else ∅,
                twoHalfChildRadius D hsymm b hδ A (Sum.inr x) t) =
                ∑ x, if j = x then
                  twoHalfChildRadius D hsymm b hδ A (Sum.inr x)
                    X.targetIndex else 0 := by
              apply Finset.sum_congr rfl
              intro x _hx
              by_cases h : j = x <;> simp [h]
            _ = _ := by
              rw [Finset.sum_ite_eq Finset.univ j,
                if_pos (Finset.mem_univ j)]

private theorem targetSlotPacket_subset
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
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

/-- Three factor slots distributed across their actual children.

For a surviving source only the middle slot is present.  For a broken source
the three slots are its entry connector, selected chord-partner component, and
reversed exit connector.  The slots may lie in different children, so the
factorization records the direct product of their actual child-side spans. -/
structure TwoHalfDistributedFactorPlacement
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (I : Finset ℕ) (lam : ℕ → Λ) (span : ℕ → G) where
  leftSlot : ∀ s, Option (TwoHalfTargetSlot A (lam s))
  middleSlot : ∀ s, Option (TwoHalfTargetSlot A (lam s))
  rightSlot : ∀ s, Option (TwoHalfTargetSlot A (lam s))
  leftInverted : ℕ → Prop
  middleInverted : ℕ → Prop
  rightInverted : ℕ → Prop
  factorization : ∀ s ∈ I,
    span s = signedOptionalTargetSlotSpan (leftInverted s) (leftSlot s) *
      signedOptionalTargetSlotSpan (middleInverted s) (middleSlot s) *
      signedOptionalTargetSlotSpan (rightInverted s) (rightSlot s)
  slots_disjoint
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (s : ℕ) : s ∈ I →
    Disjoint (targetSlotPacket q (leftSlot s))
        (targetSlotPacket q (middleSlot s)) ∧
      Disjoint
        (targetSlotPacket q (leftSlot s) ∪
          targetSlotPacket q (middleSlot s))
        (targetSlotPacket q (rightSlot s))
  sources_disjoint
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (s t : ℕ) : s ∈ I → t ∈ I → s ≠ t →
    Disjoint
      ((targetSlotPacket q (leftSlot s) ∪
          targetSlotPacket q (middleSlot s)) ∪
        targetSlotPacket q (rightSlot s))
      ((targetSlotPacket q (leftSlot t) ∪
          targetSlotPacket q (middleSlot t)) ∪
        targetSlotPacket q (rightSlot t))

namespace TwoHalfDistributedFactorPlacement

/-- Distributed geometric factors produce the exact packet placement consumed
by the matrix finite-sum theorem. -/
noncomputable def packets
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index}
    {I : Finset ℕ} {lam : ℕ → Λ} {span : ℕ → G}
    (E : TwoHalfDistributedFactorPlacement D hsymm b hδ A I lam span) :
    TwoHalfDistributedChargePlacement D hsymm b hδ A I lam span := by
  classical
  let packet := fun q s =>
    (targetSlotPacket q (E.leftSlot s) ∪
      targetSlotPacket q (E.middleSlot s)) ∪
        targetSlotPacket q (E.rightSlot s)
  refine
    { packet := packet
      packet_subset := ?_
      packet_disjoint := E.sources_disjoint
      original_mem := ?_ }
  · intro q s _hs
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact targetSlotPacket_subset q (E.leftSlot s)
      · exact targetSlotPacket_subset q (E.middleSlot s)
    · exact targetSlotPacket_subset q (E.rightSlot s)
  · intro s hs
    have hleft := signedOptionalTargetSlotSpan_mem D hsymm b hδ
      (E.leftInverted s) (E.leftSlot s)
    have hmiddle := signedOptionalTargetSlotSpan_mem D hsymm b hδ
      (E.middleInverted s) (E.middleSlot s)
    have hright := signedOptionalTargetSlotSpan_mem D hsymm b hδ
      (E.rightInverted s) (E.rightSlot s)
    have hproduct := relBall_mul D (lam s) hleft
      (relBall_mul D (lam s) hmiddle hright)
    rw [E.factorization s hs]
    have hradius :
        (∑ q, ∑ t ∈ packet q s,
          twoHalfChildRadius D hsymm b hδ A q t) =
          optionalTargetSlotRadius D hsymm b hδ (E.leftSlot s) +
            optionalTargetSlotRadius D hsymm b hδ (E.middleSlot s) +
            optionalTargetSlotRadius D hsymm b hδ (E.rightSlot s) := by
      calc
        (∑ q, ∑ t ∈ packet q s,
            twoHalfChildRadius D hsymm b hδ A q t) =
            ∑ q,
              ((∑ t ∈ targetSlotPacket q (E.leftSlot s),
                  twoHalfChildRadius D hsymm b hδ A q t) +
                (∑ t ∈ targetSlotPacket q (E.middleSlot s),
                  twoHalfChildRadius D hsymm b hδ A q t) +
                ∑ t ∈ targetSlotPacket q (E.rightSlot s),
                  twoHalfChildRadius D hsymm b hδ A q t) := by
              apply Finset.sum_congr rfl
              intro q _hq
              rw [Finset.sum_union (E.slots_disjoint q s hs).2,
                Finset.sum_union (E.slots_disjoint q s hs).1]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            sum_targetSlotPacket_radius D hsymm b hδ (E.leftSlot s),
            sum_targetSlotPacket_radius D hsymm b hδ (E.middleSlot s),
            sum_targetSlotPacket_radius D hsymm b hδ (E.rightSlot s)]
    rw [hradius]
    simpa only [mul_assoc, Nat.add_assoc] using hproduct

/-- Distributed factor geometry directly gives the charging matrix. -/
noncomputable def configuration
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index}
    {I : Finset ℕ} {lam : ℕ → Λ} {span : ℕ → G}
    (E : TwoHalfDistributedFactorPlacement D hsymm b hδ A I lam span) :
    TwoHalfChargingConfiguration D hsymm b hδ A I lam span :=
  E.packets.configuration

end TwoHalfDistributedFactorPlacement

end DGOProposition414
end GGT
end GroupApproximation

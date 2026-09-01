import GroupApproximation.GGT.DGOProposition414TwoHalfProducer

/-!
# Charging by disjoint packets of child sides

A surviving parent component is charged to one child side.  A broken parent
component is charged to the connector--partner--connector packet supplied by
its auxiliary quadrilateral.  This file performs the finite-sum step for both
cases at once: pairwise disjoint packets contained in the owning child's
target automatically produce the two-half charging configuration.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The target set belonging to one child in a two-half family. -/
def twoHalfChildTarget
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D b index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)) :
    Finset ℕ :=
  match q with
  | Sum.inl j => (A.firstChildren j).target
  | Sum.inr j => (A.secondChildren j).target

/-- The label carried by a side of its owning child. -/
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

/-- The group element represented by a side of its owning child. -/
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

/-- The canonical radius of one target side in its owning child. -/
noncomputable def twoHalfChildRadius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (t : ℕ) : ℕ :=
  match q with
  | Sum.inl j => (A.firstChildren j).radius D hsymm b hδ t
  | Sum.inr j => (A.secondChildren j).radius D hsymm b hδ t

/-- An absent connector contributes the identity element. -/
def optionalChildSpan
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D b index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)) :
    Option ℕ → G
  | none => 1
  | some t => twoHalfChildSpan A q t

/-- An absent connector has radius zero. -/
noncomputable def optionalChildRadius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)) :
    Option ℕ → ℕ
  | none => 0
  | some t => twoHalfChildRadius D hsymm b hδ A q t

/-- The singleton target packet represented by an optional slot. -/
def optionTarget : Option ℕ → Finset ℕ
  | none => ∅
  | some t => {t}

/-- Geometric charging data before the routine finite-sum assembly.

Each original side owns a finite packet of distinguished sides of one child.
Packets in the same child are disjoint.  The `original_mem` field is exactly
the survivor or quadrilateral conclusion, with its radius already expressed
as the sum of the packet's actual child radii. -/
structure TwoHalfChargePacketEmbedding
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (I : Finset ℕ) (lam : ℕ → Λ) (span : ℕ → G) where
  owner : ℕ → Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)
  packet : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) →
    ℕ → Finset ℕ
  packet_subset : ∀ s ∈ I,
    packet (owner s) s ⊆ twoHalfChildTarget A (owner s)
  packet_disjoint : ∀ q s, s ∈ I → owner s = q → ∀ t, t ∈ I →
    owner t = q → s ≠ t → Disjoint (packet q s) (packet q t)
  original_mem : ∀ s ∈ I,
    span s ∈ D.relBall (lam s)
      (∑ t ∈ packet (owner s) s,
        twoHalfChildRadius D hsymm b hδ A (owner s) t)

namespace TwoHalfChargePacketEmbedding

/-- Disjoint charge packets assemble into the exact two-half charging
configuration; no separate fibrewise sum estimate is required. -/
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
    (E : TwoHalfChargePacketEmbedding D hsymm b hδ A I lam span) :
    TwoHalfChargingConfiguration D hsymm b hδ A I lam span := by
  classical
  let radius := fun q s =>
    ∑ t ∈ E.packet q s, twoHalfChildRadius D hsymm b hδ A q t
  refine
    { owner := E.owner
      radius := radius
      original_mem := ?_
      firstCharge := ?_
      secondCharge := ?_ }
  · intro s hs
    exact E.original_mem s hs
  · intro j
    let q : Sum (Fin index.first.pieceCount)
        (Fin index.second.pieceCount) := Sum.inl j
    let F := I.filter fun s => E.owner s = q
    have hpair : (F : Set ℕ).PairwiseDisjoint (E.packet q) := by
      intro s hs t ht hne
      have hs' := Finset.mem_filter.mp hs
      have ht' := Finset.mem_filter.mp ht
      exact E.packet_disjoint q s hs'.1 hs'.2 t ht'.1 ht'.2 hne
    have hsubset : F.biUnion (E.packet q) ⊆ twoHalfChildTarget A q := by
      intro t ht
      obtain ⟨s, hs, htPacket⟩ := Finset.mem_biUnion.mp ht
      have hs' := Finset.mem_filter.mp hs
      have hsub := E.packet_subset s hs'.1
      rw [hs'.2] at hsub
      exact hsub htPacket
    change (∑ s ∈ I, if E.owner s = q then radius q s else 0) ≤ _
    rw [show (∑ s ∈ I, if E.owner s = q then radius q s else 0) =
        ∑ s ∈ F, radius q s by
          change _ = ∑ s ∈ I.filter (fun s => E.owner s = q), radius q s
          rw [Finset.sum_filter]]
    change (∑ s ∈ F, ∑ t ∈ E.packet q s,
      twoHalfChildRadius D hsymm b hδ A q t) ≤ _
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
  · intro j
    let q : Sum (Fin index.first.pieceCount)
        (Fin index.second.pieceCount) := Sum.inr j
    let F := I.filter fun s => E.owner s = q
    have hpair : (F : Set ℕ).PairwiseDisjoint (E.packet q) := by
      intro s hs t ht hne
      have hs' := Finset.mem_filter.mp hs
      have ht' := Finset.mem_filter.mp ht
      exact E.packet_disjoint q s hs'.1 hs'.2 t ht'.1 ht'.2 hne
    have hsubset : F.biUnion (E.packet q) ⊆ twoHalfChildTarget A q := by
      intro t ht
      obtain ⟨s, hs, htPacket⟩ := Finset.mem_biUnion.mp ht
      have hs' := Finset.mem_filter.mp hs
      have hsub := E.packet_subset s hs'.1
      rw [hs'.2] at hsub
      exact hsub htPacket
    change (∑ s ∈ I, if E.owner s = q then radius q s else 0) ≤ _
    rw [show (∑ s ∈ I, if E.owner s = q then radius q s else 0) =
        ∑ s ∈ F, radius q s by
          change _ = ∑ s ∈ I.filter (fun s => E.owner s = q), radius q s
          rw [Finset.sum_filter]]
    change (∑ s ∈ F, ∑ t ∈ E.packet q s,
      twoHalfChildRadius D hsymm b hδ A q t) ≤ _
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)

end TwoHalfChargePacketEmbedding

/-! ## The three geometric slots of a DGO quadrilateral -/

/-- The exact geometric input for charging surviving and broken components.

The middle slot is the surviving side or chord partner.  The optional outer
slots are the two connector sides; absence records a trivial connector.  The
factorization is the boundary identity of the component quadrilateral.
Disjointness says that no child target radius is spent twice. -/
structure TwoHalfThreeSlotPlacement
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (I : Finset ℕ) (lam : ℕ → Λ) (span : ℕ → G) where
  owner : ℕ → Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount)
  leftSlot : ℕ → Option ℕ
  middleSlot : ℕ → Option ℕ
  rightSlot : ℕ → Option ℕ
  left_mem : ∀ s ∈ I, ∀ t, leftSlot s = some t →
    t ∈ twoHalfChildTarget A (owner s)
  middle_mem : ∀ s ∈ I, ∀ t, middleSlot s = some t →
    t ∈ twoHalfChildTarget A (owner s)
  right_mem : ∀ s ∈ I, ∀ t, rightSlot s = some t →
    t ∈ twoHalfChildTarget A (owner s)
  left_label : ∀ s ∈ I, ∀ t, leftSlot s = some t →
    twoHalfChildLabel A (owner s) t = lam s
  middle_label : ∀ s ∈ I, ∀ t, middleSlot s = some t →
    twoHalfChildLabel A (owner s) t = lam s
  right_label : ∀ s ∈ I, ∀ t, rightSlot s = some t →
    twoHalfChildLabel A (owner s) t = lam s
  factorization : ∀ s ∈ I,
    span s = optionalChildSpan A (owner s) (leftSlot s) *
      optionalChildSpan A (owner s) (middleSlot s) *
      (optionalChildSpan A (owner s) (rightSlot s))⁻¹
  slots_disjoint : ∀ s ∈ I,
    Disjoint (optionTarget (leftSlot s)) (optionTarget (middleSlot s)) ∧
      Disjoint (optionTarget (leftSlot s) ∪ optionTarget (middleSlot s))
        (optionTarget (rightSlot s))
  packet_disjoint : ∀ q s, s ∈ I → owner s = q → ∀ t, t ∈ I →
    owner t = q → s ≠ t →
      Disjoint
        ((optionTarget (leftSlot s) ∪ optionTarget (middleSlot s)) ∪
          optionTarget (rightSlot s))
        ((optionTarget (leftSlot t) ∪ optionTarget (middleSlot t)) ∪
          optionTarget (rightSlot t))

namespace TwoHalfThreeSlotPlacement

private theorem optionTarget_subset {o : Option ℕ} {T : Finset ℕ}
    (h : ∀ t, o = some t → t ∈ T) : optionTarget o ⊆ T := by
  cases o with
  | none => simp [optionTarget]
  | some t => simpa [optionTarget] using h t rfl

private theorem optionalChildSpan_mem
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index}
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (lam : Λ) (o : Option ℕ)
    (hmem : ∀ t, o = some t → t ∈ twoHalfChildTarget A q)
    (hlabel : ∀ t, o = some t → twoHalfChildLabel A q t = lam) :
    optionalChildSpan A q o ∈ D.relBall lam
      (optionalChildRadius D hsymm b hδ A q o) := by
  cases o with
  | none =>
      simpa [optionalChildSpan, optionalChildRadius] using
        one_mem_relBall D lam 0
  | some t =>
      have ht := hmem t rfl
      have hl := hlabel t rfl
      cases q with
      | inl j =>
          change t ∈ (A.firstChildren j).target at ht
          change (A.firstChildren j).label t = lam at hl
          have hc := AuxiliaryCycleCertificate.sideSpan_mem_radius D hsymm b hδ
            (A.firstChildren j) t ht
          rw [hl] at hc
          simpa [optionalChildSpan, optionalChildRadius, twoHalfChildSpan,
            twoHalfChildRadius] using hc
      | inr j =>
          change t ∈ (A.secondChildren j).target at ht
          change (A.secondChildren j).label t = lam at hl
          have hc := AuxiliaryCycleCertificate.sideSpan_mem_radius D hsymm b hδ
            (A.secondChildren j) t ht
          rw [hl] at hc
          simpa [optionalChildSpan, optionalChildRadius, twoHalfChildSpan,
            twoHalfChildRadius] using hc

private theorem sum_optionTarget_radius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ b : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (o : Option ℕ) :
    (∑ t ∈ optionTarget o, twoHalfChildRadius D hsymm b hδ A q t) =
      optionalChildRadius D hsymm b hδ A q o := by
  cases o <;> simp [optionTarget, optionalChildRadius]

/-- The three geometric slots produce the disjoint packet placement consumed
by the finite charging theorem. -/
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
    (E : TwoHalfThreeSlotPlacement D hsymm b hδ A I lam span) :
    TwoHalfChargePacketEmbedding D hsymm b hδ A I lam span where
  owner := E.owner
  packet := fun _q s =>
    (optionTarget (E.leftSlot s) ∪ optionTarget (E.middleSlot s)) ∪
      optionTarget (E.rightSlot s)
  packet_subset := by
    intro s hs
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact optionTarget_subset (E.left_mem s hs)
      · exact optionTarget_subset (E.middle_mem s hs)
    · exact optionTarget_subset (E.right_mem s hs)
  packet_disjoint := E.packet_disjoint
  original_mem := by
    intro s hs
    let q := E.owner s
    have hleft := optionalChildSpan_mem (D := D) (hsymm := hsymm) (hδ := hδ)
      q (lam s) (E.leftSlot s)
      (E.left_mem s hs) (E.left_label s hs)
    have hmiddle := optionalChildSpan_mem (D := D) (hsymm := hsymm) (hδ := hδ)
      q (lam s) (E.middleSlot s)
      (E.middle_mem s hs) (E.middle_label s hs)
    have hright := optionalChildSpan_mem (D := D) (hsymm := hsymm) (hδ := hδ)
      q (lam s) (E.rightSlot s)
      (E.right_mem s hs) (E.right_label s hs)
    have hrightInv := relBall_inv D (lam s) hsymm hright
    have hmiddleRight := relBall_mul D (lam s) hmiddle hrightInv
    have hquad' := relBall_mul D (lam s) hleft hmiddleRight
    have hquad :
        optionalChildSpan A q (E.leftSlot s) *
            optionalChildSpan A q (E.middleSlot s) *
            (optionalChildSpan A q (E.rightSlot s))⁻¹ ∈
          D.relBall (lam s)
            (optionalChildRadius D hsymm b hδ A q (E.leftSlot s) +
              optionalChildRadius D hsymm b hδ A q (E.middleSlot s) +
              optionalChildRadius D hsymm b hδ A q (E.rightSlot s)) := by
      simpa only [mul_assoc, Nat.add_assoc] using hquad'
    rw [E.factorization s hs]
    have hslots := E.slots_disjoint s hs
    have hradius :
        (∑ t ∈ (optionTarget (E.leftSlot s) ∪
              optionTarget (E.middleSlot s)) ∪ optionTarget (E.rightSlot s),
            twoHalfChildRadius D hsymm b hδ A q t) =
          optionalChildRadius D hsymm b hδ A q (E.leftSlot s) +
            optionalChildRadius D hsymm b hδ A q (E.middleSlot s) +
            optionalChildRadius D hsymm b hδ A q (E.rightSlot s) := by
      rw [Finset.sum_union hslots.2, Finset.sum_union hslots.1,
        sum_optionTarget_radius D hsymm hδ A q,
        sum_optionTarget_radius D hsymm hδ A q,
        sum_optionTarget_radius D hsymm hδ A q]
    rw [hradius]
    exact hquad

/-- Three-slot geometry directly gives the final two-half charging
configuration. -/
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
    (E : TwoHalfThreeSlotPlacement D hsymm b hδ A I lam span) :
    TwoHalfChargingConfiguration D hsymm b hδ A I lam span :=
  E.packets.configuration

end TwoHalfThreeSlotPlacement

end DGOProposition414
end GGT
end GroupApproximation

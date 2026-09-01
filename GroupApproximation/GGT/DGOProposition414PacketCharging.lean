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

end DGOProposition414
end GGT
end GroupApproximation

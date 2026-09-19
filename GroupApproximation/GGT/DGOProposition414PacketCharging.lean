import GroupApproximation.GGT.DGOProposition414TwoHalfProducer

/-!
# Distributed charging by child-side packets

A broken component's two connectors generally lie in adjacent gap children.
Thus charging is a child-by-source matrix, not a single-owner assignment.
This file proves that pairwise disjoint target packets in each child assemble
into the exact two-half matrix charging configuration.
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

/-- The canonical radius of one target side in its child. -/
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

/-- Actual distributed geometric charge packets.

For each original source `s`, `packet q s` lists the target sides used in
child `q`.  Packets belonging to distinct sources are disjoint inside every
child, which is precisely the non-duplication needed for the charge bound. -/
structure TwoHalfDistributedChargePlacement
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index)
    (I : Finset ℕ) (lam : ℕ → Λ) (span : ℕ → G) where
  packet : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount) →
    ℕ → Finset ℕ
  packet_subset
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (s : ℕ) : s ∈ I → packet q s ⊆ twoHalfChildTarget A q
  packet_disjoint
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (s t : ℕ) : s ∈ I → t ∈ I → s ≠ t →
      Disjoint (packet q s) (packet q t)
  original_mem : ∀ s ∈ I,
    span s ∈ D.relBall (lam s)
      (∑ q, ∑ t ∈ packet q s,
        twoHalfChildRadius D hsymm b hδ A q t)

namespace TwoHalfDistributedChargePlacement

/-- Distributed packets assemble into matrix charging; no owner choice and no
separate finite-sum estimate remain. -/
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
    (E : TwoHalfDistributedChargePlacement D hsymm b hδ A I lam span) :
    TwoHalfChargingConfiguration D hsymm b hδ A I lam span := by
  classical
  let radius := fun q s =>
    ∑ t ∈ E.packet q s, twoHalfChildRadius D hsymm b hδ A q t
  refine
    { radius := radius
      original_mem := E.original_mem
      firstCharge := ?_
      secondCharge := ?_ }
  · intro j
    let q : Sum (Fin index.first.pieceCount)
        (Fin index.second.pieceCount) := Sum.inl j
    have hpair : (I : Set ℕ).PairwiseDisjoint (E.packet q) := by
      intro s hs t ht hne
      exact E.packet_disjoint q s t hs ht hne
    have hsubset : I.biUnion (E.packet q) ⊆ twoHalfChildTarget A q := by
      intro t ht
      obtain ⟨s, hs, htPacket⟩ := Finset.mem_biUnion.mp ht
      exact E.packet_subset q s hs htPacket
    change (∑ s ∈ I, radius q s) ≤ _
    change (∑ s ∈ I, ∑ t ∈ E.packet q s,
      twoHalfChildRadius D hsymm b hδ A q t) ≤ _
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
  · intro j
    let q : Sum (Fin index.first.pieceCount)
        (Fin index.second.pieceCount) := Sum.inr j
    have hpair : (I : Set ℕ).PairwiseDisjoint (E.packet q) := by
      intro s hs t ht hne
      exact E.packet_disjoint q s t hs ht hne
    have hsubset : I.biUnion (E.packet q) ⊆ twoHalfChildTarget A q := by
      intro t ht
      obtain ⟨s, hs, htPacket⟩ := Finset.mem_biUnion.mp ht
      exact E.packet_subset q s hs htPacket
    change (∑ s ∈ I, radius q s) ≤ _
    change (∑ s ∈ I, ∑ t ∈ E.packet q s,
      twoHalfChildRadius D hsymm b hδ A q t) ≤ _
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)

end TwoHalfDistributedChargePlacement

end DGOProposition414
end GGT
end GroupApproximation

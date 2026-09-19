import GroupApproximation.GGT.DGOProposition414FactorPlacementAux

/-!
# Distributed factor placement for balanced gap children

For a fixed pair of complete gap component families, this module packages the
three factor slots of every parent target into
`TwoHalfDistributedFactorPlacement`.  The factorization and same-source slot
separation are the component surgery identities of Dahmani--Guirardel--Osin
Proposition 4.14.  Distinct-source separation is reproved from the four origin
classifications, so this constructor is independent of any later aggregate
module.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## Separation between different parent sources -/

/-- Packets belonging to different parent targets are disjoint.  The origin
coordinates identify both the child and local target coordinate, and the
coordinate-separation lemmas recover the parent source. -/
theorem distributedSources_disjoint_local
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (q : Sum (Fin B.brokenAssignment.index.first.pieceCount)
      (Fin B.brokenAssignment.index.second.pieceCount))
    (hs : s ∈ P.target) (ht : t ∈ P.target) (hne : s ≠ t) :
    Disjoint (B.distributedPacket C q s) (B.distributedPacket C q t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  cases q with
  | inl j =>
      obtain ⟨K, hKchild, hKindex⟩ :=
        B.distributedPacket_first_origin C hs j hxs
      obtain ⟨L, hLchild, hLindex⟩ :=
        B.distributedPacket_first_origin C ht j hxt
      have hchild : K.child = L.child := hKchild.trans hLchild.symm
      have hindex : K.targetIndex = L.targetIndex :=
        hKindex.trans hLindex.symm
      exact hne (FirstChildSlotKind.source_eq_of_same_coordinate K L
        hchild hindex)
  | inr j =>
      obtain ⟨K, hKchild, hKindex⟩ :=
        B.distributedPacket_second_origin C hs j hxs
      obtain ⟨L, hLchild, hLindex⟩ :=
        B.distributedPacket_second_origin C ht j hxt
      have hchild : K.child = L.child := hKchild.trans hLchild.symm
      have hindex : K.targetIndex = L.targetIndex :=
        hKindex.trans hLindex.symm
      exact hne (SecondChildSlotKind.source_eq_of_same_coordinate K L
        hchild hindex)

/-! ## The completed distributed factor geometry -/

/-- The three canonical factors form a complete distributed placement on both
child families. -/
noncomputable def distributedFactorPlacement
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) :
    TwoHalfDistributedFactorPlacement D hsymm b hδ
      (B.gapIntervalsOfConfigurations C).toPathInput.family
      P.target P.label P.span where
  leftSlot := fun s => B.distributedLeftSlot C s
  middleSlot := fun s => B.distributedMiddleSlot C s
  rightSlot := fun s => B.distributedRightSlot C s
  leftInverted := fun _ => False
  middleInverted := fun s => B.distributedMiddleInverted s
  rightInverted := fun _ => False
  factorization := fun _s hs => B.distributedSlots_factorization C hs
  slots_disjoint := fun q _s hs => B.distributedSlots_disjoint C q hs
  sources_disjoint := fun q _s _t hs ht hne =>
    B.distributedSources_disjoint_local C q hs ht hne

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation

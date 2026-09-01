import GroupApproximation.GGT.DGOProposition414DistributedSlots
import GroupApproximation.GGT.DGOProposition414EntryOwner

/-!
# Actual target coordinates in the two-half interval family

This module exposes the local child indices used by component surgery.  A
left connector letter has index `r`; an inherited/local or chord target keeps
its stored local index; and a right connector letter has index
`left.length + arcSides + r`.  The constructors retain the child tag, so the
two connectors of one broken source may be placed in adjacent children.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace TwoHalfPathInput

/-- A target of a first-half child, with its actual local index. -/
def firstTargetSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.pieceCount) (t : ℕ) (lam : Λ)
    (ht : t ∈ (P.first j).certificate.target)
    (hl : (P.first j).certificate.label t = lam) :
    TwoHalfTargetSlot P.family lam where
  child := Sum.inl j
  targetIndex := t
  target_mem := ht
  label_eq := hl

/-- A target of a wrapped-half child, with its actual local index. -/
def secondTargetSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.pieceCount) (t : ℕ) (lam : Λ)
    (ht : t ∈ (P.second j).certificate.target)
    (hl : (P.second j).certificate.label t = lam) :
    TwoHalfTargetSlot P.family lam where
  child := Sum.inr j
  targetIndex := t
  target_mem := ht
  label_eq := hl

/-- A stored local target (in particular, a selected chord component) in a
first-half interval gives an actual child slot. -/
def firstLocalTargetSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.pieceCount) (t : ℕ) (lam : Λ)
    (ht : t ∈ (P.first j).localTarget)
    (hl : (P.first j).label t = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.firstTargetSlot j t lam (by
    exact Finset.mem_union.mpr (Or.inl ht)) hl

/-- A stored local target in a wrapped-half interval gives an actual child
slot. -/
def secondLocalTargetSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.pieceCount) (t : ℕ) (lam : Λ)
    (ht : t ∈ (P.second j).localTarget)
    (hl : (P.second j).label t = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.secondTargetSlot j t lam (by
    exact Finset.mem_union.mpr (Or.inl ht)) hl

/-- The `r`-th left connector letter of a first-half interval is target side
`r` of that same child. -/
def firstLeftConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.pieceCount) (r : ℕ)
    (hr : r < (P.first j).left.length) (lam : Λ)
    (hl : (P.first j).label r = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.firstTargetSlot j r lam (by
    exact Finset.mem_union.mpr (Or.inr
      (mem_auxiliaryCycleConnectorTarget_left _ _ _ r hr))) hl

/-- The `r`-th right connector letter of a first-half interval is target side
`left.length + arcSides + r` of that same child. -/
def firstRightConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.pieceCount) (r : ℕ)
    (hr : r < (P.first j).right.length) (lam : Λ)
    (hl : (P.first j).label
      ((P.first j).left.length + (P.first j).arcSides + r) = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.firstTargetSlot j
    ((P.first j).left.length + (P.first j).arcSides + r) lam (by
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right _ _ _ r hr))) hl

/-- The `r`-th left connector letter of a wrapped-half interval is target side
`r` of that same child. -/
def secondLeftConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.pieceCount) (r : ℕ)
    (hr : r < (P.second j).left.length) (lam : Λ)
    (hl : (P.second j).label r = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.secondTargetSlot j r lam (by
    exact Finset.mem_union.mpr (Or.inr
      (mem_auxiliaryCycleConnectorTarget_left _ _ _ r hr))) hl

/-- The `r`-th right connector letter of a wrapped-half interval is target
side `left.length + arcSides + r` of that same child. -/
def secondRightConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.pieceCount) (r : ℕ)
    (hr : r < (P.second j).right.length) (lam : Λ)
    (hl : (P.second j).label
      ((P.second j).left.length + (P.second j).arcSides + r) = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.secondTargetSlot j
    ((P.second j).left.length + (P.second j).arcSides + r) lam (by
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right _ _ _ r hr))) hl

/-! ## The adjacent children of one broken-source entry -/

/-- A first-half source entry's start connector is on the right of the gap
child immediately before that source. -/
def firstEntryStartConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.sources.length) (r : ℕ)
    (hr : r < (P.first (HalfEntry.entryChild index.first j)).right.length)
    (lam : Λ)
    (hl : (P.first (HalfEntry.entryChild index.first j)).label
      ((P.first (HalfEntry.entryChild index.first j)).left.length +
        (P.first (HalfEntry.entryChild index.first j)).arcSides + r) = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.firstRightConnectorSlot (HalfEntry.entryChild index.first j) r hr lam hl

/-- A first-half source entry's end connector is on the left of the adjacent
gap child immediately after that source. -/
def firstEntryEndConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.first.sources.length) (r : ℕ)
    (hr : r < (P.first (HalfEntry.exitChild index.first j)).left.length)
    (lam : Λ)
    (hl : (P.first (HalfEntry.exitChild index.first j)).label r = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.firstLeftConnectorSlot (HalfEntry.exitChild index.first j) r hr lam hl

/-- A wrapped-half source entry's start connector is on the right of the gap
child immediately before that source. -/
def secondEntryStartConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.sources.length) (r : ℕ)
    (hr : r < (P.second (HalfEntry.entryChild index.second j)).right.length)
    (lam : Λ)
    (hl : (P.second (HalfEntry.entryChild index.second j)).label
      ((P.second (HalfEntry.entryChild index.second j)).left.length +
        (P.second (HalfEntry.entryChild index.second j)).arcSides + r) = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.secondRightConnectorSlot (HalfEntry.entryChild index.second j) r hr lam hl

/-- A wrapped-half source entry's end connector is on the left of the
adjacent gap child immediately after that source. -/
def secondEntryEndConnectorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {b : ℕ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    (P : TwoHalfPathInput D hsymm b index)
    (j : Fin index.second.sources.length) (r : ℕ)
    (hr : r < (P.second (HalfEntry.exitChild index.second j)).left.length)
    (lam : Λ)
    (hl : (P.second (HalfEntry.exitChild index.second j)).label r = lam) :
    TwoHalfTargetSlot P.family lam :=
  P.secondLeftConnectorSlot (HalfEntry.exitChild index.second j) r hr lam hl

end TwoHalfPathInput

end DGOProposition414
end GGT
end GroupApproximation

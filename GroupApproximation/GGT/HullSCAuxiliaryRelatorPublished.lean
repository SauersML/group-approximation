import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactPublished

/-!
# Hull's §6 relator in the selected auxiliary family

The quotient lane preserves one pair for the suitable subgroup `N` and one
pair for every prescribed suitable subgroup.  Hull's alternating relator uses
only the distinguished `N` pair, but its small-cancellation estimates must be
made in the relative graph of the whole selected family.  This file begins
that reduction by focusing the full family at the `N` pair: all other
peripherals are moved into the base.  The resulting Bool-indexed relative
generating set has exactly the same relative alphabet, and its relative balls
at the two retained peripherals embed in those of the full family.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

namespace AuxiliaryPeripheralFamily

variable {G : Type u} [Group G] {A : HullGeneratingSet G}
  {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}

/-- The peripherals belonging to the prescribed subgroups, excluding the
distinguished pair belonging to `N`. -/
def extraPeripheralSet (D : AuxiliaryPeripheralFamily A N S) : Set G :=
  ⋃ j : Fin k, ⋃ b : Bool, (D.rel.fam (some j, b) : Set G)

/-- The full relative base with every non-`N` peripheral moved into it. -/
def focusNBase (D : AuxiliaryPeripheralFamily A N S) : Set G :=
  D.rel.base ∪ D.extraPeripheralSet

private theorem focusN_union_eq (D : AuxiliaryPeripheralFamily A N S) :
    D.focusNBase ∪ ⋃ b : Bool, (D.rel.fam (none, b) : Set G) =
      D.rel.base ∪
        ⋃ i : AuxiliaryPeripheralIndex k, (D.rel.fam i : Set G) := by
  ext x
  constructor
  · rintro ((hx | hx) | hx)
    · exact Or.inl hx
    · obtain ⟨j, b, hxb⟩ := Set.mem_iUnion₂.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨(some j, b), hxb⟩)
    · obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨(none, b), hxb⟩)
  · rintro (hx | hx)
    · exact Or.inl (Or.inl hx)
    · obtain ⟨⟨tag, b⟩, hxb⟩ := Set.mem_iUnion.mp hx
      cases tag with
      | none => exact Or.inr (Set.mem_iUnion.mpr ⟨b, hxb⟩)
      | some j => exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, b, hxb⟩))

/-- The Bool-indexed view of the distinguished pair, read in the full relative
alphabet by moving every other peripheral into the base. -/
def focusNRel (D : AuxiliaryPeripheralFamily A N S) : GGT.RelGenSet G Bool where
  base := D.focusNBase
  fam b := D.rel.fam (none, b)
  symmetricGenerating := by
    rw [focusN_union_eq]
    exact D.rel.symmetricGenerating

theorem focusNRel_alphabet (D : AuxiliaryPeripheralFamily A N S) :
    D.focusNRel.alphabet = D.rel.alphabet := by
  apply GGT.OsinComponents.alphabet_eq_of_carrier_eq
  exact focusN_union_eq D

/-- Read a focused letter in the full auxiliary family.  An extra-peripheral
base letter is restored to one of its original component labels. -/
noncomputable def fullLetterOfFocus (D : AuxiliaryPeripheralFamily A N S) :
    GGT.RelLetter G Bool → GGT.RelLetter G (AuxiliaryPeripheralIndex k) := by
  classical
  intro a
  cases a with
  | base x =>
      by_cases hx : x ∈ D.rel.base
      · exact GGT.RelLetter.base x
      · by_cases he : x ∈ D.extraPeripheralSet
        · let j := Classical.choose (Set.mem_iUnion.mp he)
          let hj := Classical.choose_spec (Set.mem_iUnion.mp he)
          let b := Classical.choose (Set.mem_iUnion.mp hj)
          exact GGT.RelLetter.comp (some j, b) x
        · exact GGT.RelLetter.base x
  | comp b h => exact GGT.RelLetter.comp (none, b) h

@[simp] theorem val_fullLetterOfFocus (D : AuxiliaryPeripheralFamily A N S)
    (a : GGT.RelLetter G Bool) : (D.fullLetterOfFocus a).val = a.val := by
  cases a with
  | base x =>
      by_cases hx : x ∈ D.rel.base
      · (simp [fullLetterOfFocus, hx]; rfl)
      · by_cases he : x ∈ D.extraPeripheralSet
        · (simp [fullLetterOfFocus, hx, he]; rfl)
        · (simp [fullLetterOfFocus, hx, he]; rfl)
  | comp b h => rfl

theorem isCompOf_fullLetterOfFocus (D : AuxiliaryPeripheralFamily A N S)
    (b : Bool) (a : GGT.RelLetter G Bool) :
    GGT.RelLetter.IsCompOf (none, b) (D.fullLetterOfFocus a) ↔
      GGT.RelLetter.IsCompOf b a := by
  cases a with
  | base x =>
      by_cases hx : x ∈ D.rel.base
      · simp [fullLetterOfFocus, hx, GGT.RelLetter.IsCompOf]
      · by_cases he : x ∈ D.extraPeripheralSet
        · simp [fullLetterOfFocus, hx, he, GGT.RelLetter.IsCompOf]
        · simp [fullLetterOfFocus, hx, he, GGT.RelLetter.IsCompOf]
  | comp c h => simp [fullLetterOfFocus, GGT.RelLetter.IsCompOf]

theorem isLetter_fullLetterOfFocus (D : AuxiliaryPeripheralFamily A N S)
    {a : GGT.RelLetter G Bool} (ha : D.focusNRel.IsLetter a) :
    D.rel.IsLetter (D.fullLetterOfFocus a) := by
  cases a with
  | base x =>
      change x ∈ D.focusNBase at ha
      rcases ha with hx | he
      · rw [show D.fullLetterOfFocus (GGT.RelLetter.base x) =
            GGT.RelLetter.base x by simp [fullLetterOfFocus, hx]]
        exact hx
      · by_cases hx : x ∈ D.rel.base
        · rw [show D.fullLetterOfFocus (GGT.RelLetter.base x) =
              GGT.RelLetter.base x by simp [fullLetterOfFocus, hx]]
          exact hx
        · simp only [fullLetterOfFocus, hx, he]
          let j := Classical.choose (Set.mem_iUnion.mp he)
          have hj := Classical.choose_spec (Set.mem_iUnion.mp he)
          let b := Classical.choose (Set.mem_iUnion.mp hj)
          have hb := Classical.choose_spec (Set.mem_iUnion.mp hj)
          exact hb
  | comp b h => exact ha

theorem listVal_map_fullLetterOfFocus (D : AuxiliaryPeripheralFamily A N S)
    (w : List (GGT.RelLetter G Bool)) :
    GGT.RelLetter.listVal (w.map D.fullLetterOfFocus) =
      GGT.RelLetter.listVal w := by
  show ((w.map D.fullLetterOfFocus).map GGT.RelLetter.val).prod = _
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun a _ => D.val_fullLetterOfFocus a)

theorem avoidsFrom_map_fullLetterOfFocus
    (D : AuxiliaryPeripheralFamily A N S) (b : Bool) :
    ∀ (w : List (GGT.RelLetter G Bool)) (v : G),
      GGT.AvoidsFrom D.focusNRel.fam b w v →
        GGT.AvoidsFrom D.rel.fam (none, b) (w.map D.fullLetterOfFocus) v := by
  intro w
  induction w with
  | nil => simp [GGT.AvoidsFrom]
  | cons a w ih =>
      intro v h
      constructor
      · rintro ⟨hcomp, hv⟩
        apply h.1
        exact ⟨(D.isCompOf_fullLetterOfFocus b a).mp hcomp, hv⟩
      · simpa [D.val_fullLetterOfFocus a] using ih (v * a.val) h.2

/-- A focused relative ball injects into the corresponding relative ball of
the full family.  Consequently local finiteness of the full family implies
local finiteness of the focused pair. -/
theorem focusNRel_relBall_subset (D : AuxiliaryPeripheralFamily A N S)
    (b : Bool) (n : ℕ) :
    D.focusNRel.relBall b n ⊆ D.rel.relBall (none, b) n := by
  rintro h ⟨hh, w, hw, hval, hav, hlen⟩
  refine ⟨hh, w.map D.fullLetterOfFocus, ?_, ?_, ?_, by simpa using hlen⟩
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact D.isLetter_fullLetterOfFocus (hw c hc)
  · rw [D.listVal_map_fullLetterOfFocus, hval]
  · exact D.avoidsFrom_map_fullLetterOfFocus b w 1 hav

theorem focusNRel_isHyperbolicallyEmbedded
    (D : AuxiliaryPeripheralFamily A N S) :
    D.focusNRel.IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [D.focusNRel_alphabet]
    exact D.embedded.hyperbolic
  · intro b n
    exact (D.embedded.locallyFinite (none, b) n).subset
      (D.focusNRel_relBall_subset b n)

/-- The focused full-family pair as the existing §6 exact-design core. -/
def focusNCore (D : AuxiliaryPeripheralFamily A N S) :
    HypEmbeddedCore₂ A N where
  rel := D.focusNRel
  base_le := D.base_le.trans Set.subset_union_left
  base_inv := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (D.base_inv x hx)
    · obtain ⟨j, b, hxb⟩ := Set.mem_iUnion₂.mp hx
      exact Or.inr (Set.mem_iUnion₂.mpr
        ⟨j, b, (D.rel.fam (some j, b)).inv_mem hxb⟩)
  H := D.cores.coreN.H
  fam_eq := by
    funext b
    exact D.fam_eq (none, b)
  le := D.cores.coreN.le
  embedded := D.focusNRel_isHyperbolicallyEmbedded
  lox := D.cores.coreN.lox
  lox_mem := D.cores.coreN.lox_mem
  lox_isLoxodromic := D.cores.coreN.lox_isLoxodromic
  disjoint := D.cores.coreN.disjoint

end AuxiliaryPeripheralFamily

end HullSC
end GroupApproximation

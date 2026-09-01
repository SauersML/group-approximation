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

/-- Read a full-family letter in the focused pair.  Letters of prescribed
subgroup peripherals become base letters; the distinguished `N` components
retain their Bool label. -/
def focusLetterOfFull (_D : AuxiliaryPeripheralFamily A N S) :
    GGT.RelLetter G (AuxiliaryPeripheralIndex k) → GGT.RelLetter G Bool
  | GGT.RelLetter.base x => GGT.RelLetter.base x
  | GGT.RelLetter.comp (none, b) h => GGT.RelLetter.comp b h
  | GGT.RelLetter.comp (some _, _) h => GGT.RelLetter.base h

@[simp] theorem val_focusLetterOfFull (D : AuxiliaryPeripheralFamily A N S)
    (a : GGT.RelLetter G (AuxiliaryPeripheralIndex k)) :
    (D.focusLetterOfFull a).val = a.val := by
  cases a with
  | base x => rfl
  | comp i h =>
      rcases i with ⟨tag, b⟩
      cases tag <;> rfl

theorem isCompOf_focusLetterOfFull (D : AuxiliaryPeripheralFamily A N S)
    (b : Bool) (a : GGT.RelLetter G (AuxiliaryPeripheralIndex k)) :
    GGT.RelLetter.IsCompOf b (D.focusLetterOfFull a) ↔
      GGT.RelLetter.IsCompOf (none, b) a := by
  cases a with
  | base x => simp [focusLetterOfFull, GGT.RelLetter.IsCompOf]
  | comp i h =>
      rcases i with ⟨tag, c⟩
      cases tag <;> simp [focusLetterOfFull, GGT.RelLetter.IsCompOf]

theorem isLetter_focusLetterOfFull (D : AuxiliaryPeripheralFamily A N S)
    {a : GGT.RelLetter G (AuxiliaryPeripheralIndex k)}
    (ha : D.rel.IsLetter a) : D.focusNRel.IsLetter (D.focusLetterOfFull a) := by
  cases a with
  | base x => exact Or.inl ha
  | comp i h =>
      rcases i with ⟨tag, b⟩
      cases tag with
      | none => exact ha
      | some j => exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, b, ha⟩)

theorem listVal_map_focusLetterOfFull (D : AuxiliaryPeripheralFamily A N S)
    (w : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) :
    GGT.RelLetter.listVal (w.map D.focusLetterOfFull) =
      GGT.RelLetter.listVal w := by
  show ((w.map D.focusLetterOfFull).map GGT.RelLetter.val).prod = _
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun a _ => D.val_focusLetterOfFull a)

theorem listVal_take_map_focusLetterOfFull
    (D : AuxiliaryPeripheralFamily A N S)
    (w : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) (i : ℕ) :
    GGT.RelLetter.listVal ((w.map D.focusLetterOfFull).take i) =
      GGT.RelLetter.listVal (w.take i) := by
  have htake : (w.map D.focusLetterOfFull).take i =
      (w.take i).map D.focusLetterOfFull := by
    induction w generalizing i with
    | nil => cases i <;> rfl
    | cons a w ih =>
        cases i with
        | zero => rfl
        | succ i =>
            change D.focusLetterOfFull a :: (w.map D.focusLetterOfFull).take i =
              D.focusLetterOfFull a :: (w.take i).map D.focusLetterOfFull
            exact congrArg (D.focusLetterOfFull a :: ·) (ih i)
  rw [htake, D.listVal_map_focusLetterOfFull]

theorem avoidsFrom_map_focusLetterOfFull
    (D : AuxiliaryPeripheralFamily A N S) (b : Bool) :
    ∀ (w : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) (v : G),
      GGT.AvoidsFrom D.rel.fam (none, b) w v →
        GGT.AvoidsFrom D.focusNRel.fam b (w.map D.focusLetterOfFull) v := by
  intro w
  induction w with
  | nil => simp [GGT.AvoidsFrom]
  | cons a w ih =>
      intro v h
      constructor
      · rintro ⟨hcomp, hv⟩
        apply h.1
        exact ⟨(D.isCompOf_focusLetterOfFull b a).mp hcomp, hv⟩
      · simpa [D.val_focusLetterOfFull a] using ih (v * a.val) h.2

theorem relBall_subset_focusNRel (D : AuxiliaryPeripheralFamily A N S)
    (b : Bool) (n : ℕ) :
    D.rel.relBall (none, b) n ⊆ D.focusNRel.relBall b n := by
  rintro h ⟨hh, w, hw, hval, hav, hlen⟩
  refine ⟨hh, w.map D.focusLetterOfFull, ?_, ?_, ?_, by simpa using hlen⟩
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact D.isLetter_focusLetterOfFull (hw c hc)
  · rw [D.listVal_map_focusLetterOfFull, hval]
  · exact D.avoidsFrom_map_focusLetterOfFull b w 1 hav

theorem focusNRel_relBall_eq (D : AuxiliaryPeripheralFamily A N S)
    (b : Bool) (n : ℕ) :
    D.focusNRel.relBall b n = D.rel.relBall (none, b) n :=
  Set.Subset.antisymm (D.focusNRel_relBall_subset b n)
    (D.relBall_subset_focusNRel b n)

/-- The literal inclusion of the distinguished Bool pair into the full
auxiliary index family.  Unlike `fullLetterOfFocus`, this leaves every base
letter a base letter and therefore commutes with formal inversion. -/
def embedNLetter (_D : AuxiliaryPeripheralFamily A N S) :
    GGT.RelLetter G Bool → GGT.RelLetter G (AuxiliaryPeripheralIndex k)
  | GGT.RelLetter.base x => GGT.RelLetter.base x
  | GGT.RelLetter.comp b h => GGT.RelLetter.comp (none, b) h

@[simp] theorem val_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    (a : GGT.RelLetter G Bool) : (D.embedNLetter a).val = a.val := by
  cases a <;> rfl

@[simp] theorem focusLetterOfFull_embedNLetter
    (D : AuxiliaryPeripheralFamily A N S) (a : GGT.RelLetter G Bool) :
    D.focusLetterOfFull (D.embedNLetter a) = a := by
  cases a <;> rfl

theorem inv_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    (a : GGT.RelLetter G Bool) :
    RelWord.inv (D.embedNLetter a) = D.embedNLetter (RelWord.inv a) := by
  cases a <;> rfl

theorem listVal_map_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    (w : List (GGT.RelLetter G Bool)) :
    GGT.RelLetter.listVal (w.map D.embedNLetter) =
      GGT.RelLetter.listVal w := by
  show ((w.map D.embedNLetter).map GGT.RelLetter.val).prod = _
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun a _ => D.val_embedNLetter a)

theorem revInv_map_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    (w : List (GGT.RelLetter G Bool)) :
    RelWord.revInv (w.map D.embedNLetter) =
      (RelWord.revInv w).map D.embedNLetter := by
  simp only [RelWord.revInv, List.map_reverse, List.map_map]
  apply congrArg List.reverse
  exact List.map_congr_left (fun a _ => D.inv_embedNLetter a)

theorem sym_map_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    {R w : List (GGT.RelLetter G Bool)} (h : RelWord.Sym R w) :
    RelWord.Sym (R.map D.embedNLetter) (w.map D.embedNLetter) := by
  induction h with
  | base => exact RelWord.Sym.base
  | rot n _ ih =>
      simpa only [List.map_rotate] using RelWord.Sym.rot n ih
  | inv _ ih =>
      simpa only [D.revInv_map_embedNLetter] using RelWord.Sym.inv ih

/-- Every word in the symmetrized embedded family has a unique spelling by
embedded focused letters, and that spelling belongs to the focused
symmetrized family. -/
theorem exists_preimage_sym_embedNLetter (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)}
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (h : RelWord.Sym (R.map D.embedNLetter) v) :
    ∃ w, RelWord.Sym R w ∧ v = w.map D.embedNLetter := by
  induction h with
  | base => exact ⟨R, RelWord.Sym.base, rfl⟩
  | rot n _ ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      exact ⟨w.rotate n, RelWord.Sym.rot n hw, by rw [List.map_rotate]⟩
  | inv _ ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      exact ⟨RelWord.revInv w, RelWord.Sym.inv hw,
        D.revInv_map_embedNLetter w⟩

theorem sym_map_focusLetterOfFull (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)}
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (h : RelWord.Sym (R.map D.embedNLetter) v) :
    RelWord.Sym R (v.map D.focusLetterOfFull) := by
  obtain ⟨w, hw, rfl⟩ := D.exists_preimage_sym_embedNLetter h
  have heq : (w.map D.embedNLetter).map D.focusLetterOfFull = w := by
    rw [List.map_map]
    calc
      List.map (D.focusLetterOfFull ∘ D.embedNLetter) w =
          List.map id w := List.map_congr_left (fun a _ => by
            rw [Function.comp_apply, D.focusLetterOfFull_embedNLetter]
            rfl)
      _ = w := List.map_id w
  rw [heq]
  exact hw

theorem embed_focus_eq_of_mem_sym (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)}
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hv : RelWord.Sym (R.map D.embedNLetter) v) {a} (ha : a ∈ v) :
    D.embedNLetter (D.focusLetterOfFull a) = a := by
  obtain ⟨w, _hw, rfl⟩ := D.exists_preimage_sym_embedNLetter hv
  obtain ⟨c, _hc, rfl⟩ := List.mem_map.mp ha
  rw [D.focusLetterOfFull_embedNLetter]

theorem map_embed_focus_eq_of_letters_in_sym
    (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)}
    {v z : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hv : RelWord.Sym (R.map D.embedNLetter) v)
    (hz : ∀ a ∈ z, a ∈ v) :
    (z.map D.focusLetterOfFull).map D.embedNLetter = z := by
  rw [List.map_map]
  calc
    List.map (D.embedNLetter ∘ D.focusLetterOfFull) z = List.map id z :=
      List.map_congr_left (fun a ha => by
        rw [Function.comp_apply, D.embed_focus_eq_of_mem_sym hv (hz a ha)]
        rfl)
    _ = z := List.map_id z

private theorem wordNorm_focusNBase_le (D : AuxiliaryPeripheralFamily A N S)
    (x : G) : wordNorm D.focusNRel.base x ≤ wordNorm D.rel.base x := by
  exact wordNorm_mono Set.subset_union_left
    (wordLengths_nonempty D.isSymmetricGeneratingSet_base x)

theorem isPiece_focus_of_full (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)} {eps : ℕ}
    {u v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hp : RelWord.IsPiece D.rel
      (RelWord.symmetrized (R.map D.embedNLetter)) eps u v) :
    RelWord.IsPiece D.focusNRel (RelWord.symmetrized R) eps
      (u.map D.focusLetterOfFull) (v.map D.focusLetterOfFull) := by
  obtain ⟨hv, ⟨s, hvs⟩, v', hv', hne, u', s', hv's', y, z,
    hy, hz, hval, hexcl⟩ := hp
  have huv : ∀ a ∈ u, a ∈ v := by
    intro a ha
    rw [hvs]
    exact List.mem_append_left _ ha
  have hu'v' : ∀ a ∈ u', a ∈ v' := by
    intro a ha
    rw [hv's']
    exact List.mem_append_left _ ha
  have hvrec := D.map_embed_focus_eq_of_letters_in_sym hv (fun a ha => ha)
  have hv'rec := D.map_embed_focus_eq_of_letters_in_sym hv' (fun a ha => ha)
  refine ⟨D.sym_map_focusLetterOfFull hv,
    ⟨s.map D.focusLetterOfFull, by simp [hvs]⟩,
    v'.map D.focusLetterOfFull, D.sym_map_focusLetterOfFull hv', ?_,
    u'.map D.focusLetterOfFull, s'.map D.focusLetterOfFull, by simp [hv's'],
    y, z, le_trans (D.wordNorm_focusNBase_le y) hy,
    le_trans (D.wordNorm_focusNBase_le z) hz, ?_, ?_⟩
  · intro heq
    apply hne
    rw [← hvrec, ← hv'rec, heq]
  · simpa only [D.listVal_map_focusLetterOfFull] using hval
  · simpa only [D.listVal_map_focusLetterOfFull] using hexcl

theorem isPublishedPiece_focus_of_full
    (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)} {eps : ℕ}
    {u u' v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hp : RelWord.IsPublishedPiece D.rel
      (RelWord.symmetrized (R.map D.embedNLetter)) eps u u' v) :
    RelWord.IsPublishedPiece D.focusNRel (RelWord.symmetrized R) eps
      (u.map D.focusLetterOfFull) (u'.map D.focusLetterOfFull)
      (v.map D.focusLetterOfFull) := by
  obtain ⟨hv, ⟨s, hvs⟩, v', hv', s', hv's', y, z,
    hy, hz, hval, hexcl⟩ := hp
  refine ⟨D.sym_map_focusLetterOfFull hv,
    ⟨s.map D.focusLetterOfFull, by simp [hvs]⟩,
    v'.map D.focusLetterOfFull, D.sym_map_focusLetterOfFull hv',
    s'.map D.focusLetterOfFull, by simp [hv's'], y, z,
    le_trans (D.wordNorm_focusNBase_le y) hy,
    le_trans (D.wordNorm_focusNBase_le z) hz, ?_, ?_⟩
  · simpa only [D.listVal_map_focusLetterOfFull] using hval
  · simpa only [D.listVal_map_focusLetterOfFull] using hexcl

theorem isPrimePiece_focus_of_full
    (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)} {eps : ℕ}
    {u u' v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hp : RelWord.IsPrimePiece D.rel
      (RelWord.symmetrized (R.map D.embedNLetter)) eps u u' v) :
    RelWord.IsPrimePiece D.focusNRel (RelWord.symmetrized R) eps
      (u.map D.focusLetterOfFull) (u'.map D.focusLetterOfFull)
      (v.map D.focusLetterOfFull) := by
  obtain ⟨hv, middle, tail, hsplit, y, z, hy, hz, hval⟩ := hp
  refine ⟨D.sym_map_focusLetterOfFull hv,
    middle.map D.focusLetterOfFull, tail.map D.focusLetterOfFull,
    by simp [hsplit], y, z, le_trans (D.wordNorm_focusNBase_le y) hy,
    le_trans (D.wordNorm_focusNBase_le z) hz, ?_⟩
  simpa only [D.listVal_map_focusLetterOfFull] using hval

theorem base_mem_of_mem_sym_embedNLetter
    (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)}
    (hbaseR : ∀ x, GGT.RelLetter.base x ∈ R → x ∈ D.rel.base)
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    (hv : RelWord.Sym (R.map D.embedNLetter) v) {x : G}
    (hx : GGT.RelLetter.base x ∈ v) : x ∈ D.rel.base := by
  rcases RelWord.Sym.letters hv (GGT.RelLetter.base x) hx with hxR | hxR
  · obtain ⟨a, ha, hax⟩ := List.mem_map.mp hxR
    cases a with
    | base y =>
        cases hax
        exact hbaseR x ha
    | comp b y => cases hax
  · change GGT.RelLetter.base x⁻¹ ∈ R.map D.embedNLetter at hxR
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp hxR
    cases a with
    | base y =>
        cases hax
        simpa only [inv_inv] using D.base_inv x⁻¹ (hbaseR x⁻¹ ha)
    | comp b y => cases hax

theorem isLemma49Input_map_embedNLetter
    (D : AuxiliaryPeripheralFamily A N S)
    {R : List (GGT.RelLetter G Bool)} {eps rho : ℕ} {mu : ℝ}
    (hbaseR : ∀ x, GGT.RelLetter.base x ∈ R → x ∈ D.rel.base)
    (h : RelWord.IsLemma49Input D.focusNRel
      (RelWord.symmetrized R) eps mu rho) :
    RelWord.IsLemma49Input D.rel
      (RelWord.symmetrized (R.map D.embedNLetter)) eps mu rho := by
  let V := RelWord.symmetrized (R.map D.embedNLetter)
  have hadm : ∀ v ∈ V, RelWord.IsAdmissible D.rel v := by
    intro v hv a ha
    cases a with
    | base x => exact D.base_mem_of_mem_sym_embedNLetter hbaseR hv ha
    | comp i x =>
        have hsupp := D.embed_focus_eq_of_mem_sym hv ha
        rcases i with ⟨tag, b⟩
        cases tag with
        | none =>
            change x ∈ D.rel.fam (none, b)
            have hf := h.admissible (v.map D.focusLetterOfFull)
              (D.sym_map_focusLetterOfFull hv) (GGT.RelLetter.comp b x)
              (List.mem_map.mpr ⟨_, ha, rfl⟩)
            exact hf
        | some j => cases hsupp
  have hsmall : RelWord.IsSmallCancellation D.rel V eps mu rho := by
    refine
      { admissible := hadm
        inv_mem := fun v hv => RelWord.Sym.inv hv
        rotate_mem := fun v hv n => RelWord.Sym.rot n hv
        long := by
          intro v hv
          have hl := h.long (v.map D.focusLetterOfFull)
            (D.sym_map_focusLetterOfFull hv)
          simpa using hl
        deep := by
          intro v hv a ha i hcomp hball
          have hsupp := D.embed_focus_eq_of_mem_sym hv ha
          cases a with
          | base x => exact hcomp.elim
          | comp j x =>
              rcases j with ⟨tag, b⟩
              cases tag with
              | some q => cases hsupp
              | none =>
                  have hib : i = (none, b) := hcomp.symm
                  subst i
                  have hdeep := h.deep (v.map D.focusLetterOfFull)
                    (D.sym_map_focusLetterOfFull hv) (GGT.RelLetter.comp b x)
                    (List.mem_map.mpr ⟨_, ha, rfl⟩) b rfl
                  exact hdeep (D.focusNRel_relBall_eq b rho ▸ hball)
        pieces_small := by
          intro u v hp
          have hlen := h.pieces_small (u.map D.focusLetterOfFull)
            (v.map D.focusLetterOfFull) (D.isPiece_focus_of_full hp)
          simpa using hlen }
  refine
    { toIsLemma44Input :=
        { toIsSmallCancellation := hsmall
          quasiGeodesic := by
            intro v hv
            have hq := h.quasiGeodesic (v.map D.focusLetterOfFull)
              (D.sym_map_focusLetterOfFull hv)
            rw [D.focusNRel_alphabet] at hq
            simpa only [List.length_map,
              D.listVal_take_map_focusLetterOfFull] using hq
          publishedPiecesSmall := by
            intro u u' v hp
            have hbound := h.publishedPiecesSmall
              (u.map D.focusLetterOfFull) (u'.map D.focusLetterOfFull)
              (v.map D.focusLetterOfFull)
              (D.isPublishedPiece_focus_of_full hp)
            simpa using hbound
          stronglyBounded := RelWord.finite_componentLetters_symmetrized _ }
      primePiecesSmall := by
        intro u u' v hp
        have hbound := h.primePiecesSmall
          (u.map D.focusLetterOfFull) (u'.map D.focusLetterOfFull)
          (v.map D.focusLetterOfFull) (D.isPrimePiece_focus_of_full hp)
        simpa using hbound }

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

/-- Hull's exact alternating relator, now read in the complete selected
auxiliary family rather than in the historical Bool-only quotient interface. -/
theorem exists_auxiliaryRelatorOfBaseLetterPublished_exact
    (D : AuxiliaryPeripheralFamily A N S) (hN : Suitable A.alphabet N)
    (t : G) (ht : t⁻¹ ∈ D.rel.base) (eps rho : ℕ) (mu : ℝ)
    (hmu : 0 < mu) :
    ∃ u ∈ N,
      ∃ R : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)),
        GGT.RelLetter.listVal R = t⁻¹ * u ∧
          RelWord.IsLemma49Input D.rel (RelWord.symmetrized R) eps mu rho := by
  let E := D.focusNCore
  have htE : t⁻¹ ∈ E.rel.base := Or.inl ht
  obtain ⟨u, hu, R, hval, hsc, hbase⟩ :=
    exists_hullRelatorWord₂OfBaseLetterPublished_exact E hN t htE
      eps rho mu hmu
  refine ⟨u, hu, R.map D.embedNLetter, ?_, ?_⟩
  · rw [D.listVal_map_embedNLetter, hval]
  · apply D.isLemma49Input_map_embedNLetter
    · intro x hx
      rw [hbase x hx]
      exact ht
    · exact hsc

/-- The torsion-free one-step theorem from the canonical quotient and the
full-family §6 relator.  The target is adjoined before the quotient constants
are selected, so both halves use the same relative generating set. -/
theorem hullOneStep_of_canonicalQuotient
    (hquot : TorsionFreeHullCanonicalQuotientStatement.{u}) :
    HullOneStepStatement.{u} := by
  intro G _ hG A N hN k S hS t R
  obtain ⟨D, eps, rho, mu, ht, hmu, hgood⟩ :=
    hquot hG A N hN S hS t R
  obtain ⟨u, hu, v, hval, hsc⟩ :=
    exists_auxiliaryRelatorOfBaseLetterPublished_exact D hN t ht
      eps rho mu hmu
  obtain ⟨Q⟩ := hgood (RelWord.symmetrized v) v
    (RelWord.self_mem_symmetrized v) hsc
  have hrel : Q.q (t⁻¹ * u) = 1 := by
    rw [← hval, ← MonoidHom.mem_ker, Q.ker_eq]
    exact Subgroup.subset_normalClosure rfl
  have hqt : Q.q t = Q.q u := by
    rw [map_mul, map_inv] at hrel
    exact inv_mul_eq_one.mp hrel
  refine ⟨{ step := Q.toHullStep
            mem_map := ?_
            kerNormallyGenerated := ⟨{t⁻¹ * u}, by simp, ?_⟩ }⟩
  · intro _
    show Q.q t ∈ N.map Q.q
    rw [hqt]
    exact Subgroup.mem_map_of_mem _ hu
  · show Q.q.ker =
      Subgroup.normalClosure ((({t⁻¹ * u} : Finset G)) : Set G)
    rw [Q.ker_eq, hval, Finset.coe_singleton]

end AuxiliaryPeripheralFamily

end HullSC
end GroupApproximation

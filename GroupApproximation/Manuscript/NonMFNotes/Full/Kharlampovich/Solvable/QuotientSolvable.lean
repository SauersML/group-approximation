/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.QuotientBlocks

/-!
# `G(M)` is solvable once the conjugates of the `x`-letters commute

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`
(Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4, Lemma `lH`, `p = 2`).

Let `T` be the normal closure of the letters `x_{j,S}` and `N_A` the normal closure of the
letters `x_{j,S}` and `A_i`.  Then
1. `G(M)' ≤ N_A`, since any two small letters commute (G1) (`top_comm_le_na`);
2. `⁅N_A, N_A⁆ ≤ T`: modulo `T`, conjugation by any element maps the set `wAll M` of the
   conjugates `A_i^c` into itself (`conj_wAll`), and these pairwise commute (`wAll_commute`)
   (`na_comm_le_t`);
3. `⁅T, T⁆ = 1` when all conjugates of the `x`-letters commute (`t_comm_le_bot`).
Hence the derived series of `G(M)` reaches `⊥` at step `3`
(`KMS.isSolvable_of_conj_x_commute`).
-/

namespace GroupApproximation.Full.Kharlampovich
namespace KMS
namespace QS

open Forward
open scoped commutatorElement

section Generic

variable {G Q : Type*} [Group G] [Group Q]

theorem map_conj_eq_of_map_eq_one (φ : G →* Q) {u : G} (w : G) (h : φ u = 1) :
    φ (u⁻¹ * w * u) = φ w := by
  rw [map_mul, map_mul, map_inv, h, inv_one, one_mul, mul_one]

theorem map_conj_mul (φ : G →* Q) {x y w w₁ : G} (h : φ (x⁻¹ * w * x) = φ w₁) :
    φ ((x * y)⁻¹ * w * (x * y)) = φ (y⁻¹ * w₁ * y) := by
  have e : (x * y)⁻¹ * w * (x * y) = y⁻¹ * (x⁻¹ * w * x) * y := by group
  rw [e, map_mul φ (y⁻¹ * (x⁻¹ * w * x)) y, map_mul φ y⁻¹ (x⁻¹ * w * x), h,
    map_mul φ (y⁻¹ * w₁) y, map_mul φ y⁻¹ w₁]

theorem conj_eq_of_commute {v w u : G} (h : Commute v w) (hu : u = v ∨ u = v⁻¹) :
    u⁻¹ * w * u = w := by
  rcases hu with rfl | rfl
  · exact inv_mul_mul_eq_of_commute h
  · exact inv_inv_mul_mul_eq_of_commute h

end Generic

variable {K N : ℕ} (M : Minsky.Machine K N)

/-- The letters `x_{j,S}`. -/
def xSet : Set (KhGroup M) :=
  {g | ∃ (j : Fin (N + 1)) (S : Finset (Fin (K + 1))), g = kLet M (.x j S)}

/-- The letters `A_i`. -/
def aSet : Set (KhGroup M) := {g | ∃ i, g = kLet M (.bigA i)}

/-- The normal closure `T` of the `x`-letters. -/
abbrev tSub : Subgroup (KhGroup M) := Subgroup.normalClosure (xSet M)

/-- The normal closure `N_A` of the `x`-letters and the `A`-letters. -/
abbrev naSub : Subgroup (KhGroup M) := Subgroup.normalClosure (xSet M ∪ aSet M)

theorem x_mem_t (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) : kLet M (.x j S) ∈ tSub M :=
  Subgroup.subset_normalClosure (s := xSet M) ⟨j, S, rfl⟩

theorem pi_x (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) :
    QuotientGroup.mk' (tSub M) (kLet M (.x j S)) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact x_mem_t M j S

/-! ## Conjugating `wAll M` modulo `T` -/

/-- Conjugation by a small letter (or its inverse) maps `wAll M` into itself modulo `T`. -/
theorem conj_small {s : KhGen K N} (hs : s.IsSmall) {u : KhGroup M}
    (hu : u = kLet M s ∨ u = (kLet M s)⁻¹) {w : KhGroup M} (hw : w ∈ wAll M) :
    ∃ w' ∈ wAll M,
      QuotientGroup.mk' (tSub M) (u⁻¹ * w * u) = QuotientGroup.mk' (tSub M) w' := by
  obtain ⟨j, hj⟩ := exists_block_of_isSmall hs
  obtain ⟨i, c, hc, rfl⟩ := hw
  by_cases hji : j = i
  · have hj' : s.block = some i := by rw [hj, hji]
    have hsi : kLet M s ∈ Subgroup.closure (smallSet M i) :=
      Subgroup.subset_closure ⟨s, hs, hj', rfl⟩
    have hu' : u ∈ Subgroup.closure (smallSet M i) := by
      rcases hu with rfl | rfl
      · exact hsi
      · exact inv_mem hsi
    refine ⟨(c * u)⁻¹ * kLet M (.bigA i) * (c * u), ⟨i, c * u, mul_mem hc hu', rfl⟩, ?_⟩
    have e : u⁻¹ * (c⁻¹ * kLet M (.bigA i) * c) * u
        = (c * u)⁻¹ * kLet M (.bigA i) * (c * u) := by group
    rw [e]
  · have hgen : ∀ x ∈ ({kLet M s} : Set (KhGroup M)), ∀ y ∈ smallSet M i,
        Commute x y := by
      rintro _ rfl _ ⟨t, _, ht, rfl⟩
      exact commute_kLet_of_mem M (block_mem_relators M hj ht hji)
    have hsc : Commute (kLet M s) c :=
      BR.commute_of_mem_closure hgen (Subgroup.subset_closure (Set.mem_singleton _)) hc
    have hsA : Commute (kLet M s) (kLet M (.bigA i)) :=
      commute_kLet_of_mem M (block_mem_relators M (t := .bigA i) hj rfl hji)
    have hcomm : Commute (kLet M s) (c⁻¹ * kLet M (.bigA i) * c) :=
      (hsc.inv_right.mul_right hsA).mul_right hsc
    refine ⟨c⁻¹ * kLet M (.bigA i) * c, ⟨i, c, hc, rfl⟩, ?_⟩
    rw [conj_eq_of_commute hcomm hu]

/-- Conjugation by a letter (or its inverse) maps `wAll M` into itself modulo `T`. -/
theorem conj_letter (s : KhGen K N) {u : KhGroup M} (hu : u = kLet M s ∨ u = (kLet M s)⁻¹)
    {w : KhGroup M} (hw : w ∈ wAll M) :
    ∃ w' ∈ wAll M,
      QuotientGroup.mk' (tSub M) (u⁻¹ * w * u) = QuotientGroup.mk' (tSub M) w' := by
  cases s with
  | x j S =>
    refine ⟨w, hw, map_conj_eq_of_map_eq_one (QuotientGroup.mk' (tSub M)) w ?_⟩
    rcases hu with rfl | rfl
    · exact pi_x M j S
    · rw [map_inv, pi_x M j S, inv_one]
  | bigA k =>
    have hA : kLet M (.bigA k) ∈ wAll M := ⟨k, bigA_mem_wSet M k⟩
    exact ⟨w, hw, by rw [conj_eq_of_commute (wAll_commute M hA hw) hu]⟩
  | a n => exact conj_small M (s := .a n) trivial hu hw
  | a' n => exact conj_small M (s := .a' n) trivial hu hw
  | ta n => exact conj_small M (s := .ta n) trivial hu hw
  | ta' n => exact conj_small M (s := .ta' n) trivial hu hw

/-- Conjugation by any element maps `wAll M` into itself modulo `T`. -/
theorem conj_wAll (g : KhGroup M) :
    ∀ w ∈ wAll M, ∃ w' ∈ wAll M,
      QuotientGroup.mk' (tSub M) (g⁻¹ * w * g) = QuotientGroup.mk' (tSub M) w' := by
  have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := relators M))) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction'' with
  | mem _ hx =>
    obtain ⟨s, rfl⟩ := hx
    intro w hw
    exact conj_letter M s (Or.inl rfl) hw
  | inv_mem _ hx =>
    obtain ⟨s, rfl⟩ := hx
    intro w hw
    exact conj_letter M s (Or.inr rfl) hw
  | one =>
    intro w hw
    exact ⟨w, hw, by rw [inv_one, one_mul, mul_one]⟩
  | mul _ _ _ _ ihx ihy =>
    intro w hw
    obtain ⟨w₁, hw₁, e₁⟩ := ihx w hw
    obtain ⟨w₂, hw₂, e₂⟩ := ihy w₁ hw₁
    exact ⟨w₂, hw₂, (map_conj_mul (QuotientGroup.mk' (tSub M)) e₁).trans e₂⟩

/-! ## The three steps -/

/-- Every letter lies in `N_A` or is small. -/
theorem of_mem_na_or_isSmall (s : KhGen K N) :
    (PresentedGroup.of s : KhGroup M) ∈ naSub M ∨ s.IsSmall := by
  cases s with
  | x j S =>
    exact Or.inl (Subgroup.subset_normalClosure (s := xSet M ∪ aSet M) (Or.inl ⟨j, S, rfl⟩))
  | bigA i =>
    exact Or.inl (Subgroup.subset_normalClosure (s := xSet M ∪ aSet M) (Or.inr ⟨i, rfl⟩))
  | a _ => exact Or.inr trivial
  | a' _ => exact Or.inr trivial
  | ta _ => exact Or.inr trivial
  | ta' _ => exact Or.inr trivial

/-- Step 1: `G(M)' ≤ N_A` (the small letters pairwise commute, G1). -/
theorem top_comm_le_na : ⁅(⊤ : Subgroup (KhGroup M)), ⊤⁆ ≤ naSub M := by
  rw [← PresentedGroup.closure_range_of (relators M)]
  refine commutator_closure_le ?_
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rcases of_mem_na_or_isSmall M s with hs | hs
  · exact commutatorElement_mem_left _ hs
  · rcases of_mem_na_or_isSmall M t with ht | ht
    · exact commutatorElement_mem_right _ ht
    · have h1 : ⁅(PresentedGroup.of s : KhGroup M), PresentedGroup.of t⁆ = 1 :=
        commutatorElement_eq_one_iff_commute.mpr
          (commute_kLet_of_mem M (small_mem_relators M hs ht))
      rw [h1]
      exact one_mem _

/-- Step 2: `⁅N_A, N_A⁆ ≤ T`. -/
theorem na_comm_le_t : ⁅naSub M, naSub M⁆ ≤ tSub M := by
  show ⁅Subgroup.closure (Group.conjugatesOfSet (xSet M ∪ aSet M)),
    Subgroup.closure (Group.conjugatesOfSet (xSet M ∪ aSet M))⁆ ≤ tSub M
  refine commutator_closure_le ?_
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨b, hb, hyb⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxa
  obtain ⟨d, rfl⟩ := isConj_iff.mp hyb
  rcases ha with ⟨j, S, rfl⟩ | ⟨i, rfl⟩
  · exact commutatorElement_mem_left _
      ((inferInstance : (tSub M).Normal).conj_mem _ (x_mem_t M j S) c)
  · rcases hb with ⟨j', S', rfl⟩ | ⟨i', rfl⟩
    · exact commutatorElement_mem_right _
        ((inferInstance : (tSub M).Normal).conj_mem _ (x_mem_t M j' S') d)
    · obtain ⟨w, hw, ew⟩ := conj_wAll M c⁻¹ (kLet M (.bigA i)) ⟨i, bigA_mem_wSet M i⟩
      obtain ⟨w', hw', ew'⟩ :=
        conj_wAll M d⁻¹ (kLet M (.bigA i')) ⟨i', bigA_mem_wSet M i'⟩
      rw [inv_inv] at ew ew'
      have e : QuotientGroup.mk' (tSub M)
          ⁅c * kLet M (.bigA i) * c⁻¹, d * kLet M (.bigA i') * d⁻¹⁆ = 1 := by
        rw [map_commutatorElement, ew, ew']
        exact commutatorElement_eq_one_iff_commute.mpr
          ((wAll_commute M hw hw').map (QuotientGroup.mk' (tSub M)))
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e

/-- Step 3: `⁅T, T⁆ = 1` when the conjugates of the `x`-letters pairwise commute. -/
theorem t_comm_le_bot
    (hT : ∀ (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) (g h : KhGroup M),
      Commute (g⁻¹ * PresentedGroup.of (KhGen.x j S) * g)
        (h⁻¹ * PresentedGroup.of (KhGen.x j' S') * h)) :
    ⁅tSub M, tSub M⁆ ≤ ⊥ := by
  show ⁅Subgroup.closure (Group.conjugatesOfSet (xSet M)),
    Subgroup.closure (Group.conjugatesOfSet (xSet M))⁆ ≤ ⊥
  refine commutator_closure_le_bot ?_
  intro x hx y hy
  obtain ⟨a, ⟨j, S, rfl⟩, hxa⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨b, ⟨j', S', rfl⟩, hyb⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxa
  obtain ⟨d, rfl⟩ := isConj_iff.mp hyb
  have h := hT j j' S S' c⁻¹ d⁻¹
  rw [inv_inv, inv_inv] at h
  exact h

end QS
end KMS

/-- **Kharlampovich--Myasnikov--Sapir, Lemma `lH` (`p = 2`).**  If all conjugates of the
letters `x_{j,S}` pairwise commute, then `G(M)` is solvable (of derived length at most `3`). -/
theorem KMS.isSolvable_of_conj_x_commute {K N : ℕ} (M : Minsky.Machine K N)
    (hT : ∀ (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) (g h : KMS.KhGroup M),
      Commute (g⁻¹ * PresentedGroup.of (KMS.KhGen.x j S) * g)
        (h⁻¹ * PresentedGroup.of (KMS.KhGen.x j' S') * h)) :
    IsSolvable (KMS.KhGroup M) := by
  have h1 : derivedSeries (KMS.KhGroup M) 1 ≤ KMS.QS.naSub M :=
    (derivedSeries_succ (KMS.KhGroup M) 0).trans_le (by
      rw [derivedSeries_zero]
      exact KMS.QS.top_comm_le_na M)
  have h2 : derivedSeries (KMS.KhGroup M) 2 ≤ KMS.QS.tSub M :=
    (derivedSeries_succ (KMS.KhGroup M) 1).trans_le
      ((Subgroup.commutator_mono h1 h1).trans (KMS.QS.na_comm_le_t M))
  have h3 : derivedSeries (KMS.KhGroup M) 3 ≤ ⊥ :=
    (derivedSeries_succ (KMS.KhGroup M) 2).trans_le
      ((Subgroup.commutator_mono h2 h2).trans (KMS.QS.t_comm_le_bot M hT))
  exact ⟨⟨3, le_bot_iff.mp h3⟩⟩

end GroupApproximation.Full.Kharlampovich

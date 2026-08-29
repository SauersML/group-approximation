import GroupApproximation.Sofic.Sofic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic

/-!
# Soficity of split extensions by the integers

`SoficFiniteSemidirect` proves that `N ⋊ K` is sofic when `N` is sofic and
`K` is *finite*, using the exact induced model on `Y × K`.  That argument is
unavailable for `K = ℤ`: there is no finite level set on which the shift acts
by an honest action.

This file proves the split `ℤ` case, which is the special case of the
Elek--Szabó amenable-quotient permanence theorem that the sofic-witness
endpoint needs.  The model is the same induced model with the level set `ℤ`
truncated to `ZMod L`:

`(n, k) · (y, i) = (σ (twist (-(i + k).val) n) y, i + k)`.

The twist exponent is the *integer representative* of the level, so the
cocycle identity that made the finite case exact now holds off a set of at
most `2|k|` levels -- the wrap-around boundary of the cyclic level set.
Choosing `L` large compared with the window's shifts makes that boundary
fraction as small as desired, while the base model handles every level
exactly as before.  Two ingredients therefore go into the estimate: the
fibrewise average identity for level permutations, and the bound on the
number of wrap-around levels.
-/

namespace GroupApproximation
namespace SoficIntegerExtension

open Finset

variable {N : Type*} [Group N]

/-! ## Level permutations -/

section Level

variable {Y : Type*} {L : ℕ}

/-- The permutation of `Y × ZMod L` that applies the level-indexed
permutation `p` and then shifts the level by `c`. -/
def levelPerm (p : ZMod L → Equiv.Perm Y) (c : ZMod L) :
    Equiv.Perm (Y × ZMod L) where
  toFun z := (p z.2 z.1, z.2 + c)
  invFun z := ((p (z.2 - c)).symm z.1, z.2 - c)
  left_inv z := by
    apply Prod.ext <;> simp
  right_inv z := by
    apply Prod.ext <;> simp

@[simp] theorem levelPerm_apply (p : ZMod L → Equiv.Perm Y) (c : ZMod L)
    (z : Y × ZMod L) : levelPerm p c z = (p z.2 z.1, z.2 + c) := rfl

/-- Level permutations compose to level permutations. -/
theorem levelPerm_mul (p q : ZMod L → Equiv.Perm Y) (c d : ZMod L) :
    levelPerm p c * levelPerm q d =
      levelPerm (fun i ↦ p (i + d) * q i) (d + c) := by
  apply Equiv.ext
  intro z
  apply Prod.ext
  · rfl
  · show z.2 + d + c = z.2 + (d + c)
    rw [add_assoc]

/-- The finite carrier of the truncated induced model. -/
abbrev levelModel (Y : FiniteModel) (L : ℕ) [NeZero L] : FiniteModel :=
  ⟨Y × ZMod L, inferInstance, inferInstance⟩

/-- **Fibrewise average.**  Two level permutations with the same shift are at
the average of their fibrewise distances. -/
theorem hammingDistance_levelPerm (Y : FiniteModel) {L : ℕ} [NeZero L]
    (p q : ZMod L → Equiv.Perm Y) (c : ZMod L) :
    hammingDistance (levelModel Y L) (levelPerm p c) (levelPerm q c) =
      (∑ i : ZMod L, hammingDistance Y (p i) (q i)) / L := by
  classical
  have hfiber : ∀ i : ZMod L,
      (hammingDisagreement (levelPerm p c) (levelPerm q c)).filter
          (fun z ↦ z.2 = i) =
        (hammingDisagreement (p i) (q i)).map
          ⟨fun y ↦ (y, i), fun _ _ e ↦ congrArg Prod.fst e⟩ := by
    intro i
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, mem_hammingDisagreement,
      levelPerm_apply, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hz, rfl⟩
      refine ⟨z.1, ?_, rfl⟩
      intro hy
      exact hz (Prod.ext hy rfl)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, rfl⟩
      intro hz
      exact hy (congrArg Prod.fst hz)
  have hcardD :
      (hammingDisagreement (levelPerm p c) (levelPerm q c)).card =
        ∑ i : ZMod L, (hammingDisagreement (p i) (q i)).card := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (s := hammingDisagreement (levelPerm p c) (levelPerm q c))
      (t := (Finset.univ : Finset (ZMod L))) (g := Prod.snd)
    simp only [Finset.mem_univ, Finset.filter_true] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hfiber i, Finset.card_map]
  have hcard : Fintype.card (levelModel Y L) = Fintype.card Y * L := by
    show Fintype.card (Y × ZMod L) = _
    rw [Fintype.card_prod, ZMod.card]
  have hRHS : (∑ i : ZMod L, hammingDistance Y (p i) (q i)) =
      (∑ i : ZMod L, ((hammingDisagreement (p i) (q i)).card : ℝ)) /
        (Fintype.card Y : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ rfl
  rw [hammingDistance, hcard, hcardD, hRHS]
  push_cast
  rw [div_div]

/-- Level permutations with different shifts disagree everywhere. -/
theorem hammingDistance_levelPerm_of_shift_ne (Y : FiniteModel) {L : ℕ}
    [NeZero L] (p q : ZMod L → Equiv.Perm Y) {c d : ZMod L} (hcd : c ≠ d)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (levelModel Y L) (levelPerm p c) (levelPerm q d) = 1 := by
  classical
  have hdis : hammingDisagreement (levelPerm p c) (levelPerm q d) =
      Finset.univ := by
    refine Finset.eq_univ_of_forall fun z ↦ ?_
    rw [mem_hammingDisagreement]
    intro hz
    exact hcd (add_left_cancel (congrArg Prod.snd hz))
  rw [hammingDistance, hdis, Finset.card_univ]
  apply div_self
  have : Fintype.card (levelModel Y L) = Fintype.card Y * L := by
    show Fintype.card (Y × ZMod L) = _
    rw [Fintype.card_prod, ZMod.card]
  rw [this]
  exact_mod_cast (Nat.mul_pos hY (Nat.pos_of_ne_zero (NeZero.ne L))).ne'

end Level

/-! ## The wrap-around boundary -/

/-- The levels at which adding `k` wraps around the cyclic level set. -/
noncomputable def badLevels (L : ℕ) [NeZero L] (k : ℤ) : Finset (ZMod L) :=
  Finset.univ.filter fun u ↦ (((u + (k : ZMod L)).val : ℤ) ≠ (u.val : ℤ) + k)

/-- Off the wrap-around boundary the integer representative is additive. -/
theorem val_add_of_not_bad {L : ℕ} [NeZero L] {k : ℤ} {u : ZMod L}
    (hu : u ∉ badLevels L k) :
    ((u + (k : ZMod L)).val : ℤ) = (u.val : ℤ) + k := by
  by_contra h
  exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)

/-- A level is in the boundary only if its representative is within `|k|` of
one of the two ends. -/
theorem badLevels_subset {L : ℕ} [NeZero L] (k : ℤ) :
    badLevels L k ⊆
      (Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs) ∪
        (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val) := by
  classical
  intro u hu
  rw [badLevels, Finset.mem_filter] at hu
  by_contra hmem
  rw [Finset.mem_union, not_or] at hmem
  have h1 : k.natAbs ≤ u.val :=
    not_lt.mp fun h ↦ hmem.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
  have h2 : u.val < L - k.natAbs :=
    not_le.mp fun h ↦ hmem.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
  -- the representative stays inside `[0, L)`, so the cast is additive
  have hlt : u.val < L := ZMod.val_lt u
  have hrange : 0 ≤ (u.val : ℤ) + k ∧ (u.val : ℤ) + k < L := by omega
  obtain ⟨hge, hltL⟩ := hrange
  set m : ℕ := ((u.val : ℤ) + k).toNat with hm
  have hmval : (m : ℤ) = (u.val : ℤ) + k := Int.toNat_of_nonneg hge
  have hmlt : m < L := by omega
  have hcast : u + (k : ZMod L) = (m : ZMod L) := by
    have : ((((u.val : ℤ) + k : ℤ)) : ZMod L) = (m : ZMod L) := by
      rw [← hmval]
      push_cast
      ring
    rw [← this]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  apply hu.2
  rw [hcast, ZMod.val_natCast_of_lt hmlt, hmval]

/-- **The boundary is small**: at most `2|k|` levels wrap around. -/
theorem card_badLevels_le {L : ℕ} [NeZero L] (k : ℤ) :
    (badLevels L k).card ≤ 2 * k.natAbs := by
  classical
  have hmemA : ∀ u ∈ (Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs),
      u.val < k.natAbs := by
    intro u hu
    simpa using hu
  have hmemB : ∀ u ∈ (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val),
      L - k.natAbs ≤ u.val := by
    intro u hu
    simpa using hu
  have hlow : (Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs).card ≤
      k.natAbs := by
    have hle : (Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs).card ≤
        (Finset.range k.natAbs).card := by
      refine Finset.card_le_card_of_injOn (fun u ↦ u.val) ?_ ?_
      · intro u hu
        exact Finset.mem_range.mpr (hmemA u hu)
      · intro a _ b _ hab
        exact ZMod.val_injective _ hab
    simpa using hle
  have hhigh : (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val).card ≤
      k.natAbs := by
    have hle : (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val).card ≤
        (Finset.range k.natAbs).card := by
      apply Finset.card_le_card_of_injOn (fun u ↦ u.val - (L - k.natAbs))
      · intro u hu
        have h1 := hmemB u hu
        have h2 : u.val < L := ZMod.val_lt u
        refine Finset.mem_range.mpr ?_
        show u.val - (L - k.natAbs) < k.natAbs
        omega
      · intro a ha b hb hab
        have ha' := hmemB a (Finset.mem_coe.mp ha)
        have hb' := hmemB b (Finset.mem_coe.mp hb)
        have hal : a.val < L := ZMod.val_lt a
        have hbl : b.val < L := ZMod.val_lt b
        apply ZMod.val_injective
        have hab' : a.val - (L - k.natAbs) = b.val - (L - k.natAbs) := hab
        omega
    simpa using hle
  calc (badLevels L k).card
      ≤ ((Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs) ∪
          (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val)).card :=
        Finset.card_le_card (badLevels_subset k)
    _ ≤ (Finset.univ.filter fun u : ZMod L ↦ u.val < k.natAbs).card +
          (Finset.univ.filter fun u : ZMod L ↦ L - k.natAbs ≤ u.val).card :=
        Finset.card_union_le _ _
    _ ≤ k.natAbs + k.natAbs := Nat.add_le_add hlow hhigh
    _ = 2 * k.natAbs := by ring

/-! ## The split integer extension -/

section IntExtension

variable (φ : Multiplicative ℤ →* MulAut N)

/-- The `j`-th power of the acting automorphism, as a map on `N`. -/
def tw (j : ℤ) (n : N) : N := φ (Multiplicative.ofAdd j) n

theorem tw_add (j₁ j₂ : ℤ) (n : N) :
    tw φ (j₁ + j₂) n = tw φ j₁ (tw φ j₂ n) := by
  show φ (Multiplicative.ofAdd (j₁ + j₂)) n = _
  rw [ofAdd_add, map_mul]
  rfl

theorem tw_mul (j : ℤ) (a b : N) : tw φ j (a * b) = tw φ j a * tw φ j b :=
  map_mul _ _ _

theorem tw_injective (j : ℤ) : Function.Injective (tw φ j) :=
  (φ (Multiplicative.ofAdd j)).injective

/-- The integer shift of an element of the split extension. -/
def shiftOf (g : N ⋊[φ] Multiplicative ℤ) : ℤ := Multiplicative.toAdd g.right

@[simp] theorem shiftOf_mul (g h : N ⋊[φ] Multiplicative ℤ) :
    shiftOf φ (g * h) = shiftOf φ g + shiftOf φ h := rfl

theorem left_mul (g h : N ⋊[φ] Multiplicative ℤ) :
    (g * h).left = g.left * tw φ (shiftOf φ g) h.left := rfl

variable {Y : Type*}

/-- The label used on the fibre whose *destination* level is `r`. -/
def labelAt (L : ℕ) (g : N ⋊[φ] Multiplicative ℤ) (r : ZMod L) :
    N :=
  tw φ (-(r.val : ℤ)) g.left

/-- The truncated induced permutation: apply the level label, then shift the
level by the integer part. -/
def modelPerm (L : ℕ) (σ : N → Equiv.Perm Y)
    (g : N ⋊[φ] Multiplicative ℤ) : Equiv.Perm (Y × ZMod L) :=
  levelPerm (fun i ↦ σ (labelAt φ L g (i + ((shiftOf φ g : ℤ) : ZMod L))))
    ((shiftOf φ g : ℤ) : ZMod L)

theorem modelPerm_mul_left (L : ℕ) (σ : N → Equiv.Perm Y)
    (g h : N ⋊[φ] Multiplicative ℤ) :
    modelPerm φ L σ g * modelPerm φ L σ h =
      levelPerm (fun i ↦
          σ (labelAt φ L g
              (i + ((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L))) *
            σ (labelAt φ L h (i + ((shiftOf φ h : ℤ) : ZMod L))))
        (((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L)) := by
  rw [modelPerm, modelPerm, levelPerm_mul]

theorem modelPerm_mul_right (L : ℕ) (σ : N → Equiv.Perm Y)
    (g h : N ⋊[φ] Multiplicative ℤ) :
    modelPerm φ L σ (g * h) =
      levelPerm (fun i ↦
          σ (labelAt φ L (g * h)
              (i + ((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L))))
        (((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L)) := by
  have hs : ((shiftOf φ (g * h) : ℤ) : ZMod L) =
      ((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L) := by
    rw [shiftOf_mul]
    push_cast
    ring
  rw [modelPerm, hs]
  simp only [← add_assoc]

/-- **Off the wrap-around boundary the label cocycle is exact.** -/
theorem labelAt_mul_of_not_bad (L : ℕ) [NeZero L]
    (g h : N ⋊[φ] Multiplicative ℤ) (i : ZMod L)
    (hgood : (i + ((shiftOf φ h : ℤ) : ZMod L)) ∉
      badLevels L (shiftOf φ g)) :
    labelAt φ L (g * h)
        (i + ((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L)) =
      labelAt φ L g
          (i + ((shiftOf φ h : ℤ) : ZMod L) + ((shiftOf φ g : ℤ) : ZMod L)) *
        labelAt φ L h (i + ((shiftOf φ h : ℤ) : ZMod L)) := by
  have hval := val_add_of_not_bad hgood
  rw [labelAt, labelAt, labelAt, left_mul, tw_mul, ← tw_add]
  congr 2
  omega

/-- **Soficity passes to split extensions by the integers.**

This is the special case of Elek--Szabó amenable-quotient permanence that the
sofic-witness endpoint needs, proved directly from the local definition. -/
theorem isSofic_int_semidirectProduct (hN : IsSofic N) :
    IsSofic (N ⋊[φ] Multiplicative ℤ) := by
  classical
  intro F ε hε
  -- the largest shift occurring in the window
  set K : ℕ := F.sup (fun g ↦ (shiftOf φ g).natAbs) with hKdef
  have hKmem : ∀ g ∈ F, (shiftOf φ g).natAbs ≤ K := fun g hg ↦
    Finset.le_sup (f := fun g ↦ (shiftOf φ g).natAbs) hg
  -- a level count separating those shifts and making the boundary thin
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (4 * (K : ℝ) / ε)
  set L : ℕ := max (2 * K + 1) (L₀ + 1) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  haveI : NeZero L := ⟨hLpos.ne'⟩
  have hKL : 2 * K < L := lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hLbig : 4 * (K : ℝ) / ε < L := by
    have hstep : (L₀ : ℝ) < L := by
      have : L₀ + 1 ≤ L := le_max_right _ _
      exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self L₀) this
    exact lt_trans hL₀ hstep
  have h4K : 4 * (K : ℝ) < ε * L := by
    have := (div_lt_iff₀ hε).mp hLbig
    simpa [mul_comm] using this
  have hboundary : 2 * (K : ℝ) ≤ (ε / 2) * L := by
    linarith only [h4K]
  -- the twisted test set for the base model
  set T : Finset N :=
    (F ×ˢ Finset.range L).image (fun p ↦ tw φ (-(p.2 : ℤ)) p.1.left) with hTdef
  have hmemT : ∀ g ∈ F, ∀ r : ZMod L, labelAt φ L g r ∈ T := by
    intro g hg r
    refine Finset.mem_image.mpr ⟨(g, r.val), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr (ZMod.val_lt r)⟩
  obtain ⟨M⟩ := hN T (ε / 2) (half_pos hε)
  have hcardModel : Fintype.card (levelModel M.carrier L) =
      Fintype.card M.carrier * L := by
    show Fintype.card (M.carrier × ZMod L) = _
    rw [Fintype.card_prod, ZMod.card]
  refine ⟨{
    carrier := levelModel M.carrier L
    nonempty := ?_
    map := fun g ↦ modelPerm φ L M.map g
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [hcardModel]
    exact Nat.mul_pos M.nonempty hLpos
  · -- multiplicativity: exact off the wrap-around boundary
    intro g hg h hh
    rw [modelPerm_mul_right, modelPerm_mul_left,
      hammingDistance_levelPerm M.carrier _ _ _]
    set sg : ZMod L := ((shiftOf φ g : ℤ) : ZMod L) with hsg
    set sh : ZMod L := ((shiftOf φ h : ℤ) : ZMod L) with hsh
    set d : ZMod L → ℝ := fun i ↦
      hammingDistance M.carrier
        (M.map (labelAt φ L (g * h) (i + sh + sg)))
        (M.map (labelAt φ L g (i + sh + sg)) *
          M.map (labelAt φ L h (i + sh))) with hd
    set BAD : Finset (ZMod L) :=
      Finset.univ.filter (fun i ↦ (i + sh) ∈ badLevels L (shiftOf φ g))
      with hBAD
    have hmemBAD : ∀ i ∈ BAD, (i + sh) ∈ badLevels L (shiftOf φ g) := by
      intro i hi
      simpa [hBAD] using hi
    have hBADcard : BAD.card ≤ 2 * K := by
      have h1 : BAD.card ≤ (badLevels L (shiftOf φ g)).card := by
        refine Finset.card_le_card_of_injOn (fun i ↦ i + sh) ?_ ?_
        · intro i hi
          exact hmemBAD i (Finset.mem_coe.mp hi)
        · intro a _ b _ hab
          exact add_right_cancel hab
      have h2 := card_badLevels_le (L := L) (shiftOf φ g)
      have h3 : (shiftOf φ g).natAbs ≤ K := hKmem g hg
      omega
    have hall : ∀ i : ZMod L, d i ≤ 1 := fun i ↦ hammingDistance_le_one _ _ _
    have hgood : ∀ i ∈ BADᶜ, d i ≤ ε / 2 := by
      intro i hi
      have hnb : (i + sh) ∉ badLevels L (shiftOf φ g) := by
        intro hb
        exact (Finset.mem_compl.mp hi) (by simpa [hBAD] using hb)
      have hlab := labelAt_mul_of_not_bad φ L g h i hnb
      show hammingDistance M.carrier
          (M.map (labelAt φ L (g * h) (i + sh + sg)))
          (M.map (labelAt φ L g (i + sh + sg)) *
            M.map (labelAt φ L h (i + sh))) ≤ ε / 2
      rw [hlab]
      exact M.multiplicative _ (hmemT g hg _) _ (hmemT h hh _)
    have hsum : ∑ i : ZMod L, d i ≤ 2 * (K : ℝ) + L * (ε / 2) := by
      have hsplit : ∑ i ∈ BAD, d i + ∑ i ∈ BADᶜ, d i = ∑ i : ZMod L, d i :=
        Finset.sum_add_sum_compl _ _
      have hb : ∑ i ∈ BAD, d i ≤ (BAD.card : ℝ) := by
        calc ∑ i ∈ BAD, d i ≤ ∑ _i ∈ BAD, (1 : ℝ) :=
              Finset.sum_le_sum (fun i _ ↦ hall i)
          _ = (BAD.card : ℝ) := by simp
      have hc : ∑ i ∈ BADᶜ, d i ≤ (BADᶜ.card : ℝ) * (ε / 2) := by
        calc ∑ i ∈ BADᶜ, d i ≤ ∑ _i ∈ BADᶜ, (ε / 2) := Finset.sum_le_sum hgood
          _ = (BADᶜ.card : ℝ) * (ε / 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (BADᶜ.card : ℝ) ≤ L := by
        have hle : BADᶜ.card ≤ Fintype.card (ZMod L) := Finset.card_le_univ _
        rw [ZMod.card] at hle
        exact_mod_cast hle
      have hBADR : (BAD.card : ℝ) ≤ 2 * K := by exact_mod_cast hBADcard
      have hεpos : (0 : ℝ) < ε / 2 := half_pos hε
      nlinarith only [hsplit, hb, hc, hcard, hBADR, hεpos]
    rw [div_le_iff₀ hLR]
    linarith only [hsum, hboundary]
  · -- separation
    intro g hg h hh hne
    by_cases hs : ((shiftOf φ g : ℤ) : ZMod L) = ((shiftOf φ h : ℤ) : ZMod L)
    · -- equal truncated shifts force equal integer shifts
      have hKg : (shiftOf φ g).natAbs ≤ K := hKmem g hg
      have hKh : (shiftOf φ h).natAbs ≤ K := hKmem h hh
      have hKLZ : (2 * K : ℤ) < (L : ℤ) := by exact_mod_cast hKL
      have hkeq : shiftOf φ g = shiftOf φ h := by
        have hmod : shiftOf φ g ≡ shiftOf φ h [ZMOD (L : ℕ)] :=
          (ZMod.intCast_eq_intCast_iff _ _ _).mp hs
        obtain ⟨c, hc⟩ : (L : ℤ) ∣ (shiftOf φ h - shiftOf φ g) :=
          Int.ModEq.dvd hmod
        have hgb : -(K : ℤ) ≤ shiftOf φ g ∧ shiftOf φ g ≤ (K : ℤ) := by omega
        have hhb : -(K : ℤ) ≤ shiftOf φ h ∧ shiftOf φ h ≤ (K : ℤ) := by omega
        have hLZ : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hLpos
        rcases lt_trichotomy c 0 with hneg | hzero | hpos
        · exfalso
          have hcL : (L : ℤ) * c ≤ -(L : ℤ) := by
            nlinarith only [hneg, hLZ]
          linarith only [hc, hcL, hgb.1, hgb.2, hhb.1, hhb.2, hKLZ]
        · rw [hzero, mul_zero] at hc
          linarith only [hc]
        · exfalso
          have hcL : (L : ℤ) ≤ (L : ℤ) * c := by
            nlinarith only [hpos, hLZ]
          linarith only [hc, hcL, hgb.1, hgb.2, hhb.1, hhb.2, hKLZ]
      have hright : g.right = h.right :=
        Multiplicative.toAdd.injective hkeq
      have hleft : g.left ≠ h.left := fun heq ↦
        hne (SemidirectProduct.ext heq hright)
      rw [modelPerm, modelPerm, ← hs,
        hammingDistance_levelPerm M.carrier _ _ _]
      have hfib : ∀ i : ZMod L,
          1 - ε / 2 ≤ hammingDistance M.carrier
            (M.map (labelAt φ L g (i + ((shiftOf φ g : ℤ) : ZMod L))))
            (M.map (labelAt φ L h (i + ((shiftOf φ g : ℤ) : ZMod L)))) := by
        intro i
        refine M.separated _ (hmemT g hg _) _ (hmemT h hh _) ?_
        intro heq
        exact hleft (tw_injective φ _ heq)
      have hsum : (L : ℝ) * (1 - ε / 2) ≤
          ∑ i : ZMod L, hammingDistance M.carrier
            (M.map (labelAt φ L g (i + ((shiftOf φ g : ℤ) : ZMod L))))
            (M.map (labelAt φ L h (i + ((shiftOf φ g : ℤ) : ZMod L)))) := by
        have hconst := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (ZMod L))) ↦ hfib i)
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card] at hconst
        exact hconst
      rw [le_div_iff₀ hLR]
      nlinarith only [hsum, hε, hLR]
    · rw [modelPerm, modelPerm,
        hammingDistance_levelPerm_of_shift_ne M.carrier _ _ hs M.nonempty]
      exact sub_le_self 1 hε.le

end IntExtension

end SoficIntegerExtension
end GroupApproximation

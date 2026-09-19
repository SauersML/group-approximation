import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients
import GroupApproximation.Leavitt.ElementaryNormalGeneration
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# Relative elementary groups, congruence subgroups, and the centre of `GL`

The manuscript's five-sentence proof of Proposition `prop:simple` quotes
Preusser's normal-subgroup theorem for `GL_n` and then runs an elementary case
split on the level ideal.  This file isolates the generic upper-sandwich
hypothesis and proves the rest of that route: the two objects the sandwich is
stated with, the two endpoints of the case split, and the manuscript's own
two-step computation of the centre of `GL_ι(R)`.  `PreusserAssembly`
discharges the hypothesis for normal subgroups of `EL_ι(R)`; the direct
root-extraction route remains independently available in
`DiagonalNormalExtraction`.

## The two objects

* `relativeElementary ι I` — the manuscript's `EL_n(R, I)`, the normal closure
  inside `EL_ι(R)` of the elementary matrices `e_{ij}(a)` with `a ∈ I`.
* `congruenceSubgroup ι I` — the manuscript's `C_n(R, I)`.  A unit of
  `M_ι(R)` belongs to it when it is congruent modulo `I`, entrywise, to a
  scalar matrix `lam • 1` whose coefficient is central *modulo `I`*
  (`relativeCenter`).  Both clauses are needed: the relative-centre clause is
  what makes the set closed under inversion, and it is what makes the level-`0`
  computation `C_ι(R, 0) = Z(GL_ι(R))` come out right.

## The two endpoints of the case split

* `relativeElementary_top` : `EL_ι(R, R) = EL_ι(R)`;
* `congruenceSubgroup_bot` : `C_ι(R, 0) = Z(GL_ι(R))`, for `2 ≤ #ι`.

## The centre

The manuscript computes `Z(GL_12(R))` in two steps, and both are formalized
here for an arbitrary unital ring and `2 ≤ #ι`:

* `eq_diagonal_of_commute_single` — commuting with every `e_{ij}(1)` already
  forces a matrix to be scalar;
* `commute_of_commute_single` — commuting with every `e_{ij}(a)` then forces
  the scalar into the centre of `R`.

`center_eq_bot_of_central_units_trivial` packages the two steps in the form the
manuscript uses them: if the central units of `R` are trivial then
`Z(GL_ι(R)) = 1`.  Its hypothesis is exactly the conclusion of
`BinaryLeavitt.central_units_trivial`, which is already proved in
`GroupApproximation/Leavitt/BinaryLeavittSimple.lean`, so for the binary
Leavitt algebra the input is available inside this library.

## Manuscript status

`isSimpleGroup_of_preusser_sandwich` assembles the four pieces.  It carries a
single explicit hypothesis, `hpreusser`, which is Preusser's normal-subgroup
theorem in the exact shape the printed proof quotes it.  That generic interface
is discharged in `PreusserAssembly` from the exchange refinement and the
row-annihilator calculation.  It is not an assumption of the repository's
final result:
`DiagonalNormalExtraction.isSimpleGroup_of_leavittFamily_root_extraction`
proves the needed simplicity directly from the Leavitt-family inputs.
-/

namespace GroupApproximation

/-! ### Coefficients that are central modulo an ideal -/

section RelativeCenter

variable {R : Type*} [Ring R]

/-- The **`I`-relative centre** of `R`: the coefficients that commute with
every element of `R` modulo `I`.  For `I = 0` this is the ordinary centre. -/
def relativeCenter (I : TwoSidedIdeal R) : Set R :=
  {lam | ∀ x : R, lam * x - x * lam ∈ I}

theorem mem_relativeCenter {I : TwoSidedIdeal R} {lam : R} :
    lam ∈ relativeCenter I ↔ ∀ x : R, lam * x - x * lam ∈ I :=
  Iff.rfl

theorem zero_mem_relativeCenter (I : TwoSidedIdeal R) :
    (0 : R) ∈ relativeCenter I := by
  intro x
  rw [zero_mul, mul_zero, sub_self]
  exact I.zero_mem

theorem one_mem_relativeCenter (I : TwoSidedIdeal R) :
    (1 : R) ∈ relativeCenter I := by
  intro x
  rw [one_mul, mul_one, sub_self]
  exact I.zero_mem

theorem mul_mem_relativeCenter {I : TwoSidedIdeal R} {lam mu : R}
    (hlam : lam ∈ relativeCenter I) (hmu : mu ∈ relativeCenter I) :
    lam * mu ∈ relativeCenter I := by
  intro x
  have key : lam * mu * x - x * (lam * mu)
      = lam * (mu * x - x * mu) + (lam * x - x * lam) * mu := by
    noncomm_ring
  rw [key]
  exact I.add_mem (I.mul_mem_left _ _ (hmu x)) (I.mul_mem_right _ _ (hlam x))

/-- At level `0` the relative centre is the honest centre. -/
theorem mem_relativeCenter_bot {lam : R} :
    lam ∈ relativeCenter (⊥ : TwoSidedIdeal R) ↔ ∀ x : R, lam * x = x * lam := by
  constructor
  · intro h x
    have hx : lam * x - x * lam = 0 := by simpa using h x
    exact sub_eq_zero.mp hx
  · intro h x
    have hx : lam * x - x * lam = 0 := sub_eq_zero.mpr (h x)
    simpa using hx

/-- If `mu` is a left inverse of `lam` modulo `I`, then `lam` may be cancelled
from a left factor: `lam * d ∈ I` forces `d ∈ I`. -/
theorem mem_of_mul_mem_of_relative_inv (I : TwoSidedIdeal R) {lam mu d : R}
    (hf : mu * lam - 1 ∈ I) (hd : lam * d ∈ I) : d ∈ I := by
  have key : d = mu * (lam * d) - (mu * lam - 1) * d := by noncomm_ring
  rw [key]
  exact I.sub_mem (I.mul_mem_left _ _ hd) (I.mul_mem_right _ _ hf)

/-- Two elements with the same `lam`-multiple modulo `I` have their difference
killed by `lam` modulo `I`. -/
theorem mul_sub_mem_of_sub_mem (I : TwoSidedIdeal R) {lam s t e : R}
    (hs : lam * s - e ∈ I) (ht : lam * t - e ∈ I) : lam * (s - t) ∈ I := by
  have key : lam * (s - t) = (lam * s - e) - (lam * t - e) := by noncomm_ring
  rw [key]
  exact I.sub_mem hs ht

/-- Finite sums of ideal elements stay in the ideal. -/
theorem sum_mem_twoSidedIdeal {κ : Type*} (I : TwoSidedIdeal R) {s : Finset κ}
    {f : κ → R} (hf : ∀ i ∈ s, f i ∈ I) : (∑ i ∈ s, f i) ∈ I :=
  Finset.sum_induction f (· ∈ I) (fun _ _ ha hb ↦ I.add_mem ha hb) I.zero_mem hf

/-- A matrix whose entries all lie in `I` absorbs a right factor. -/
theorem entry_mul_mem_of_left {κ : Type*} [Fintype κ] (I : TwoSidedIdeal R)
    {A : Matrix κ κ R} (hA : ∀ i j : κ, A i j ∈ I) (B : Matrix κ κ R)
    (i j : κ) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact sum_mem_twoSidedIdeal I fun k _ ↦ I.mul_mem_right _ _ (hA i k)

/-- A matrix whose entries all lie in `I` absorbs a left factor. -/
theorem entry_mul_mem_of_right {κ : Type*} [Fintype κ] (I : TwoSidedIdeal R)
    (A : Matrix κ κ R) {B : Matrix κ κ R} (hB : ∀ i j : κ, B i j ∈ I)
    (i j : κ) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact sum_mem_twoSidedIdeal I fun k _ ↦ I.mul_mem_left _ _ (hB k j)

end RelativeCenter

/-! ### The relative elementary group `EL_ι(R, I)` -/

section RelativeElementaryDefs

variable (ι : Type*) [Fintype ι] [DecidableEq ι] {R : Type*} [Ring R]

/-- The elementary roots with coefficients in `I`, as a subset of `EL_ι(R)`. -/
def relativeElementarySet (I : TwoSidedIdeal R) : Set (elementaryGroup ι R) :=
  {g | ∃ (i j : ι) (hij : i ≠ j) (a : R), a ∈ I ∧ g = elGen i j hij a}

/-- The **relative elementary group** `EL_ι(R, I)`: the normal closure inside
`EL_ι(R)` of the elementary matrices with coefficients in `I`. -/
def relativeElementary (I : TwoSidedIdeal R) : Subgroup (elementaryGroup ι R) :=
  Subgroup.normalClosure (relativeElementarySet ι I)

end RelativeElementaryDefs

section RelativeElementary

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

instance relativeElementary_normal (I : TwoSidedIdeal R) :
    (relativeElementary ι I).Normal :=
  Subgroup.normalClosure_normal

theorem elGen_mem_relativeElementary {I : TwoSidedIdeal R} (i j : ι)
    (hij : i ≠ j) {a : R} (ha : a ∈ I) :
    elGen i j hij a ∈ relativeElementary ι I :=
  Subgroup.subset_normalClosure ⟨i, j, hij, a, ha, rfl⟩

theorem relativeElementary_mono {I J : TwoSidedIdeal R} (hIJ : I ≤ J) :
    relativeElementary ι I ≤ relativeElementary ι J := by
  apply Subgroup.normalClosure_mono
  rintro g ⟨i, j, hij, a, ha, rfl⟩
  exact ⟨i, j, hij, a, hIJ ha, rfl⟩

/-- **First endpoint of the manuscript's case split.**  At level `R` the
relative elementary group is everything: the roots with arbitrary coefficients
already generate `EL_ι(R)`. -/
theorem relativeElementary_top :
    relativeElementary ι (⊤ : TwoSidedIdeal R) = ⊤ := by
  refine le_antisymm le_top ?_
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact Subgroup.subset_normalClosure
        ⟨i, j, hij, a, by simp, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
      have hxy : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : elementaryGroup ι R)
          = (⟨x, hx⟩ : elementaryGroup ι R) * ⟨y, hy⟩ := rfl
      rw [hxy]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
      have hxi : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : elementaryGroup ι R)
          = (⟨x, hx⟩ : elementaryGroup ι R)⁻¹ := rfl
      rw [hxi]
      exact Subgroup.inv_mem _ ihx

end RelativeElementary

/-! ### The level ideal of a normal subgroup

For a normal subgroup `N ◁ EL_ι(R)`, its elementary level consists of the
coefficients occurring in every root subgroup of `N`.  Three indices suffice
to prove that this additive set is a two-sided ideal: the Steinberg
commutator relation implements multiplication on either side.  This is the
canonical candidate level in Preusser's sandwich and makes the lower sandwich
inclusion unconditional. -/

section NormalLevel

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The elementary level ideal of a normal subgroup of `EL_ι(R)`. -/
def normalLevel (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk'
    {a | ∀ (i j : ι) (hij : i ≠ j), elGen i j hij a ∈ N}
  (by
    intro i j hij
    rw [elGen_zero]
    exact N.one_mem)
  (by
    intro a b ha hb i j hij
    rw [← elGen_mul]
    exact N.mul_mem (ha i j hij) (hb i j hij))
  (by
    intro a ha i j hij
    have heq : elGen i j hij (-a) = (elGen i j hij a)⁻¹ := by
      calc
        elGen i j hij (-a) = 1 * elGen i j hij (-a) := (one_mul _).symm
        _ = ((elGen i j hij a)⁻¹ * elGen i j hij a) *
              elGen i j hij (-a) := by simp
        _ = (elGen i j hij a)⁻¹ *
              (elGen i j hij a * elGen i j hij (-a)) := by
                rw [mul_assoc]
        _ = (elGen i j hij a)⁻¹ := by
              rw [elGen_mul, add_neg_cancel, elGen_zero, mul_one]
    rw [heq]
    exact N.inv_mem (ha i j hij))
  (by
    intro r a ha i j hij
    obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
    have hik : i ≠ k := Ne.symm hki
    have hkj' : k ≠ j := hkj
    have hy : elGen k j hkj' a ∈ N := ha k j hkj'
    rw [← elGen_commutator i k j hik hkj' hij r a]
    exact N.mul_mem (hN.conj_mem _ hy (elGen i k hik r)) (N.inv_mem hy))
  (by
    intro a r ha i j hij
    obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
    have hik : i ≠ k := Ne.symm hki
    have hkj' : k ≠ j := hkj
    have hx : elGen i k hik a ∈ N := ha i k hik
    rw [← elGen_commutator i k j hik hkj' hij a r]
    have heq : elGen i k hik a * elGen k j hkj' r *
          (elGen i k hik a)⁻¹ * (elGen k j hkj' r)⁻¹ =
        elGen i k hik a *
          (elGen k j hkj' r * (elGen i k hik a)⁻¹ *
            (elGen k j hkj' r)⁻¹) := by simp only [mul_assoc]
    rw [heq]
    exact N.mul_mem hx
      (hN.conj_mem _ (N.inv_mem hx) (elGen k j hkj' r)))

theorem mem_normalLevel_iff (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {a : R} :
    a ∈ normalLevel hcard N ↔
      ∀ (i j : ι) (hij : i ≠ j), elGen i j hij a ∈ N :=
  by simp [normalLevel]

/-- The lower half of Preusser's sandwich holds for the canonical level ideal
without any external normal-structure theorem. -/
theorem relativeElementary_normalLevel_le (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] :
    relativeElementary ι (normalLevel hcard N) ≤ N := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨i, j, hij, a, ha, rfl⟩
  exact (mem_normalLevel_iff hcard N).mp ha i j hij

/-- If the canonical level is nonzero and every nonzero coefficient has a
two-sided unit sandwich, normal generation of one root makes `N` everything. -/
theorem normal_eq_top_of_normalLevel_ne_bot
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    (hlevel : normalLevel hcard N ≠ ⊥) : N = ⊤ := by
  obtain ⟨a, ha, ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hlevel)
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
    1 < Fintype.card ι)
  have hamem : ∀ (i j : ι) (hij : i ≠ j), elGen i j hij a ∈ N :=
    (mem_normalLevel_iff hcard N).mp ha
  exact elementaryGroup_normal_eq_top_of_elGen_mem hcard N hij
    (hamem i j hij) (hdiv a ha0)

end NormalLevel

/-! ### The full congruence subgroup `C_ι(R, I)` -/

section Congruence

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Constant diagonal matrices multiply coefficientwise. -/
theorem diagonal_const_mul_const (lam mu : R) :
    (Matrix.diagonal fun _ : ι ↦ lam) * (Matrix.diagonal fun _ : ι ↦ mu)
      = Matrix.diagonal fun _ : ι ↦ lam * mu :=
  Matrix.diagonal_mul_diagonal _ _

/-- **Closure under inversion for the congruence condition.**  If `u` is
congruent to `lam • 1` modulo `I` with `lam` central modulo `I`, then `u⁻¹` is
congruent to `mu • 1` with `mu` central modulo `I`; one may take for `mu` any
diagonal entry of `u⁻¹`, since `lam` is invertible modulo `I`. -/
theorem exists_inv_congruent (I : TwoSidedIdeal R) (u : (Matrix ι ι R)ˣ)
    {lam : R} (hlam : lam ∈ relativeCenter I)
    (hu : ∀ i j : ι,
      ((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam) i j ∈ I) :
    ∃ mu ∈ relativeCenter I, ∀ i j : ι,
      (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
        - Matrix.diagonal fun _ : ι ↦ mu) i j ∈ I := by
  rcases isEmpty_or_nonempty ι with hempty | hne
  · exact ⟨0, zero_mem_relativeCenter I, fun i ↦ (hempty.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  -- the entries of `lam • 1 - u` lie in `I`
  have hu' : ∀ i j : ι,
      ((Matrix.diagonal fun _ : ι ↦ lam) - (u : Matrix ι ι R)) i j ∈ I := by
    intro i j
    have h : ((Matrix.diagonal fun _ : ι ↦ lam) - (u : Matrix ι ι R)) i j
        = -(((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, neg_sub]
    rw [h]
    exact I.neg_mem (hu i j)
  -- `lam` is a left inverse of `u⁻¹` modulo `I`, entrywise
  have step₁ : ∀ i j : ι,
      lam * ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j
        - (1 : Matrix ι ι R) i j ∈ I := by
    intro i j
    have hid : (((Matrix.diagonal fun _ : ι ↦ lam) - (u : Matrix ι ι R))
          * ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) i j
        = lam * ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j
          - (1 : Matrix ι ι R) i j := by
      rw [sub_mul, Matrix.sub_apply, u.mul_inv, Matrix.diagonal_mul]
    rw [← hid]
    exact entry_mul_mem_of_left I hu' _ i j
  -- and a right inverse of `u⁻¹` modulo `I`, entrywise
  have step₂ : ∀ i j : ι,
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j * lam
        - (1 : Matrix ι ι R) i j ∈ I := by
    intro i j
    have hid : (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
          * ((Matrix.diagonal fun _ : ι ↦ lam) - (u : Matrix ι ι R))) i j
        = ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j * lam
          - (1 : Matrix ι ι R) i j := by
      rw [mul_sub, Matrix.sub_apply, u.inv_mul, Matrix.mul_diagonal]
    rw [← hid]
    exact entry_mul_mem_of_right I _ hu' i j
  obtain ⟨mu, hmudef⟩ :
      ∃ mu : R, mu = ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i₀ i₀ := ⟨_, rfl⟩
  have he : lam * mu - 1 ∈ I := by
    rw [hmudef]
    have h := step₁ i₀ i₀
    rwa [Matrix.one_apply_eq] at h
  have hf : mu * lam - 1 ∈ I := by
    rw [hmudef]
    have h := step₂ i₀ i₀
    rwa [Matrix.one_apply_eq] at h
  -- `mu` is again central modulo `I`
  have hmu : mu ∈ relativeCenter I := by
    intro x
    have key : mu * x - x * mu
        = -(mu * x * (lam * mu - 1)) + mu * -(lam * x - x * lam) * mu
          + (mu * lam - 1) * (x * mu) := by
      noncomm_ring
    rw [key]
    exact I.add_mem
      (I.add_mem (I.neg_mem (I.mul_mem_left _ _ he))
        (I.mul_mem_right _ _ (I.mul_mem_left _ _ (I.neg_mem (hlam x)))))
      (I.mul_mem_right _ _ hf)
  refine ⟨mu, hmu, fun i j ↦ ?_⟩
  -- the scalar `mu • 1` satisfies the same relation as `u⁻¹` after scaling by `lam`
  have hscal : lam * (Matrix.diagonal fun _ : ι ↦ mu) i j
      - (1 : Matrix ι ι R) i j ∈ I := by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact he
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, mul_zero,
        sub_zero]
      exact I.zero_mem
  have hd : lam * ((((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      - Matrix.diagonal fun _ : ι ↦ mu) i j) ∈ I := by
    rw [Matrix.sub_apply]
    exact mul_sub_mem_of_sub_mem I (step₁ i j) hscal
  exact mem_of_mul_mem_of_relative_inv I hf hd

end Congruence

section CongruenceDef

variable (ι : Type*) [Fintype ι] [DecidableEq ι] {R : Type*} [Ring R]

/-- The **full congruence subgroup of level `I`**, the manuscript's
`C_n(R, I)`: the units of `M_ι(R)` congruent modulo `I` to a scalar matrix
whose coefficient is central modulo `I`. -/
def congruenceSubgroup (I : TwoSidedIdeal R) : Subgroup (Matrix ι ι R)ˣ where
  carrier := {u | ∃ lam ∈ relativeCenter I, ∀ i j : ι,
    ((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam) i j ∈ I}
  one_mem' := by
    refine ⟨1, one_mem_relativeCenter I, fun i j ↦ ?_⟩
    have hz : ((1 : (Matrix ι ι R)ˣ) : Matrix ι ι R)
        - (Matrix.diagonal fun _ : ι ↦ (1 : R)) = 0 := by
      rw [Units.val_one, Matrix.diagonal_one, sub_self]
    rw [hz, Matrix.zero_apply]
    exact I.zero_mem
  mul_mem' := by
    rintro u v ⟨lam, hlam, hu⟩ ⟨mu, hmu, hv⟩
    refine ⟨lam * mu, mul_mem_relativeCenter hlam hmu, fun i j ↦ ?_⟩
    have hsplit : ((u * v : (Matrix ι ι R)ˣ) : Matrix ι ι R)
          - Matrix.diagonal (fun _ : ι ↦ lam * mu)
        = ((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam)
            * (v : Matrix ι ι R)
          + (Matrix.diagonal fun _ : ι ↦ lam)
            * ((v : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ mu) := by
      rw [Units.val_mul, ← diagonal_const_mul_const lam mu]
      noncomm_ring
    rw [hsplit, Matrix.add_apply]
    exact I.add_mem (entry_mul_mem_of_left I hu _ i j)
      (entry_mul_mem_of_right I _ hv i j)
  inv_mem' := by
    rintro u ⟨lam, hlam, hu⟩
    exact exists_inv_congruent I u hlam hu

end CongruenceDef

section CongruenceMem

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

theorem mem_congruenceSubgroup {I : TwoSidedIdeal R} {u : (Matrix ι ι R)ˣ} :
    u ∈ congruenceSubgroup ι I ↔ ∃ lam ∈ relativeCenter I, ∀ i j : ι,
      ((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam) i j ∈ I :=
  Iff.rfl

end CongruenceMem

/-! ### The centre of `GL_ι(R)`, by the manuscript's two-step argument -/

section Centre

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- A row of `single i j c` off the `i`-th one annihilates any right factor. -/
theorem single_mul_apply_eq_zero (i j : ι) (c : R) (M : Matrix ι ι R) {a : ι}
    (h : i ≠ a) (b : ι) : (Matrix.single i j c * M) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [Matrix.single_apply_of_row_ne h, zero_mul]

/-- **Step 1 of the manuscript's centre computation.**  Commuting with every
elementary matrix `e_{ij}(1)` already forces a matrix to be scalar: the
off-diagonal entries are killed and the diagonal entries are all equal. -/
theorem eq_diagonal_of_commute_single (hcard : 1 < Fintype.card ι) (i₀ : ι)
    (z : Matrix ι ι R)
    (hz : ∀ i j : ι, i ≠ j →
      z * Matrix.single i j (1 : R) = Matrix.single i j (1 : R) * z) :
    z = Matrix.diagonal fun _ : ι ↦ z i₀ i₀ := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.diagonal_apply_eq]
    by_cases hk : k = i₀
    · subst hk
      rfl
    · have h : (z * Matrix.single k i₀ (1 : R)) k i₀
          = (Matrix.single k i₀ (1 : R) * z) k i₀ := by
        rw [hz k i₀ hk]
      rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, mul_one,
        one_mul] at h
      exact h
  · rw [Matrix.diagonal_apply_ne _ hkl]
    obtain ⟨j, hjl⟩ := Fintype.exists_ne_of_one_lt_card hcard l
    have h : (z * Matrix.single l j (1 : R)) k j
        = (Matrix.single l j (1 : R) * z) k j := by
      rw [hz l j (Ne.symm hjl)]
    rw [Matrix.mul_single_apply_same, mul_one,
      single_mul_apply_eq_zero l j (1 : R) z (Ne.symm hkl) j] at h
    exact h

/-- **Step 2 of the manuscript's centre computation.**  Once the matrix is
known to be the scalar `lam`, commuting with `e_{ij}(a)` for arbitrary `a`
says exactly that `lam` is central in `R`. -/
theorem commute_of_commute_single (hcard : 1 < Fintype.card ι) (lam : R)
    (hz : ∀ (i j : ι) (a : R), i ≠ j →
      (Matrix.diagonal fun _ : ι ↦ lam) * Matrix.single i j a
        = Matrix.single i j a * (Matrix.diagonal fun _ : ι ↦ lam))
    (x : R) : lam * x = x * lam := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have h : ((Matrix.diagonal fun _ : ι ↦ lam) * Matrix.single i j x) i j
      = (Matrix.single i j x * (Matrix.diagonal fun _ : ι ↦ lam)) i j := by
    rw [hz i j x hij]
  rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply_same] at h

/-- A unit in the centre of `GL_ι(R)` commutes with every elementary matrix.
This is the bridge from group-theoretic centrality to the two steps above. -/
theorem commute_single_of_mem_center {u : (Matrix ι ι R)ˣ}
    (hu : u ∈ Subgroup.center (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j) (a : R) :
    (u : Matrix ι ι R) * Matrix.single i j a
      = Matrix.single i j a * (u : Matrix ι ι R) := by
  have h := Subgroup.mem_center_iff.mp hu (elementaryUnit i j hij a)
  have h' : (elementaryUnit i j hij a : Matrix ι ι R) * (u : Matrix ι ι R)
      = (u : Matrix ι ι R) * (elementaryUnit i j hij a : Matrix ι ι R) := by
    rw [← Units.val_mul, ← Units.val_mul, h]
  have hval : (elementaryUnit i j hij a : Matrix ι ι R)
      = 1 + Matrix.single i j a := rfl
  rw [hval, add_mul, mul_add, one_mul, mul_one] at h'
  exact (add_left_cancel h').symm

/-- **The centre of `GL_ι(R)` consists of central scalars.**  This is the
combination of the two printed steps. -/
theorem exists_central_scalar_of_mem_center (hcard : 1 < Fintype.card ι)
    (i₀ : ι) {u : (Matrix ι ι R)ˣ}
    (hu : u ∈ Subgroup.center (Matrix ι ι R)ˣ) :
    ∃ lam : R, (∀ x : R, lam * x = x * lam)
      ∧ (u : Matrix ι ι R) = Matrix.diagonal fun _ : ι ↦ lam := by
  have hcomm := commute_single_of_mem_center hu
  have hdiag : (u : Matrix ι ι R)
      = Matrix.diagonal fun _ : ι ↦ (u : Matrix ι ι R) i₀ i₀ :=
    eq_diagonal_of_commute_single hcard i₀ _ fun i j hij ↦ hcomm i j hij 1
  refine ⟨(u : Matrix ι ι R) i₀ i₀, fun x ↦ ?_, hdiag⟩
  refine commute_of_commute_single hcard _ (fun i j a hij ↦ ?_) x
  rw [← hdiag]
  exact hcomm i j hij a

/-- **Second endpoint of the manuscript's case split.**  At level `0` the full
congruence subgroup is the centre of `GL_ι(R)`. -/
theorem congruenceSubgroup_bot (hcard : 1 < Fintype.card ι) (i₀ : ι) :
    congruenceSubgroup ι (⊥ : TwoSidedIdeal R)
      = Subgroup.center (Matrix ι ι R)ˣ := by
  ext u
  constructor
  · rintro ⟨lam, hlam, hu⟩
    have hval : (u : Matrix ι ι R) = Matrix.diagonal fun _ : ι ↦ lam := by
      ext i j
      have h := hu i j
      rw [Matrix.sub_apply] at h
      have hz : (u : Matrix ι ι R) i j - Matrix.diagonal (fun _ : ι ↦ lam) i j = 0 := by
        simpa using h
      exact sub_eq_zero.mp hz
    have hcent : ∀ x : R, lam * x = x * lam := mem_relativeCenter_bot.mp hlam
    rw [Subgroup.mem_center_iff]
    intro v
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hval]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact (hcent ((v : Matrix ι ι R) i j)).symm
  · intro hu
    obtain ⟨lam, hcent, hval⟩ :=
      exists_central_scalar_of_mem_center hcard i₀ hu
    refine ⟨lam, mem_relativeCenter_bot.mpr hcent, fun i j ↦ ?_⟩
    rw [Matrix.sub_apply, hval, sub_self]
    exact TwoSidedIdeal.zero_mem _

/-- **Third printed step.**  If the central units of `R` are trivial then the
centre of `GL_ι(R)` is trivial.  The hypothesis is exactly the conclusion of
`BinaryLeavitt.central_units_trivial`. -/
theorem center_eq_bot_of_central_units_trivial (hcard : 1 < Fintype.card ι)
    (i₀ : ι) (hcentral : ∀ u : Rˣ, (∀ x : R, Commute (u : R) x) → (u : R) = 1) :
    Subgroup.center (Matrix ι ι R)ˣ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  obtain ⟨lam, hlam, hval⟩ := exists_central_scalar_of_mem_center hcard i₀ hu
  obtain ⟨mu, -, hvalinv⟩ := exists_central_scalar_of_mem_center hcard i₀
    (Subgroup.inv_mem _ hu)
  have hone : (Matrix.diagonal fun _ : ι ↦ lam * mu) = (1 : Matrix ι ι R) := by
    rw [← diagonal_const_mul_const lam mu, ← hval, ← hvalinv]
    exact u.mul_inv
  have hone' : (Matrix.diagonal fun _ : ι ↦ mu * lam) = (1 : Matrix ι ι R) := by
    rw [← diagonal_const_mul_const mu lam, ← hvalinv, ← hval]
    exact u.inv_mul
  have hlm : lam * mu = 1 := by
    have h : (Matrix.diagonal fun _ : ι ↦ lam * mu) i₀ i₀
        = (1 : Matrix ι ι R) i₀ i₀ := by rw [hone]
    rwa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  have hml : mu * lam = 1 := by
    have h : (Matrix.diagonal fun _ : ι ↦ mu * lam) i₀ i₀
        = (1 : Matrix ι ι R) i₀ i₀ := by rw [hone']
    rwa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  have hlam1 : lam = 1 :=
    hcentral ⟨lam, mu, hlm, hml⟩ fun x ↦ hlam x
  apply Units.ext
  rw [Units.val_one, hval, hlam1, Matrix.diagonal_one]

end Centre

/-! ### The assembly, conditional on Preusser's theorem alone -/

section Assembly

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Proposition `prop:simple`, reduced to one named citation.**

The hypothesis `hpreusser` is Preusser's normal-subgroup theorem in the shape
the printed proof quotes it: every normal subgroup of `EL_ι(R)` is sandwiched
between a relative elementary group and a full congruence subgroup of the same
level.  Every other ingredient of the printed proof is discharged here: the
case split on the level ideal uses simplicity of `R`, the level-`R` branch uses
`relativeElementary_top`, and the level-`0` branch uses `congruenceSubgroup_bot`
together with the centre computation.

The hypothesis is a leading explicit binder, so nothing about this statement is
asserted unconditionally. -/
theorem isSimpleGroup_of_preusser_sandwich (hn : 3 ≤ Fintype.card ι)
    [IsSimpleRing R]
    (hcentral : ∀ u : Rˣ, (∀ x : R, Commute (u : R) x) → (u : R) = 1)
    (hpreusser : ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
      ∃ I : TwoSidedIdeal R, relativeElementary ι I ≤ N ∧
        N.map (elementaryGroup ι R).subtype ≤ congruenceSubgroup ι I)
    (hne : Nontrivial (elementaryGroup ι R)) :
    IsSimpleGroup (elementaryGroup ι R) := by
  haveI := hne
  have hcard : 1 < Fintype.card ι := by omega
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  refine { eq_bot_or_eq_top_of_normal := fun N hN ↦ ?_ }
  obtain ⟨I, hIle, hIcong⟩ := hpreusser N hN
  rcases IsSimpleOrder.eq_bot_or_eq_top I with rfl | rfl
  · left
    rw [congruenceSubgroup_bot hcard i₀,
      center_eq_bot_of_central_units_trivial hcard i₀ hcentral] at hIcong
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxmap : (elementaryGroup ι R).subtype x ∈
        N.map (elementaryGroup ι R).subtype := ⟨x, hx, rfl⟩
    have hxone : (elementaryGroup ι R).subtype x = 1 := by
      simpa using hIcong hxmap
    exact (elementaryGroup ι R).subtype_injective hxone
  · right
    rw [relativeElementary_top] at hIle
    exact top_le_iff.mp hIle

end Assembly

end GroupApproximation

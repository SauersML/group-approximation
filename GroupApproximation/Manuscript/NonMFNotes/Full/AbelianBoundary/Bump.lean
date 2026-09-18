import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Slowly varying bump functions on finite quotients

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160),
torsion-free half (tex lines 2098--2150).  The proof uses
`f_n(y) = max {1 - ℓ_n(y)/n, 0}` on `K_n = q_n(Γ_1)`, where `ℓ_n` is word length.  It
needs two facts:

* `f_n(1) = 1`, and `f_n` vanishes off a ball of radius `n`;
* `|f_n(u y) - f_n(y)| ≤ |u|/n` (tex lines 2128--2131), so conjugating `D_n(a)` by
  `Λ_n(u)` moves it by at most `|θ(a)| |u| / n`.

Here the subgroup `Γ_1` can be any subgroup `H` of `G` with an enumeration `e : ℕ → H`
(no finite generation is needed).  At stage `n` the generating set is
`{1} ∪ {e_j^{±1} : j ≤ n}`, with balls `ball e n k`, and the bump is the average of the
`n + 1` layer indicators
`bump e n K y = (1 / (n+1)) · ∑_{k ≤ n} 1[y ∈ mk (ball e n k)]`
on `G ⧸ K`.  For each generator `t` it is `1/(n+1)`-Lipschitz, which gives the same
`O(1/n)` estimate as the printed `f_n`.
-/

namespace GroupApproximation.Full.NN06

noncomputable section

variable {G : Type*} [Group G]

/-- The stage-`n` generating set `{1} ∪ {e_j, e_j⁻¹ : j ≤ n}`. -/
def gens (e : ℕ → G) (n : ℕ) : Set G :=
  insert 1 (e '' {j | j ≤ n} ∪ (fun j => (e j)⁻¹) '' {j | j ≤ n})

theorem one_mem_gens (e : ℕ → G) (n : ℕ) : (1 : G) ∈ gens e n :=
  Set.mem_insert 1 _

theorem e_mem_gens (e : ℕ → G) {n j : ℕ} (hj : j ≤ n) : e j ∈ gens e n :=
  Set.mem_insert_of_mem _ (Or.inl ⟨j, hj, rfl⟩)

theorem inv_e_mem_gens (e : ℕ → G) {n j : ℕ} (hj : j ≤ n) : (e j)⁻¹ ∈ gens e n :=
  Set.mem_insert_of_mem _ (Or.inr ⟨j, hj, rfl⟩)

theorem gens_finite (e : ℕ → G) (n : ℕ) : (gens e n).Finite :=
  Set.Finite.insert 1 (Set.Finite.union (Set.Finite.image e (Set.finite_le_nat n))
    (Set.Finite.image (fun j => (e j)⁻¹) (Set.finite_le_nat n)))

theorem gens_subset (e : ℕ → G) {H : Subgroup G} (he : ∀ j, e j ∈ H) (n : ℕ) :
    gens e n ⊆ (H : Set G) := by
  rintro t (rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩)
  · exact H.one_mem
  · exact he j
  · exact H.inv_mem (he j)

/-- The ball of radius `k` for the stage-`n` generating set. -/
def ball (e : ℕ → G) (n : ℕ) : ℕ → Set G
  | 0 => {1}
  | k + 1 => Set.image2 (· * ·) (gens e n) (ball e n k)

theorem mul_mem_ball (e : ℕ → G) {n k : ℕ} {t c : G} (ht : t ∈ gens e n)
    (hc : c ∈ ball e n k) : t * c ∈ ball e n (k + 1) := by
  show t * c ∈ Set.image2 (· * ·) (gens e n) (ball e n k)
  exact Set.mem_image2_of_mem ht hc

theorem one_mem_ball (e : ℕ → G) (n k : ℕ) : (1 : G) ∈ ball e n k := by
  induction k with
  | zero =>
    show (1 : G) ∈ ({1} : Set G)
    exact Set.mem_singleton 1
  | succ k ih =>
    have h := mul_mem_ball e (one_mem_gens e n) ih
    rwa [one_mul] at h

theorem ball_subset_succ (e : ℕ → G) (n k : ℕ) : ball e n k ⊆ ball e n (k + 1) := by
  intro c hc
  have h := mul_mem_ball e (one_mem_gens e n) hc
  rwa [one_mul] at h

theorem ball_mono (e : ℕ → G) (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    ball e n k ⊆ ball e n l :=
  monotone_nat_of_le_succ (f := ball e n) (fun k => ball_subset_succ e n k) hkl

theorem ball_finite (e : ℕ → G) (n k : ℕ) : (ball e n k).Finite := by
  induction k with
  | zero =>
    show ({1} : Set G).Finite
    exact Set.finite_singleton 1
  | succ k ih =>
    show (Set.image2 (· * ·) (gens e n) (ball e n k)).Finite
    exact Set.Finite.image2 _ (gens_finite e n) ih

theorem ball_subset (e : ℕ → G) {H : Subgroup G} (he : ∀ j, e j ∈ H) (n k : ℕ) :
    ball e n k ⊆ (H : Set G) := by
  induction k with
  | zero =>
    intro c hc
    have hc' : c = 1 := hc
    rw [hc']
    exact H.one_mem
  | succ k ih =>
    intro c hc
    obtain ⟨t, ht, d, hd, rfl⟩ : c ∈ Set.image2 (· * ·) (gens e n) (ball e n k) := hc
    exact H.mul_mem (gens_subset e he n ht) (ih hd)

/-! ## Indicators and layers -/

/-- The real indicator function of a set. -/
def ind {α : Type*} (S : Set α) (y : α) : ℝ :=
  Set.indicator S (fun _ => (1 : ℝ)) y

theorem ind_of_mem {α : Type*} {S : Set α} {y : α} (h : y ∈ S) : ind S y = 1 :=
  Set.indicator_of_mem h _

theorem ind_of_notMem {α : Type*} {S : Set α} {y : α} (h : y ∉ S) : ind S y = 0 :=
  Set.indicator_of_notMem h _

theorem ind_nonneg {α : Type*} (S : Set α) (y : α) : 0 ≤ ind S y := by
  by_cases h : y ∈ S
  · exact (zero_le_one : (0 : ℝ) ≤ 1).trans_eq (ind_of_mem h).symm
  · exact le_of_eq (ind_of_notMem h).symm

theorem ind_le_one {α : Type*} (S : Set α) (y : α) : ind S y ≤ 1 := by
  by_cases h : y ∈ S
  · exact le_of_eq (ind_of_mem h)
  · exact (ind_of_notMem h).trans_le (zero_le_one : (0 : ℝ) ≤ 1)

/-- The `k`-th layer: the image of the ball of radius `k` in `G ⧸ K`. -/
def layer (e : ℕ → G) (n : ℕ) (K : Subgroup G) (k : ℕ) : Set (G ⧸ K) :=
  (QuotientGroup.mk : G → G ⧸ K) '' ball e n k

/-- `∑_{k ≤ n} 1[y ∈ layer k]`. -/
def bumpSum (e : ℕ → G) (n : ℕ) (K : Subgroup G) (y : G ⧸ K) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ind (layer e n K k) y

/-- The slowly varying bump `f_n` (tex line 2121). -/
def bump (e : ℕ → G) (n : ℕ) (K : Subgroup G) (y : G ⧸ K) : ℝ :=
  bumpSum e n K y / ((n : ℝ) + 1)

theorem bumpSum_one (e : ℕ → G) (n : ℕ) (K : Subgroup G) :
    bumpSum e n K (QuotientGroup.mk (1 : G)) = (n : ℝ) + 1 := by
  have h : ∀ k ∈ Finset.range (n + 1),
      ind (layer e n K k) (QuotientGroup.mk (1 : G) : G ⧸ K) = 1 :=
    fun k _ => ind_of_mem ⟨1, one_mem_ball e n k, rfl⟩
  have h2 := Finset.sum_eq_card_nsmul h
  rw [Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add_one] at h2
  exact h2

/-- `f_n(1) = 1`. -/
theorem bump_one (e : ℕ → G) (n : ℕ) (K : Subgroup G) :
    bump e n K (QuotientGroup.mk (1 : G)) = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  rw [bump, bumpSum_one]
  exact div_self hpos.ne'

/-- `f_n` vanishes off the image of the ball of radius `n`. -/
theorem bump_eq_zero (e : ℕ → G) {n : ℕ} {K : Subgroup G} {y : G ⧸ K}
    (h : ∀ c ∈ ball e n n, (QuotientGroup.mk c : G ⧸ K) ≠ y) : bump e n K y = 0 := by
  have hs : bumpSum e n K y = 0 := by
    show ∑ k ∈ Finset.range (n + 1), ind (layer e n K k) y = 0
    refine Finset.sum_eq_zero fun k hk => ind_of_notMem ?_
    rintro ⟨c, hc, hcy⟩
    have hkn : k ≤ n := by
      have hk' := Finset.mem_range.mp hk
      omega
    exact h c (ball_mono e n hkn hc) hcy
  rw [bump, hs, zero_div]

/-! ## The Lipschitz estimate -/

theorem ind_layer_le (e : ℕ → G) {n : ℕ} {K : Subgroup G} {t : G} (ht : t ∈ gens e n)
    (k : ℕ) (y : G ⧸ K) :
    ind (layer e n K k) y ≤ ind (layer e n K (k + 1)) (t • y) := by
  by_cases hy : y ∈ layer e n K k
  · obtain ⟨c, hc, hcy⟩ : y ∈ (QuotientGroup.mk : G → G ⧸ K) '' ball e n k := hy
    have hmem : t • y ∈ layer e n K (k + 1) := by
      refine ⟨t * c, mul_mem_ball e ht hc, ?_⟩
      have h1 : t • y = t • (QuotientGroup.mk c : G ⧸ K) := by rw [hcy]
      exact h1.symm
    exact le_of_eq ((ind_of_mem ⟨c, hc, hcy⟩).trans (ind_of_mem hmem).symm)
  · exact (ind_of_notMem hy).trans_le (ind_nonneg _ _)

theorem bumpSum_le_smul (e : ℕ → G) {n : ℕ} {K : Subgroup G} {t : G} (ht : t ∈ gens e n)
    (y : G ⧸ K) : bumpSum e n K y ≤ bumpSum e n K (t • y) + 1 := by
  have h1 : bumpSum e n K y ≤
      ∑ k ∈ Finset.range (n + 1), ind (layer e n K (k + 1)) (t • y) :=
    Finset.sum_le_sum fun k _ => ind_layer_le e ht k y
  have h2 : ∑ k ∈ Finset.range (n + 1 + 1), ind (layer e n K k) (t • y) =
      ∑ k ∈ Finset.range (n + 1), ind (layer e n K (k + 1)) (t • y) +
        ind (layer e n K 0) (t • y) :=
    Finset.sum_range_succ' (fun k => ind (layer e n K k) (t • y)) (n + 1)
  have h3 : ∑ k ∈ Finset.range (n + 1 + 1), ind (layer e n K k) (t • y) =
      bumpSum e n K (t • y) + ind (layer e n K (n + 1)) (t • y) :=
    Finset.sum_range_succ (fun k => ind (layer e n K k) (t • y)) (n + 1)
  have h4 := ind_le_one (layer e n K (n + 1)) (t • y)
  have h5 := ind_nonneg (layer e n K 0) (t • y)
  linarith

/-- **The Lipschitz estimate** (tex lines 2128--2131): translating by a generator whose
inverse is also a generator moves the bump by at most `1/(n+1)`. -/
theorem abs_bump_smul_sub_le (e : ℕ → G) {n : ℕ} {K : Subgroup G} {t : G}
    (ht : t ∈ gens e n) (ht' : t⁻¹ ∈ gens e n) (y : G ⧸ K) :
    |bump e n K (t • y) - bump e n K y| ≤ 1 / ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  have hA := bumpSum_le_smul e ht y
  have hB : bumpSum e n K (t • y) ≤ bumpSum e n K y + 1 := by
    have h := bumpSum_le_smul e ht' (t • y)
    rwa [inv_smul_smul] at h
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · rw [bump, bump, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  · rw [bump, bump, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- For an enumeration of `H`, eventually every `h ∈ H` and its inverse are generators. -/
theorem mem_gens_of_le (e : ℕ → G) {j n : ℕ} (hj : j ≤ n) :
    e j ∈ gens e n ∧ (e j)⁻¹ ∈ gens e n :=
  ⟨e_mem_gens e hj, inv_e_mem_gens e hj⟩

end

#audit_axioms ball_finite
#audit_axioms ball_subset
#audit_axioms bump_one
#audit_axioms bump_eq_zero
#audit_axioms abs_bump_smul_sub_le

end GroupApproximation.Full.NN06

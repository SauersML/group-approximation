/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group

/-!
# A Baumslag--Remeslennikov lemma for families (KMS, Lemma lBRG)

Abstract group theory behind Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4,
Lemma `lBRG`, specialised to `p = 2`.

Let `a, a'` be commuting elements of a group `G` and `A : ι → G` a family with
* `Commute (A w) (A w')` for all `w, w'`,
* `Commute (A w) (a⁻¹ * A w' * a)` for all `w, w'`,
* `a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹` for all `w`.

Then all conjugates `(a^p a'^q)⁻¹ * A w * (a^p a'^q)` pairwise commute (`BR.conj_commute`).

Proof. Put `D w k = a^{-k} A_w a^k`. Conjugation by `a'` sends `D w k` to
`D w (k-1) * (D w k)⁻¹`. Induction on the distance `|k - l|` shows that all `D w k`
commute. Their closure `N` is therefore abelian and stable under conjugation by `a'`, and
every conjugate of `A w` by `a^p a'^q` is an `a'`-conjugate of an element of `N`.
-/

namespace GroupApproximation.Full.Kharlampovich
namespace KMS
namespace BR

variable {G : Type*} [Group G]

/-- Conjugation preserves commuting. -/
theorem commute_conj {x y : G} (h : Commute x y) (g : G) :
    Commute (g⁻¹ * x * g) (g⁻¹ * y * g) := by
  have e : x * y = y * x := h.eq
  show g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * y * g * (g⁻¹ * x * g)
  calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by
        simp only [mul_assoc, mul_inv_cancel_left]
    _ = g⁻¹ * (y * x) * g := by rw [e]
    _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by
        simp only [mul_assoc, mul_inv_cancel_left]

/-- Elements of the closures of two elementwise commuting sets commute. -/
theorem commute_of_mem_closure {k₁ k₂ : Set G} (h : ∀ x ∈ k₁, ∀ y ∈ k₂, Commute x y)
    {x y : G} (hx : x ∈ Subgroup.closure k₁) (hy : y ∈ Subgroup.closure k₂) :
    Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx' =>
    induction hy using Subgroup.closure_induction with
    | mem y hy' => exact h x hx' y hy'
    | one => exact Commute.one_right x
    | mul _ _ _ _ h₁ h₂ => exact h₁.mul_right h₂
    | inv _ _ h₁ => exact h₁.inv_right
  | one => exact Commute.one_left y
  | mul _ _ _ _ h₁ h₂ => exact h₁.mul_left h₂
  | inv _ _ h₁ => exact h₁.inv_left

variable {ι : Type*} (A : ι → G) (a a' : G)

/-- `D w k = a^{-k} * A w * a^k`. -/
def D (w : ι) (k : ℤ) : G := (a ^ k)⁻¹ * A w * a ^ k

theorem D_zero (w : ι) : D A a w 0 = A w := by
  rw [D, zpow_zero, inv_one, one_mul, mul_one]

theorem D_conj (w : ι) (k i : ℤ) : (a ^ i)⁻¹ * D A a w k * a ^ i = D A a w (k + i) := by
  simp only [D, zpow_add, mul_inv_rev, mul_assoc]

theorem D_shift {w w' : ι} {k l : ℤ} (h : Commute (D A a w k) (D A a w' l)) (i : ℤ) :
    Commute (D A a w (k + i)) (D A a w' (l + i)) := by
  rw [← D_conj A a w k i, ← D_conj A a w' l i]
  exact commute_conj h _

theorem D_comm0 (hC0 : ∀ w w', Commute (A w) (A w')) (w w' : ι) (k : ℤ) :
    Commute (D A a w k) (D A a w' k) := by
  have h := D_shift A a (w := w) (w' := w') (k := 0) (l := 0)
    (by rw [D_zero, D_zero]; exact hC0 w w') k
  rwa [zero_add] at h

theorem D_comm1 (hC : ∀ w w', Commute (A w) (a⁻¹ * A w' * a)) (w w' : ι) (k : ℤ) :
    Commute (D A a w k) (D A a w' (k + 1)) := by
  have h1 : Commute (D A a w 0) (D A a w' 1) := by
    rw [D_zero, D, zpow_one]
    exact hC w w'
  have h := D_shift A a h1 k
  rwa [zero_add, add_comm 1 k] at h

/-- Conjugation by `a'` acts on the `D`'s as `D w k ↦ D w (k-1) * (D w k)⁻¹`. -/
theorem D_conj_a' (haa' : Commute a a')
    (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹) (w : ι) (j : ℤ) :
    a' * D A a w j * a'⁻¹ = D A a w (j - 1) * (D A a w j)⁻¹ := by
  have hc : a' * (a ^ j)⁻¹ = (a ^ j)⁻¹ * a' := ((haa'.zpow_left j).inv_left).eq.symm
  have hc2 : a ^ j * a'⁻¹ = a'⁻¹ * a ^ j := ((haa'.zpow_left j).inv_right).eq
  calc a' * D A a w j * a'⁻¹ = (a' * (a ^ j)⁻¹) * A w * (a ^ j * a'⁻¹) := by
        simp only [D, mul_assoc]
    _ = (a ^ j)⁻¹ * (a' * A w * a'⁻¹) * a ^ j := by
        rw [hc, hc2]
        simp only [mul_assoc]
    _ = (a ^ j)⁻¹ * (a * A w * a⁻¹ * (A w)⁻¹) * a ^ j := by rw [hE w]
    _ = D A a w (j - 1) * (D A a w j)⁻¹ := by
        simp only [D]
        group

section Dist

variable (hC0 : ∀ w w', Commute (A w) (A w'))
  (hC : ∀ w w', Commute (A w) (a⁻¹ * A w' * a)) (haa' : Commute a a')
  (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹)

include hC0 hC haa' hE

/-- The `D`'s at distance at most `m` commute. -/
theorem D_commute_dist (m : ℕ) :
    ∀ (w w' : ι) (k l : ℤ), k ≤ l → l ≤ k + m → Commute (D A a w k) (D A a w' l) := by
  induction m with
  | zero =>
    intro w w' k l h1 h2
    obtain rfl : l = k := by omega
    exact D_comm0 A a hC0 w w' _
  | succ m ih =>
    intro w w' k l h1 h2
    by_cases h3 : l ≤ k + m
    · exact ih w w' k l h1 h3
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · have h4 : l = k + 1 := by omega
        subst h4
        exact D_comm1 A a hC w w' k
      · have key : Commute (D A a w (-1)) (D A a w' (m : ℤ)) := by
          have c2 : Commute (D A a w 0) (D A a w' (m : ℤ)) :=
            ih w w' 0 (m : ℤ) (by omega) (by omega)
          have hconj := commute_conj c2 a'⁻¹
          rw [inv_inv, D_conj_a' A a a' haa' hE, D_conj_a' A a a' haa' hE, zero_sub] at hconj
          have c1 : Commute (D A a w 0) (D A a w' ((m : ℤ) - 1)) :=
            ih w w' 0 ((m : ℤ) - 1) (by omega) (by omega)
          have c3 : Commute (D A a w (-1)) (D A a w' ((m : ℤ) - 1)) :=
            ih w w' (-1) ((m : ℤ) - 1) (by omega) (by omega)
          have h4 := hconj.mul_left (c1.mul_right c2.inv_right)
          rw [inv_mul_cancel_right] at h4
          have h5 := c3.inv_right.mul_right h4
          rw [inv_mul_cancel_left] at h5
          exact Commute.inv_right_iff.mp h5
        have h6 := D_shift A a key (k + 1)
        rw [show (-1 : ℤ) + (k + 1) = k by omega, show (m : ℤ) + (k + 1) = l by omega] at h6
        exact h6

/-- All the `D`'s commute. -/
theorem D_commute (w w' : ι) (k l : ℤ) : Commute (D A a w k) (D A a w' l) := by
  rcases le_total k l with h | h
  · exact D_commute_dist A a a' hC0 hC haa' hE (l - k).toNat w w' k l h
      (by omega)
  · exact (D_commute_dist A a a' hC0 hC haa' hE (k - l).toNat w' w l k h
      (by omega)).symm

end Dist

/-- The subgroup generated by all the `D`'s. -/
abbrev brN : Subgroup G := Subgroup.closure (Set.range fun x : ι × ℤ => D A a x.1 x.2)

theorem conj_a'_mem (haa' : Commute a a')
    (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹) {x : G} (hx : x ∈ brN A a) :
    a' * x * a'⁻¹ ∈ brN A a := by
  induction hx using Subgroup.closure_induction with
  | mem x hx' =>
    obtain ⟨⟨w, k⟩, rfl⟩ := hx'
    show a' * D A a w k * a'⁻¹ ∈ brN A a
    rw [D_conj_a' A a a' haa' hE]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(w, k - 1), rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨(w, k), rfl⟩))
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : a' * (x * y) * a'⁻¹ = (a' * x * a'⁻¹) * (a' * y * a'⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : a' * x⁻¹ * a'⁻¹ = (a' * x * a'⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem pow_conj_mem (haa' : Commute a a')
    (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹) (w : ι) (p : ℤ) (n : ℕ) :
    a' ^ n * D A a w p * (a' ^ n)⁻¹ ∈ brN A a := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul, inv_one, mul_one]
    exact Subgroup.subset_closure ⟨(w, p), rfl⟩
  | succ n ih =>
    have e : a' ^ (n + 1) * D A a w p * (a' ^ (n + 1))⁻¹
        = a' * (a' ^ n * D A a w p * (a' ^ n)⁻¹) * a'⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [e]
    exact conj_a'_mem A a a' haa' hE ih

theorem zpow_conj_mem (haa' : Commute a a')
    (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹) (w : ι) (p e : ℤ) (he : 0 ≤ e) :
    a' ^ e * D A a w p * (a' ^ e)⁻¹ ∈ brN A a := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he
  rw [zpow_natCast]
  exact pow_conj_mem A a a' haa' hE w p n

theorem conj_eq (w : ι) (p q e : ℤ) :
    (a ^ p * a' ^ q)⁻¹ * A w * (a ^ p * a' ^ q)
      = (a' ^ e)⁻¹ * (a' ^ (e - q) * D A a w p * (a' ^ (e - q))⁻¹) * a' ^ e := by
  calc (a ^ p * a' ^ q)⁻¹ * A w * (a ^ p * a' ^ q) = (a' ^ q)⁻¹ * D A a w p * a' ^ q := by
        simp only [D, mul_inv_rev, mul_assoc]
    _ = (a' ^ e)⁻¹ * (a' ^ (e - q) * D A a w p * (a' ^ (e - q))⁻¹) * a' ^ e := by
        group

/-- **Lemma lBRG** (KMS, `p = 2`, family version): the conjugates of the `A w` by elements
`a^p a'^q` pairwise commute. -/
theorem conj_commute (hC0 : ∀ w w', Commute (A w) (A w'))
    (hC : ∀ w w', Commute (A w) (a⁻¹ * A w' * a)) (haa' : Commute a a')
    (hE : ∀ w, a' * A w * a'⁻¹ = a * A w * a⁻¹ * (A w)⁻¹) (w w' : ι) (p q p' q' : ℤ) :
    Commute ((a ^ p * a' ^ q)⁻¹ * A w * (a ^ p * a' ^ q))
      ((a ^ p' * a' ^ q')⁻¹ * A w' * (a ^ p' * a' ^ q')) := by
  have hgen : ∀ x ∈ Set.range (fun x : ι × ℤ => D A a x.1 x.2),
      ∀ y ∈ Set.range (fun x : ι × ℤ => D A a x.1 x.2), Commute x y := by
    rintro _ ⟨⟨v, k⟩, rfl⟩ _ ⟨⟨v', l⟩, rfl⟩
    exact D_commute A a a' hC0 hC haa' hE v v' k l
  rw [conj_eq A a a' w p q ((q.natAbs : ℤ) + q'.natAbs),
    conj_eq A a a' w' p' q' ((q.natAbs : ℤ) + q'.natAbs)]
  exact commute_conj (commute_of_mem_closure hgen
    (zpow_conj_mem A a a' haa' hE w p _ (by omega))
    (zpow_conj_mem A a a' haa' hE w' p' _ (by omega))) _

end BR
end KMS
end GroupApproximation.Full.Kharlampovich

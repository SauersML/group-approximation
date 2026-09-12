import GroupApproximation.CharClass.OddPTotalInterface

/-!
# Grading lemmas for packaging the reduced powers

Coefficient-generic facts about `TotalHOf K X = ⨁ₙ Hⁿ(X; K)` used by
`OddPTotalPackaging.lean`: components of homogeneous classes, scalars through the grading and
through pullback, the expansion of a class over a finite set of degrees, the projection onto one
degree, and the arithmetic of the degrees `d + 2s(p − 1)` (`GoodDeg`).
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

section Grading

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- The component of a homogeneous class, as a `dite` on the degrees. -/
theorem component_of_eq_dite {a : ℕ} (e : ℕ) (c : TotalPieceOf K X a) :
    TotalHOf.component K X e (TotalHOf.of K X a c) = if h : a = e then cohCast h c else 0 := by
  by_cases h : a = e
  · subst h
    rw [dif_pos rfl, TotalHOf.component_of, cohCast_rfl]
  · rw [dif_neg h]
    exact TotalHOf.component_of_ne K X (fun h' => h h'.symm) c

theorem of_smul (n : ℕ) (s : K) (c : TotalPieceOf K X n) :
    TotalHOf.of K X n (s • c) = s • TotalHOf.of K X n c :=
  (DirectSum.lof K ℕ (fun n : ℕ => TotalPieceOf K X n) n).map_smul s c

theorem component_smul (n : ℕ) (s : K) (x : TotalHOf K X) :
    TotalHOf.component K X n (s • x) = s • TotalHOf.component K X n x :=
  DirectSum.smul_apply s x n

theorem isEven_smul (s : K) {x : TotalHOf K X} (hx : TotalHOf.IsEven x) :
    TotalHOf.IsEven (s • x) := by
  intro n hn
  rw [component_smul, hx n hn, smul_zero]

theorem smul_mul_left (s : K) (x y : TotalHOf K X) : (s • x) * y = s • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [smul_zero, zero_mul]
  | of a c =>
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero, smul_zero]
    | of b d =>
      show (s • TotalHOf.of K X a c) * TotalHOf.of K X b d
        = s • (TotalHOf.of K X a c * TotalHOf.of K X b d)
      rw [← of_smul, ← TotalHOf.of_mul, ← TotalHOf.of_mul, cup_smul_left, of_smul]
    | add y z hy hz => rw [mul_add, mul_add, hy, hz, smul_add]
  | add x x' hx hx' => rw [smul_add, add_mul, add_mul, hx, hx', smul_add]

theorem mul_smul_right (s : K) (x y : TotalHOf K X) : x * (s • y) = s • (x * y) := by
  induction y using DirectSum.induction_on with
  | zero => simp only [smul_zero, mul_zero]
  | of b d =>
    induction x using DirectSum.induction_on with
    | zero => simp only [zero_mul, smul_zero]
    | of a c =>
      show TotalHOf.of K X a c * (s • TotalHOf.of K X b d)
        = s • (TotalHOf.of K X a c * TotalHOf.of K X b d)
      rw [← of_smul, ← TotalHOf.of_mul, ← TotalHOf.of_mul, cup_smul_right, of_smul]
    | add x x' hx hx' => rw [add_mul, add_mul, hx, hx', smul_add]
  | add y y' hy hy' => rw [smul_add, mul_add, mul_add, hy, hy', smul_add]

theorem map_smul' {Y : TopCat.{0}} (f : X ⟶ Y) (s : K) (x : TotalHOf K Y) :
    TotalHOf.map K f (s • x) = s • TotalHOf.map K f x := by
  induction x using DirectSum.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | of a c =>
    show TotalHOf.map K f (s • TotalHOf.of K Y a c) = s • TotalHOf.map K f (TotalHOf.of K Y a c)
    rw [← of_smul, TotalHOf.map_of, TotalHOf.map_of, pull_smul, of_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Components commute with pullback. -/
theorem component_map {Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (x : TotalHOf K Y) :
    TotalHOf.component K X n (TotalHOf.map K f x) = pull f n (TotalHOf.component K Y n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, pull_zero]
  | of a c =>
    show TotalHOf.component K X n (TotalHOf.map K f (TotalHOf.of K Y a c))
      = pull f n (TotalHOf.component K Y n (TotalHOf.of K Y a c))
    rw [TotalHOf.map_of, component_of_eq_dite, component_of_eq_dite]
    by_cases h : a = n
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
      rfl
    · rw [dif_neg h, dif_neg h, pull_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, pull_add]

/-- A class is the sum of its components over any finite set of degrees outside which it
vanishes. -/
theorem eq_sum_components (x : TotalHOf K X) (T : Finset ℕ)
    (hT : ∀ e, e ∉ T → TotalHOf.component K X e x = 0) :
    x = ∑ e ∈ T, TotalHOf.of K X e (TotalHOf.component K X e x) := by
  apply DFinsupp.ext
  intro e
  show TotalHOf.component K X e x
    = TotalHOf.component K X e (∑ e' ∈ T, TotalHOf.of K X e' (TotalHOf.component K X e' x))
  rw [map_sum]
  simp only [component_of_eq_dite]
  by_cases he : e ∈ T
  · rw [Finset.sum_eq_single e]
    · rw [dif_pos rfl, cohCast_rfl]
    · intro b _ hb
      rw [dif_neg hb]
    · intro h
      exact absurd he h
  · rw [Finset.sum_eq_zero fun b hb => dif_neg (fun h => he (h ▸ hb))]
    exact hT e he

/-- The projection onto one degree. -/
def projDeg (e : ℕ) : TotalHOf K X →+ TotalHOf K X :=
  (TotalHOf.of K X e).comp (TotalHOf.component K X e)

theorem projDeg_apply (e : ℕ) (x : TotalHOf K X) :
    projDeg K X e x = TotalHOf.of K X e (TotalHOf.component K X e x) :=
  rfl

theorem projDeg_of (e a : ℕ) (c : TotalPieceOf K X a) :
    projDeg K X e (TotalHOf.of K X a c) = if a = e then TotalHOf.of K X a c else 0 := by
  rw [projDeg_apply, component_of_eq_dite]
  by_cases h : a = e
  · rw [dif_pos h, if_pos h, TotalHOf.of_cohCast]
  · rw [dif_neg h, if_neg h, map_zero]

theorem projDeg_smul (e : ℕ) (s : K) (x : TotalHOf K X) :
    projDeg K X e (s • x) = s • projDeg K X e x := by
  rw [projDeg_apply, projDeg_apply, component_smul, of_smul]

theorem projDeg_map {Y : TopCat.{0}} (f : X ⟶ Y) (e : ℕ) (x : TotalHOf K Y) :
    projDeg K X e (TotalHOf.map K f x) = TotalHOf.map K f (projDeg K Y e x) := by
  rw [projDeg_apply, projDeg_apply, component_map, TotalHOf.map_of]

end Grading

/-! ## The degrees `d + 2s(p − 1)` -/

theorem goodDeg_add {p a b e₁ e₂ : ℕ} (h₁ : GoodDeg p a e₁) (h₂ : GoodDeg p b e₂) :
    GoodDeg p (a + b) (e₁ + e₂) := by
  obtain ⟨h₁le, h₁m⟩ := h₁
  obtain ⟨h₂le, h₂m⟩ := h₂
  refine ⟨by omega, ?_⟩
  have h : e₁ + e₂ - (a + b) = (e₁ - a) + (e₂ - b) := by omega
  rw [h, Nat.add_mod, h₁m, h₂m, Nat.zero_add, Nat.zero_mod]

theorem goodDeg_self_add (p a s : ℕ) : GoodDeg p a (a + 2 * s * (p - 1)) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_sub_cancel_left, show 2 * s * (p - 1) = 2 * (p - 1) * s by ring]
  exact Nat.mul_mod_right _ _

theorem exists_of_goodDeg {p a e : ℕ} (hp : 2 ≤ p) (he : e ≤ p * a) (h : GoodDeg p a e) :
    ∃ s, 2 * s ≤ a ∧ e = a + 2 * s * (p - 1) := by
  obtain ⟨hle, hm⟩ := h
  obtain ⟨m, hmeq⟩ := Nat.dvd_of_mod_eq_zero hm
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : 0 < q := by omega
  simp only [Nat.add_sub_cancel] at hmeq ⊢
  have heq : e = 2 * q * m + a := Nat.eq_add_of_sub_eq hle hmeq
  refine ⟨m, ?_, by rw [heq]; ring⟩
  have h2 : q * (2 * m) ≤ q * a := by
    have : (q + 1) * a = a + q * a := by ring
    nlinarith
  exact Nat.le_of_mul_le_mul_left h2 hq

theorem sub_goodDeg {p a s : ℕ} (hp : 1 ≤ p) (hs : 2 * s ≤ a) :
    p * a - (a + 2 * s * (p - 1)) = (a - 2 * s) * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, a = 2 * s + t := ⟨a - 2 * s, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  have h : (q + 1) * (2 * s + t) = (2 * s + t + 2 * s * q) + t * q := by ring
  rw [h, Nat.add_sub_cancel_left]

theorem goodDeg_le {p a s : ℕ} (hp : 1 ≤ p) (hs : 2 * s ≤ a) : a + 2 * s * (p - 1) ≤ p * a := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : 2 * s * q ≤ a * q := Nat.mul_le_mul_right q hs
  nlinarith

theorem goodDeg_inj {p a s s' : ℕ} (hp : 2 ≤ p)
    (h : a + 2 * s * (p - 1) = a + 2 * s' * (p - 1)) : s = s' := by
  have h' : 2 * (p - 1) * s = 2 * (p - 1) * s' := by
    have := Nat.add_left_cancel h
    calc 2 * (p - 1) * s = 2 * s * (p - 1) := by ring
      _ = 2 * s' * (p - 1) := this
      _ = 2 * (p - 1) * s' := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h'

end

end OddPTotal

#audit_axioms OddPTotal.component_of_eq_dite
#audit_axioms OddPTotal.smul_mul_left
#audit_axioms OddPTotal.mul_smul_right
#audit_axioms OddPTotal.component_map
#audit_axioms OddPTotal.eq_sum_components
#audit_axioms OddPTotal.projDeg_of
#audit_axioms OddPTotal.projDeg_map
#audit_axioms OddPTotal.goodDeg_add
#audit_axioms OddPTotal.exists_of_goodDeg
#audit_axioms OddPTotal.sub_goodDeg
#audit_axioms OddPTotal.goodDeg_inj

end CharClass
end GroupApproximation

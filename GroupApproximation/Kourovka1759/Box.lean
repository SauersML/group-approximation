import GroupApproximation.Kourovka1759.Statement

/-!
# Boxes, canonical maps and class transpositions

A *box* is a residue class `r + mℤ` with `0 ≤ r < m`. The *canonical map* between two boxes
sends `r₁ + t m₁` to `r₂ + t m₂`. For disjoint boxes the swap built from the two canonical maps
is a class transposition.
-/

namespace GroupApproximation.Kourovka1759

/-- The residue class `r + mℤ`, normalized by `0 ≤ r < m`. -/
@[ext] structure Box where
  r : ℤ
  m : ℤ
  hr : 0 ≤ r
  hrm : r < m

namespace Box

theorem m_pos (B : Box) : 0 < B.m := lt_of_le_of_lt B.hr B.hrm

theorem m_ne (B : Box) : B.m ≠ 0 := B.m_pos.ne'

/-- `n` lies in the box `B`. -/
def Mem (B : Box) (n : ℤ) : Prop := n % B.m = B.r

theorem elt_div (B : Box) (t : ℤ) : (B.r + t * B.m) / B.m = t := by
  rw [Int.add_mul_ediv_right _ _ B.m_ne, Int.ediv_eq_zero_of_lt B.hr B.hrm, zero_add]

theorem elt_mem (B : Box) (t : ℤ) : B.Mem (B.r + t * B.m) := by
  unfold Mem
  rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt B.hr B.hrm]

theorem eq_of_mem {B : Box} {n : ℤ} (h : B.Mem n) : B.r + n / B.m * B.m = n := by
  have := Int.emod_add_ediv_mul n B.m
  unfold Mem at h
  rw [h] at this
  exact this

theorem mem_iff (B : Box) (n : ℤ) : B.Mem n ↔ ∃ t, n = B.r + t * B.m :=
  ⟨fun h => ⟨n / B.m, (eq_of_mem h).symm⟩, fun ⟨t, ht⟩ => ht ▸ B.elt_mem t⟩

/-- The whole of `ℤ` as a box. -/
def univ : Box := ⟨0, 1, le_refl _, zero_lt_one⟩

theorem univ_mem (n : ℤ) : univ.Mem n := by
  unfold Mem univ; simp

/-- The `j`-th child of `ℤ` under the `k`-split: the class `j + kℤ`. -/
def child (k : ℕ) (j : Fin k) : Box :=
  ⟨j, k, by positivity, by exact_mod_cast j.isLt⟩

/-- `place N X` is the box `X` transported into `N` by the canonical map `ℤ → N`. -/
def place (N X : Box) : Box :=
  ⟨N.r + X.r * N.m, X.m * N.m, by
    have := N.hr; have := X.hr; have := N.m_pos; positivity, by
    have h1 := N.hrm; have h2 := X.hrm; have h3 := N.m_pos
    nlinarith⟩

@[simp] theorem place_r (N X : Box) : (place N X).r = N.r + X.r * N.m := rfl
@[simp] theorem place_m (N X : Box) : (place N X).m = X.m * N.m := rfl

theorem place_elt (N X : Box) (t : ℤ) :
    (place N X).r + t * (place N X).m = N.r + (X.r + t * X.m) * N.m := by
  simp only [place_r, place_m]; ring

theorem place_assoc (N M X : Box) : place N (place M X) = place (place N M) X := by
  ext <;> simp only [place_r, place_m] <;> ring

@[simp] theorem place_univ (N : Box) : place N univ = N := by
  ext <;> simp [place, univ]

@[simp] theorem univ_place (X : Box) : place univ X = X := by
  ext <;> simp [place, univ]

theorem mem_place {N X : Box} {n : ℤ} :
    (place N X).Mem n ↔ N.Mem n ∧ X.Mem (n / N.m) := by
  constructor
  · rintro h
    obtain ⟨t, rfl⟩ := ((place N X).mem_iff n).1 h
    rw [place_elt]
    refine ⟨N.elt_mem _, ?_⟩
    rw [N.elt_div]; exact X.elt_mem t
  · rintro ⟨h1, h2⟩
    rw [mem_iff] at h2 ⊢
    obtain ⟨t, ht⟩ := h2
    refine ⟨t, ?_⟩
    rw [place_elt, ← ht, eq_of_mem h1]

theorem place_mem_of {N X : Box} {n : ℤ} (h : (place N X).Mem n) : N.Mem n :=
  (mem_place.1 h).1

/-- Two boxes are disjoint. -/
def Disj (A B : Box) : Prop := ∀ n, A.Mem n → B.Mem n → False

theorem Disj.symm {A B : Box} (h : A.Disj B) : B.Disj A := fun n hb ha => h n ha hb

theorem disj_place {N X Y : Box} (h : X.Disj Y) : (place N X).Disj (place N Y) :=
  fun _ hx hy => h _ (mem_place.1 hx).2 (mem_place.1 hy).2

theorem disj_place_of {N N' X Y : Box} (h : N.Disj N') : (place N X).Disj (place N' Y) :=
  fun _ hx hy => h _ (place_mem_of hx) (place_mem_of hy)

theorem child_disj (k : ℕ) {i j : Fin k} (hij : i ≠ j) : (child k i).Disj (child k j) := by
  intro n hi hj
  unfold Mem child at hi hj
  simp only at hi hj
  apply hij
  ext
  exact_mod_cast hi.symm.trans hj

end Box

open Equiv

/-- `g` maps the box `A` onto the box `B` canonically: `A.r + t A.m ↦ B.r + t B.m`. -/
def CanonOn (g : Perm ℤ) (A B : Box) : Prop := ∀ t : ℤ, g (A.r + t * A.m) = B.r + t * B.m

namespace CanonOn

theorem one (A : Box) : CanonOn 1 A A := fun _ => rfl

theorem comp {g h : Perm ℤ} {A B C : Box} (hg : CanonOn g A B) (hh : CanonOn h B C) :
    CanonOn (h * g) A C := fun t => by
  rw [Perm.mul_apply, hg t, hh t]

theorem inv {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) : CanonOn g⁻¹ B A := fun t => by
  rw [← hg t, Perm.coe_inv, Equiv.symm_apply_apply]

theorem place {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) (X : Box) :
    CanonOn g (Box.place A X) (Box.place B X) := fun t => by
  rw [Box.place_elt, Box.place_elt, hg]

theorem mem {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) {n : ℤ} (hn : A.Mem n) :
    B.Mem (g n) := by
  rw [← A.eq_of_mem hn, hg]; exact B.elt_mem _

theorem apply {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) {n : ℤ} (hn : A.Mem n) :
    g n = B.r + n / A.m * B.m := by
  conv_lhs => rw [← A.eq_of_mem hn]
  exact hg _

/-- A permutation fixing every point of `A` maps `A` canonically onto itself. -/
theorem of_fix {g : Perm ℤ} {A : Box} (h : ∀ n, A.Mem n → g n = n) : CanonOn g A A :=
  fun t => h _ (A.elt_mem t)

/-- Two permutations canonical on the same box with the same target agree on it. -/
theorem agree {g h : Perm ℤ} {A B : Box} (hg : CanonOn g A B) (hh : CanonOn h A B)
    {n : ℤ} (hn : A.Mem n) : g n = h n := by
  rw [hg.apply hn, hh.apply hn]

end CanonOn

end GroupApproximation.Kourovka1759

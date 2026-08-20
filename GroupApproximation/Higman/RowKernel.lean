import GroupApproximation.Higman.RowBasis

/-!
# The row subgroup is the kernel of the `c`-exponent, and its positive half

Higman's later examples (3.6, 3.7) need two things about `F₀ = ⟨b, c⟩` that
`Higman.Row` and `Higman.RowBasis` do not yet say.

The first is that the row subgroup is *exactly* the kernel of the `c`-exponent
homomorphism.  One inclusion is a computation; the other is the "collecting"
statement that every word can be written as a row element times a power of
`c`, which is proved here as a subgroup argument: the set of words that can be
so written contains `b` and `c` and is closed under products and inverses,
because the row is normalized by `c` (`conj_row`).  This is the fact that
converts *any* hypothesis about the `c`-exponent into membership in the row,
and every later argument about an endomorphism of `F₀` starts with it.

The second is the *positive half* of the row,

    HalfRow = ⟨bᵢ : i ≥ 0⟩ ,

together with the criterion for membership in it.  Because the `bᵢ` are a free
basis (`Higman.RowBasis`), membership in the half row is a statement about
*letters*: `basisHom W ∈ HalfRow` exactly when every letter of `W` is a
nonnegative index, and that is detected by the retraction `killNeg` that
deletes the negative letters.  Higman's Example 3.7 --- the half row is benign
--- is proved from exactly this criterion, and nothing else about `HalfRow` is
ever needed.

## Contents

* `expHom` --- the `c`-exponent, as a homomorphism to `Multiplicative ℤ`.
* `conj_row`, `conj_mem_Row` --- the row is normalized by `c`.
* `splitSub_eq_top` --- every word is a row element times a power of `c`.
* `Row_eq_ker` --- `Row = ker expHom`.
* `posSub`, `killNeg`, `mem_posSub_iff` --- the positive part of `FreeGroup ℤ`.
* `HalfRow`, `mem_halfRow_iff`, `halfRow_eq_closure` --- the positive half of
  the row and the two forms of membership in it.
-/

namespace GroupApproximation
namespace Higman
namespace Row

/-! ## 0.  The two generators -/

/-- `Fin 2` has two elements.  Used to check statements on the generators of
`F₀` without invoking `fin_cases`. -/
theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/-! ## 1.  The `c`-exponent -/

/-- The `c`-exponent homomorphism: `b ↦ 0`, `c ↦ 1`. -/
def expHom : F₀ →* Multiplicative ℤ :=
  FreeGroup.lift (fun i : Fin 2 =>
    if i = 0 then (1 : Multiplicative ℤ) else Multiplicative.ofAdd (1 : ℤ))

@[simp] theorem expHom_b : expHom b = 1 := by
  unfold expHom b
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem expHom_c : expHom c = Multiplicative.ofAdd (1 : ℤ) := by
  unfold expHom c
  rw [FreeGroup.lift.of]
  simp

theorem expHom_zpow_c (n : ℤ) : expHom (c ^ n) = Multiplicative.ofAdd n := by
  induction n using Int.induction_on with
  | hz => simp
  | hp k ih =>
      rw [zpow_add, zpow_one, map_mul, ih, expHom_c]
      rfl
  | hn k ih =>
      rw [zpow_sub, zpow_one, map_mul, map_inv, ih, expHom_c]
      rfl

/-- An element of `Multiplicative ℤ` is trivial exactly when its exponent
is. -/
theorem ofAdd_eq_one_iff {n : ℤ} : Multiplicative.ofAdd n = 1 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h
    rw [h]
    rfl

theorem expHom_row (i : ℤ) : expHom (row i) = 1 := by
  unfold row
  rw [map_mul, map_mul, expHom_zpow_c, expHom_b, expHom_zpow_c, mul_one,
    ← Multiplicative.ofAdd_add, neg_add_cancel]
  rfl

/-! ## 2.  The row is normalized by `c` -/

theorem conj_row (n i : ℤ) : c ^ n * row i * c ^ (-n) = row (i - n) := by
  have h1 : c ^ n * c ^ (-i) = c ^ (-(i - n)) := by
    rw [← zpow_add]
    congr 1
    ring
  have h2 : c ^ i * c ^ (-n) = c ^ (i - n) := by
    rw [← zpow_add]
    congr 1
    ring
  calc c ^ n * row i * c ^ (-n)
      = (c ^ n * c ^ (-i)) * b * (c ^ i * c ^ (-n)) := by
        unfold row
        group
    _ = c ^ (-(i - n)) * b * c ^ (i - n) := by rw [h1, h2]
    _ = row (i - n) := rfl

/-- The form of `conj_row` with the sign of the conjugating power flipped. -/
theorem conj_row' (n i : ℤ) : c ^ (-n) * row i * c ^ n = row (i + n) := by
  have h := conj_row (-n) i
  rw [neg_neg] at h
  rw [h]
  congr 1
  ring

theorem conj_mem_Row (n : ℤ) {x : F₀} (hx : x ∈ Row) : c ^ n * x * c ^ (-n) ∈ Row := by
  refine Subgroup.closure_induction (p := fun z _ => c ^ n * z * c ^ (-n) ∈ Row)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [conj_row]
    exact row_mem _
  · rw [mul_one, zpow_neg, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro y z _ _ hy hz
    have hsplit : c ^ n * (y * z) * c ^ (-n)
        = (c ^ n * y * c ^ (-n)) * (c ^ n * z * c ^ (-n)) := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ hy hz
  · intro y _ hy
    have hsplit : c ^ n * y⁻¹ * c ^ (-n) = (c ^ n * y * c ^ (-n))⁻¹ := by group
    rw [hsplit]
    exact Subgroup.inv_mem _ hy

/-! ## 3.  Every word is a row element times a power of `c` -/

/-- The words that can be split as a row element times the power of `c` their
exponent prescribes. -/
def SplitSub : Subgroup F₀ where
  carrier := {W : F₀ | ∃ r ∈ Row, W = r * c ^ (Multiplicative.toAdd (expHom W))}
  one_mem' := by
    refine ⟨1, Subgroup.one_mem Row, ?_⟩
    rw [map_one]
    show (1 : F₀) = 1 * c ^ (Multiplicative.toAdd (1 : Multiplicative ℤ))
    have h : Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 := rfl
    rw [h, zpow_zero, mul_one]
  mul_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
    set a := Multiplicative.toAdd (expHom x) with ha
    set d := Multiplicative.toAdd (expHom y) with hd
    have hn : Multiplicative.toAdd (expHom (x * y)) = a + d := by
      rw [map_mul]
      rfl
    refine ⟨r * (c ^ a * s * c ^ (-a)), Subgroup.mul_mem _ hr (conj_mem_Row a hs), ?_⟩
    rw [hn, hx, hy, zpow_add]
    group
  inv_mem' := by
    rintro x ⟨r, hr, hx⟩
    set a := Multiplicative.toAdd (expHom x) with ha
    have hn : Multiplicative.toAdd (expHom x⁻¹) = -a := by
      rw [map_inv]
      rfl
    refine ⟨c ^ (-a) * r⁻¹ * c ^ (-(-a)),
      conj_mem_Row (-a) (Subgroup.inv_mem _ hr), ?_⟩
    rw [hn, hx]
    group

theorem splitSub_eq_top : SplitSub = ⊤ := by
  refine top_le_iff.mp ?_
  intro W -
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro i
    rcases fin_two_cases i with rfl | rfl
    · show b ∈ SplitSub
      refine ⟨b, ?_, ?_⟩
      · rw [← row_zero]
        exact row_mem 0
      · rw [expHom_b]
        show b = b * c ^ (Multiplicative.toAdd (1 : Multiplicative ℤ))
        have h : Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 := rfl
        rw [h, zpow_zero, mul_one]
    · show c ∈ SplitSub
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [expHom_c]
      show c = 1 * c ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)))
      have h : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = 1 := rfl
      rw [h, zpow_one, one_mul]
  · intro i hmem
    exact Subgroup.inv_mem _ hmem
  · intro x y hx hy
    exact Subgroup.mul_mem _ hx hy

/-- **Every word splits.** -/
theorem exists_row_mul (W : F₀) :
    ∃ r ∈ Row, W = r * c ^ (Multiplicative.toAdd (expHom W)) := by
  have hW : W ∈ SplitSub := by
    rw [splitSub_eq_top]
    trivial
  exact hW

/-! ## 4.  The row is the kernel of the exponent -/

theorem Row_le_ker : Row ≤ MonoidHom.ker expHom := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  exact MonoidHom.mem_ker.mpr (expHom_row i)

theorem mem_Row_of_expHom_eq_one {W : F₀} (h : expHom W = 1) : W ∈ Row := by
  obtain ⟨r, hr, hW⟩ := exists_row_mul W
  have h0 : Multiplicative.toAdd (expHom W) = 0 := by
    rw [h]
    rfl
  rw [h0, zpow_zero, mul_one] at hW
  rw [hW]
  exact hr

/-- **`Row = ker expHom`.** -/
theorem Row_eq_ker : Row = MonoidHom.ker expHom :=
  le_antisymm Row_le_ker fun _ hW => mem_Row_of_expHom_eq_one (MonoidHom.mem_ker.mp hW)

theorem mem_Row_iff {W : F₀} : W ∈ Row ↔ expHom W = 1 := by
  constructor
  · intro h
    exact MonoidHom.mem_ker.mp (Row_le_ker h)
  · exact mem_Row_of_expHom_eq_one

/-- A power of `c` lies in the row only if it is trivial. -/
theorem zpow_c_mem_Row_iff {n : ℤ} : c ^ n ∈ Row ↔ n = 0 := by
  rw [mem_Row_iff, expHom_zpow_c, ofAdd_eq_one_iff]

/-! ## 5.  The positive part of `FreeGroup ℤ` -/

/-- The nonnegative generators. -/
def posSet : Set (FreeGroup ℤ) := (fun i : ℤ => FreeGroup.of i) '' {i : ℤ | 0 ≤ i}

/-- The subgroup they generate. -/
def posSub : Subgroup (FreeGroup ℤ) := Subgroup.closure posSet

/-- The retraction deleting the negative letters. -/
def killNeg : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => if 0 ≤ i then FreeGroup.of i else 1)

@[simp] theorem killNeg_of (i : ℤ) :
    killNeg (FreeGroup.of i) = if 0 ≤ i then FreeGroup.of i else 1 := by
  unfold killNeg
  rw [FreeGroup.lift.of]

theorem killNeg_mem_posSub (W : FreeGroup ℤ) : killNeg W ∈ posSub := by
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro i
    rw [killNeg_of]
    by_cases hi : 0 ≤ i
    · rw [if_pos hi]
      exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    · rw [if_neg hi]
      exact Subgroup.one_mem _
  · intro i hmem
    rw [map_inv]
    exact Subgroup.inv_mem _ hmem
  · intro x y hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy

theorem killNeg_eq_self_of_mem {W : FreeGroup ℤ} (hW : W ∈ posSub) :
    killNeg W = W := by
  refine Subgroup.closure_induction (p := fun z _ => killNeg z = z) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨i, hi, rfl⟩
    rw [killNeg_of, if_pos hi]
  · exact map_one _
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy]
  · intro x _ hx
    rw [map_inv, hx]

/-- **Membership in the positive part is a statement about letters.** -/
theorem mem_posSub_iff {W : FreeGroup ℤ} : W ∈ posSub ↔ killNeg W = W := by
  constructor
  · exact killNeg_eq_self_of_mem
  · intro h
    rw [← h]
    exact killNeg_mem_posSub W

/-! ## 6.  The half row -/

/-- **The positive half of the row**, `⟨bᵢ : i ≥ 0⟩`. -/
def HalfRow : Subgroup F₀ := posSub.map basisHom

theorem halfRow_le_Row : HalfRow ≤ Row := by
  rintro _ ⟨W, _, rfl⟩
  rw [← range_basisHom]
  exact ⟨W, rfl⟩

theorem row_mem_halfRow {i : ℤ} (hi : 0 ≤ i) : row i ∈ HalfRow :=
  ⟨FreeGroup.of i, Subgroup.subset_closure ⟨i, hi, rfl⟩, basisHom_of i⟩

/-- **Membership in the half row, read on the basis.** -/
theorem mem_halfRow_iff {W : FreeGroup ℤ} : basisHom W ∈ HalfRow ↔ W ∈ posSub := by
  constructor
  · rintro ⟨V, hV, hVW⟩
    have hVW' : V = W := basisHom_injective hVW
    rwa [← hVW']
  · intro hW
    exact ⟨W, hW, rfl⟩

/-- The half row is generated by the nonnegative row elements. -/
theorem halfRow_eq_closure :
    HalfRow = Subgroup.closure ((fun i : ℤ => row i) '' {i : ℤ | 0 ≤ i}) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨W, hW, rfl⟩
    refine Subgroup.closure_induction
      (p := fun z _ => basisHom z ∈
        Subgroup.closure ((fun i : ℤ => row i) '' {i : ℤ | 0 ≤ i}))
      ?_ ?_ ?_ ?_ hW
    · rintro _ ⟨i, hi, rfl⟩
      rw [basisHom_of]
      exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      rw [map_inv]
      exact Subgroup.inv_mem _ hx
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact row_mem_halfRow hi

end Row
end Higman
end GroupApproximation

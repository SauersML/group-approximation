import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.UpperTriangular
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# The Borel subgroup of `GL₄(ℚ)` is solvable

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: the Guentner--Higson--Weinberger argument embeds `Σ`
coarsely into the group of upper-triangular matrices, which is solvable and
hence has property A.  This file proves the solvability (work order
WO-NN09b-A).

* `borelDiagHom : borel →* (Fin 4 → ℚˣ)` reads off the diagonal; its kernel
  lies in the unipotent group `unipFilt 1`.
* `unipFilt r` consists of unipotent upper-triangular units `u` (with `u⁻¹`
  of the same shape) such that `u i j = 0` whenever `0 < j - i < r`.
* `unipDistHom r : unipFilt r →* Multiplicative (Fin 4 → Fin 4 → ℚ)` reads
  off the entries at distance `r` from the diagonal; it is additive, and its
  kernel lies in `unipFilt (r + 1)`.
* `unipFilt 4` is trivial.

Extensions of solvable groups by solvable groups are solvable
(`solvable_of_ker_le_range`), giving `borel_isSolvable`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel

/-- An extension criterion: if `g : H →* A` has solvable target and its
kernel lies in a solvable subgroup `K ≤ H`, then `H` is solvable. -/
theorem isSolvable_of_ker_mem {G A : Type*} [Group G] [Group A] {H K : Subgroup G}
    (hKH : K ≤ H) (g : ↥H →* A) (hker : ∀ x : ↥H, g x = 1 → (x : G) ∈ K)
    (hA : IsSolvable A) (hK : IsSolvable ↥K) : IsSolvable ↥H :=
  solvable_of_ker_le_range (hG' := hK) (hG'' := hA) (Subgroup.inclusion hKH) g
    fun x hx ↦ MonoidHom.mem_range.mpr
      ⟨⟨(x : G), hker x (MonoidHom.mem_ker.mp hx)⟩,
        Subtype.ext (Subgroup.coe_inclusion hKH _)⟩

/-! ### The unipotent filtration -/

/-- Unipotent upper-triangular matrices vanishing at distances `0 < j - i < r`. -/
def IsUnipFilt (r : ℕ) (m : Mat) : Prop :=
  IsUpperTri m ∧ (∀ i : Fin 4, m i i = 1) ∧
    ∀ i j : Fin 4, i < j → (j : ℕ) < (i : ℕ) + r → m i j = 0

theorem isUnipFilt_one (r : ℕ) : IsUnipFilt r (1 : Mat) :=
  ⟨isUpperTri_one, fun i ↦ Matrix.one_apply_eq i, fun _ _ hij _ ↦ Matrix.one_apply_ne hij.ne⟩

theorem isUnipFilt_mul {r : ℕ} {a b : Mat} (ha : IsUnipFilt r a) (hb : IsUnipFilt r b) :
    IsUnipFilt r (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨isUpperTri_mul ha1 hb1, fun i ↦ ?_, fun i j hij hjr ↦ ?_⟩
  · rw [upperTri_mul_apply_diag ha1 hb1 i, ha2 i, hb2 i, mul_one]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hki : k < i
    · rw [ha1 i k hki, zero_mul]
    · by_cases hjk : j < k
      · rw [hb1 k j hjk, mul_zero]
      · by_cases hik : i < k
        · have hk : (k : ℕ) < (i : ℕ) + r := by
            have h1 : (k : ℕ) ≤ (j : ℕ) := Fin.le_def.mp (not_lt.mp hjk)
            omega
          rw [ha3 i k hik hk, zero_mul]
        · have hki' : k = i := le_antisymm (not_lt.mp hik) (not_lt.mp hki)
          rw [hki', hb3 i j hij hjr, mul_zero]

theorem IsUnipFilt.of_succ {r : ℕ} {m : Mat} (h : IsUnipFilt (r + 1) m) : IsUnipFilt r m := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun i j hij hjr ↦ h3 i j hij (by omega)⟩

/-- An upper-triangular matrix with unit diagonal lies in the first step of
the filtration (the distance condition is vacuous). -/
theorem isUnipFilt_one_of {m : Mat} (h1 : IsUpperTri m) (hd : ∀ i : Fin 4, m i i = 1) :
    IsUnipFilt 1 m :=
  ⟨h1, hd, fun i j hij hjr ↦ absurd hjr (by
    have h : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
    omega)⟩

/-- The unipotent subgroup `N_r`. -/
def unipFilt (r : ℕ) : Subgroup Matˣ where
  carrier := {u | IsUnipFilt r (u : Mat) ∧ IsUnipFilt r ((u⁻¹ : Matˣ) : Mat)}
  mul_mem' := by
    intro u v hu hv
    obtain ⟨hu1, hu2⟩ : IsUnipFilt r (u : Mat) ∧ IsUnipFilt r ((u⁻¹ : Matˣ) : Mat) := hu
    obtain ⟨hv1, hv2⟩ : IsUnipFilt r (v : Mat) ∧ IsUnipFilt r ((v⁻¹ : Matˣ) : Mat) := hv
    show IsUnipFilt r ((u * v : Matˣ) : Mat) ∧ IsUnipFilt r (((u * v)⁻¹ : Matˣ) : Mat)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact isUnipFilt_mul hu1 hv1
    · rw [mul_inv_rev, Units.val_mul]
      exact isUnipFilt_mul hv2 hu2
  one_mem' := by
    show IsUnipFilt r ((1 : Matˣ) : Mat) ∧ IsUnipFilt r (((1 : Matˣ)⁻¹ : Matˣ) : Mat)
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact isUnipFilt_one r
    · rw [inv_one, Units.val_one]
      exact isUnipFilt_one r
  inv_mem' := by
    intro u hu
    obtain ⟨hu1, hu2⟩ : IsUnipFilt r (u : Mat) ∧ IsUnipFilt r ((u⁻¹ : Matˣ) : Mat) := hu
    show IsUnipFilt r ((u⁻¹ : Matˣ) : Mat) ∧ IsUnipFilt r ((u⁻¹⁻¹ : Matˣ) : Mat)
    refine ⟨hu2, ?_⟩
    rw [inv_inv]
    exact hu1

theorem mem_unipFilt {r : ℕ} {u : Matˣ} :
    u ∈ unipFilt r ↔ IsUnipFilt r (u : Mat) ∧ IsUnipFilt r ((u⁻¹ : Matˣ) : Mat) :=
  Iff.rfl

theorem unipFilt_succ_le (r : ℕ) : unipFilt (r + 1) ≤ unipFilt r := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := mem_unipFilt.mp hu
  exact mem_unipFilt.mpr ⟨hu1.of_succ, hu2.of_succ⟩

theorem unipFilt_one_le_borel : unipFilt 1 ≤ borel := by
  intro u hu
  obtain ⟨⟨hu1, -, -⟩, ⟨hu2, -, -⟩⟩ := mem_unipFilt.mp hu
  exact mem_borel.mpr ⟨hu1, hu2⟩

/-! ### Entries at distance `r` -/

/-- The entries of `m` at distance exactly `r` above the diagonal. -/
def unipDistEntries (r : ℕ) (m : Mat) : Fin 4 → Fin 4 → ℚ :=
  fun i j ↦ if (j : ℕ) = (i : ℕ) + r then m i j else 0

theorem unipDistEntries_mul {r : ℕ} (hr : 1 ≤ r) {a b : Mat} (ha : IsUnipFilt r a)
    (hb : IsUnipFilt r b) :
    unipDistEntries r (a * b) = unipDistEntries r a + unipDistEntries r b := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, -⟩ := hb
  funext i j
  show (if (j : ℕ) = (i : ℕ) + r then (a * b) i j else 0) =
    (if (j : ℕ) = (i : ℕ) + r then a i j else 0) + (if (j : ℕ) = (i : ℕ) + r then b i j else 0)
  by_cases h : (j : ℕ) = (i : ℕ) + r
  · rw [if_pos h, if_pos h, if_pos h]
    have hij : i ≠ j := by
      intro e
      rw [e] at h
      omega
    have hzero : ∀ c : Fin 4, c ≠ i ∧ c ≠ j → a i c * b c j = 0 := by
      intro c hc
      rcases lt_or_gt_of_ne hc.1 with hci | hci
      · rw [ha1 i c hci, zero_mul]
      · by_cases hcr : (c : ℕ) < (i : ℕ) + r
        · rw [ha3 i c hci hcr, zero_mul]
        · have hjc : j < c := by
            have hne : (c : ℕ) ≠ (j : ℕ) := fun e ↦ hc.2 (Fin.ext e)
            exact Fin.lt_def.mpr (by omega)
          rw [hb1 c j hjc, mul_zero]
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij hzero, ha2 i, hb2 j, one_mul, mul_one]
    exact add_comm _ _
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem IsUnipFilt.succ_of_unipDistEntries_eq_zero {r : ℕ} {m : Mat} (hm : IsUnipFilt r m)
    (hd : unipDistEntries r m = 0) : IsUnipFilt (r + 1) m := by
  obtain ⟨h1, h2, h3⟩ := hm
  refine ⟨h1, h2, fun i j hij hjr ↦ ?_⟩
  by_cases h : (j : ℕ) < (i : ℕ) + r
  · exact h3 i j hij h
  · have h' : (j : ℕ) = (i : ℕ) + r := by omega
    have hij' : (if (j : ℕ) = (i : ℕ) + r then m i j else 0) = 0 :=
      congrFun (congrFun hd i) j
    rwa [if_pos h'] at hij'

/-- The homomorphism `N_r → ℚ^{4×4}` reading off the entries at distance `r`. -/
def unipDistHom (r : ℕ) (hr : 1 ≤ r) : ↥(unipFilt r) →* Multiplicative (Fin 4 → Fin 4 → ℚ) :=
  MonoidHom.mk' (fun u ↦ Multiplicative.ofAdd (unipDistEntries r ((u : Matˣ) : Mat)))
    fun u v ↦ by
      show Multiplicative.ofAdd (unipDistEntries r (((u : Matˣ) * (v : Matˣ) : Matˣ) : Mat)) =
        Multiplicative.ofAdd (unipDistEntries r ((u : Matˣ) : Mat)) *
          Multiplicative.ofAdd (unipDistEntries r ((v : Matˣ) : Mat))
      rw [Units.val_mul,
        unipDistEntries_mul hr (mem_unipFilt.mp u.2).1 (mem_unipFilt.mp v.2).1, ofAdd_add]

theorem unipDistHom_apply {r : ℕ} (hr : 1 ≤ r) (u : ↥(unipFilt r)) :
    unipDistHom r hr u = Multiplicative.ofAdd (unipDistEntries r ((u : Matˣ) : Mat)) :=
  rfl

theorem unipDistHom_ker {r : ℕ} (hr : 1 ≤ r) (u : ↥(unipFilt r)) (hu : unipDistHom r hr u = 1) :
    (u : Matˣ) ∈ unipFilt (r + 1) := by
  have hinv : unipDistHom r hr u⁻¹ = 1 := by
    rw [map_inv, hu, inv_one]
  rw [unipDistHom_apply] at hu hinv
  have h0 : unipDistEntries r ((u : Matˣ) : Mat) = 0 := ofAdd_eq_one.mp hu
  have h0' : unipDistEntries r (((u : Matˣ)⁻¹ : Matˣ) : Mat) = 0 := ofAdd_eq_one.mp hinv
  obtain ⟨hu1, hu2⟩ := mem_unipFilt.mp u.2
  exact mem_unipFilt.mpr
    ⟨hu1.succ_of_unipDistEntries_eq_zero h0, hu2.succ_of_unipDistEntries_eq_zero h0'⟩

theorem eq_one_of_mem_unipFilt_four {u : Matˣ} (hu : u ∈ unipFilt 4) : u = 1 := by
  obtain ⟨⟨hut, hd, hf⟩, -⟩ := mem_unipFilt.mp hu
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  rw [Units.val_one]
  rcases lt_trichotomy i j with h | h | h
  · have hj : (j : ℕ) < (i : ℕ) + 4 := by
      have hj4 : (j : ℕ) < 4 := j.isLt
      omega
    rw [hf i j h hj, Matrix.one_apply_ne h.ne]
  · rw [h, hd j, Matrix.one_apply_eq]
  · rw [hut i j h, Matrix.one_apply_ne h.ne']

theorem isSolvable_unipFilt_four : IsSolvable ↥(unipFilt 4) :=
  isSolvable_of_comm fun a b ↦ Subtype.ext
    ((eq_one_of_mem_unipFilt_four (a * b).2).trans (eq_one_of_mem_unipFilt_four (b * a).2).symm)

theorem isSolvable_unipFilt_of_succ {r : ℕ} (hr : 1 ≤ r) (h : IsSolvable ↥(unipFilt (r + 1))) :
    IsSolvable ↥(unipFilt r) :=
  isSolvable_of_ker_mem (unipFilt_succ_le r) (unipDistHom r hr) (unipDistHom_ker hr)
    inferInstance h

/-- The unipotent upper-triangular group `N = N_1` is solvable. -/
theorem isSolvable_unipFilt_one : IsSolvable ↥(unipFilt 1) :=
  isSolvable_unipFilt_of_succ (r := 1) le_rfl
    (isSolvable_unipFilt_of_succ (r := 2) (by norm_num)
      (isSolvable_unipFilt_of_succ (r := 3) (by norm_num) isSolvable_unipFilt_four))

/-! ### The diagonal homomorphism -/

/-- The `i`-th diagonal entry of an element of the Borel group, as a unit. -/
def borelDiagUnit {u : Matˣ} (hu : u ∈ borel) (i : Fin 4) : ℚˣ where
  val := (u : Mat) i i
  inv := ((u⁻¹ : Matˣ) : Mat) i i
  val_inv := by
    show (u : Mat) i i * ((u⁻¹ : Matˣ) : Mat) i i = 1
    rw [← upperTri_mul_apply_diag (mem_borel.mp hu).1 (mem_borel.mp hu).2 i, Units.mul_inv,
      Matrix.one_apply_eq]
  inv_val := by
    show ((u⁻¹ : Matˣ) : Mat) i i * (u : Mat) i i = 1
    rw [← upperTri_mul_apply_diag (mem_borel.mp hu).2 (mem_borel.mp hu).1 i, Units.inv_mul,
      Matrix.one_apply_eq]

/-- The diagonal homomorphism `B → (ℚˣ)⁴`. -/
def borelDiagHom : ↥borel →* (Fin 4 → ℚˣ) :=
  MonoidHom.mk' (fun u i ↦ borelDiagUnit u.2 i) fun u v ↦ by
    funext i
    refine Units.ext ?_
    show (((u : Matˣ) * (v : Matˣ) : Matˣ) : Mat) i i =
      ((u : Matˣ) : Mat) i i * ((v : Matˣ) : Mat) i i
    rw [Units.val_mul]
    exact upperTri_mul_apply_diag (mem_borel.mp u.2).1 (mem_borel.mp v.2).1 i

theorem borelDiagHom_ker (u : ↥borel) (hu : borelDiagHom u = 1) : (u : Matˣ) ∈ unipFilt 1 := by
  have hinv : borelDiagHom u⁻¹ = 1 := by
    rw [map_inv, hu, inv_one]
  have hd : ∀ i : Fin 4, ((u : Matˣ) : Mat) i i = 1 :=
    fun i ↦ congrArg Units.val (congrFun hu i)
  have hdi : ∀ i : Fin 4, (((u : Matˣ)⁻¹ : Matˣ) : Mat) i i = 1 :=
    fun i ↦ congrArg Units.val (congrFun hinv i)
  obtain ⟨h1, h2⟩ := mem_borel.mp u.2
  exact mem_unipFilt.mpr ⟨isUnipFilt_one_of h1 hd, isUnipFilt_one_of h2 hdi⟩

/-- **The Borel subgroup of `GL₄(ℚ)` is solvable** (`non_mf_group_notes.tex`,
paragraph `Exactness`, GHW coarse embedding into upper-triangular matrices). -/
instance borel_isSolvable : IsSolvable ↥borel :=
  isSolvable_of_ker_mem unipFilt_one_le_borel borelDiagHom borelDiagHom_ker inferInstance
    isSolvable_unipFilt_one

end GroupApproximation.Full.NN09b

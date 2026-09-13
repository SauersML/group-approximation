import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import GroupApproximation.GroupTheory.HigmanThompson.GeometricF

/-!
# Thompson's group `F`

`F` is given by Guba's presentation (1.2) of arXiv:2305.07113,
`⟨x₀, x₁ | x₁^{x₀²} = x₁^{x₀x₁}, x₁^{x₀³} = x₁^{x₀²x₁}⟩` with `a^b = b⁻¹ab`, each relation
`u = v` written as the relator `u v⁻¹`.  The generators `x_{n+1} = x₀⁻ⁿ x₁ x₀ⁿ` satisfy
`x_i⁻¹ x_j x_i = x_{j+1}` for `i < j`.

The map `x_i ↦ X_i⁻¹` is an isomorphism onto Brown's group `BrownGroup 0` (Brown's relators
`X₁ X_j X₁⁻¹ = X_{j+1}`, `j = 2, 3`, are the two relations above), and Brown's evaluation into
`Equiv.Perm ℚ` is faithful.  So `ev : F →* Equiv.Perm ℚ` is injective with image `geoF 0`:
every `ev g` is strictly increasing and fixes `(-∞, 0]`, and `ev x_k` fixes `(-∞, k]`.
-/

namespace GroupApproximation
namespace ThompsonOre

open HigmanThompson

noncomputable section

def conjBy (a b : FreeGroup (Fin 2)) : FreeGroup (Fin 2) :=
  b⁻¹ * a * b

def thompsonRels : Set (FreeGroup (Fin 2)) :=
  {conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 * FreeGroup.of 1))⁻¹,
    conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 3) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2 * FreeGroup.of 1))⁻¹}

abbrev ThompsonF : Type :=
  PresentedGroup thompsonRels

def x0 : ThompsonF :=
  PresentedGroup.of 0

def x1 : ThompsonF :=
  PresentedGroup.of 1

/-! ## Relations -/

/-- Images satisfying the two relations define a homomorphism out of `F`. -/
theorem lift_thompsonRels {G : Type*} [Group G] (f : Fin 2 → G)
    (h1 : (f 0 ^ 2)⁻¹ * f 1 * f 0 ^ 2 = (f 0 * f 1)⁻¹ * f 1 * (f 0 * f 1))
    (h2 : (f 0 ^ 3)⁻¹ * f 1 * f 0 ^ 3 = (f 0 ^ 2 * f 1)⁻¹ * f 1 * (f 0 ^ 2 * f 1)) :
    ∀ r ∈ thompsonRels, FreeGroup.lift f r = 1 := by
  rintro r (rfl | rfl)
  · simp only [conjBy, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr h1
  · simp only [conjBy, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr h2

theorem rel_one : (x0 ^ 2)⁻¹ * x1 * x0 ^ 2 = (x0 * x1)⁻¹ * x1 * (x0 * x1) := by
  have h := PresentedGroup.one_of_mem (rels := thompsonRels) (Set.mem_insert _ _)
  simp only [conjBy, map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

theorem rel_two : (x0 ^ 3)⁻¹ * x1 * x0 ^ 3 = (x0 ^ 2 * x1)⁻¹ * x1 * (x0 ^ 2 * x1) := by
  have h := PresentedGroup.one_of_mem (rels := thompsonRels)
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [conjBy, map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

/-- Guba's generators: `x₀`, and `x_{n+1} = x₀⁻ⁿ x₁ x₀ⁿ`. -/
def xn : ℕ → ThompsonF
  | 0 => x0
  | n + 1 => (x0 ^ n)⁻¹ * x1 * x0 ^ n

theorem xn_zero : xn 0 = x0 := rfl

theorem xn_succ (n : ℕ) : xn (n + 1) = (x0 ^ n)⁻¹ * x1 * x0 ^ n := rfl

theorem xn_one : xn 1 = x1 := by
  show (x0 ^ 0)⁻¹ * x1 * x0 ^ 0 = x1
  simp

theorem xn_of (i : Fin 2) : xn i.val = PresentedGroup.of i := by
  rcases i with ⟨_ | _ | n, hn⟩
  · rfl
  · exact xn_one
  · omega

theorem xn_conj_one_two : (xn 1)⁻¹ * xn 2 * xn 1 = xn 3 := by
  rw [xn_one]
  calc x1⁻¹ * xn 2 * x1 = (x0 * x1)⁻¹ * x1 * (x0 * x1) := by
        show x1⁻¹ * ((x0 ^ 1)⁻¹ * x1 * x0 ^ 1) * x1 = _
        group
    _ = (x0 ^ 2)⁻¹ * x1 * x0 ^ 2 := rel_one.symm

theorem xn_conj_one_three : (xn 1)⁻¹ * xn 3 * xn 1 = xn 4 := by
  rw [xn_one]
  calc x1⁻¹ * xn 3 * x1 = (x0 ^ 2 * x1)⁻¹ * x1 * (x0 ^ 2 * x1) := by
        show x1⁻¹ * ((x0 ^ 2)⁻¹ * x1 * x0 ^ 2) * x1 = _
        group
    _ = (x0 ^ 3)⁻¹ * x1 * x0 ^ 3 := rel_two.symm

/-! ## Brown's group -/

theorem brownX_inv_conj {i j : ℕ} (h : i < j) :
    brownX 0 i * (brownX 0 j)⁻¹ * (brownX 0 i)⁻¹ = (brownX 0 (j + 1))⁻¹ := by
  have e := brownX_rel 0 h
  simp only [add_zero] at e
  rw [← e]
  group

theorem conj_pow_succ {G : Type*} [Group G] (c b : G) (n : ℕ) :
    (c ^ (n + 1))⁻¹ * b * c ^ (n + 1) = c⁻¹ * ((c ^ n)⁻¹ * b * c ^ n) * c := by
  rw [pow_succ]
  group

theorem toBrown_rel_one :
    ((brownX 0 0)⁻¹ ^ 2)⁻¹ * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ ^ 2 =
      ((brownX 0 0)⁻¹ * (brownX 0 1)⁻¹)⁻¹ * (brownX 0 1)⁻¹ *
        ((brownX 0 0)⁻¹ * (brownX 0 1)⁻¹) := by
  have c01 : brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ = (brownX 0 2)⁻¹ :=
    brownX_inv_conj (by norm_num)
  have c02 : brownX 0 0 * (brownX 0 2)⁻¹ * (brownX 0 0)⁻¹ = (brownX 0 3)⁻¹ :=
    brownX_inv_conj (by norm_num)
  have c12 : brownX 0 1 * (brownX 0 2)⁻¹ * (brownX 0 1)⁻¹ = (brownX 0 3)⁻¹ :=
    brownX_inv_conj (by norm_num)
  calc ((brownX 0 0)⁻¹ ^ 2)⁻¹ * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ ^ 2
      = brownX 0 0 * (brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹) * (brownX 0 0)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, inv_inv, mul_assoc]
    _ = brownX 0 1 * (brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹) * (brownX 0 1)⁻¹ := by
        rw [c01, c02, c12]
    _ = ((brownX 0 0)⁻¹ * (brownX 0 1)⁻¹)⁻¹ * (brownX 0 1)⁻¹ *
        ((brownX 0 0)⁻¹ * (brownX 0 1)⁻¹) := by
        group

theorem toBrown_rel_two :
    ((brownX 0 0)⁻¹ ^ 3)⁻¹ * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ ^ 3 =
      ((brownX 0 0)⁻¹ ^ 2 * (brownX 0 1)⁻¹)⁻¹ * (brownX 0 1)⁻¹ *
        ((brownX 0 0)⁻¹ ^ 2 * (brownX 0 1)⁻¹) := by
  have c01 : brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ = (brownX 0 2)⁻¹ :=
    brownX_inv_conj (by norm_num)
  have c02 : brownX 0 0 * (brownX 0 2)⁻¹ * (brownX 0 0)⁻¹ = (brownX 0 3)⁻¹ :=
    brownX_inv_conj (by norm_num)
  have c03 : brownX 0 0 * (brownX 0 3)⁻¹ * (brownX 0 0)⁻¹ = (brownX 0 4)⁻¹ :=
    brownX_inv_conj (by norm_num)
  have c13 : brownX 0 1 * (brownX 0 3)⁻¹ * (brownX 0 1)⁻¹ = (brownX 0 4)⁻¹ :=
    brownX_inv_conj (by norm_num)
  calc ((brownX 0 0)⁻¹ ^ 3)⁻¹ * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ ^ 3
      = brownX 0 0 * (brownX 0 0 * (brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹) *
          (brownX 0 0)⁻¹) * (brownX 0 0)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, inv_inv, mul_assoc]
    _ = brownX 0 1 * (brownX 0 0 * (brownX 0 0 * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹) *
          (brownX 0 0)⁻¹) * (brownX 0 1)⁻¹ := by
        rw [c01, c02, c03, c13]
    _ = ((brownX 0 0)⁻¹ ^ 2 * (brownX 0 1)⁻¹)⁻¹ * (brownX 0 1)⁻¹ *
        ((brownX 0 0)⁻¹ ^ 2 * (brownX 0 1)⁻¹) := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, inv_inv, mul_assoc]

/-- `x_i ↦ X_i⁻¹`, from `F` to Brown's group. -/
def toBrown : ThompsonF →* BrownGroup 0 :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => (brownX 0 i.val)⁻¹)
    (lift_thompsonRels _ toBrown_rel_one toBrown_rel_two)

theorem toBrown_of (i : Fin 2) : toBrown (PresentedGroup.of i) = (brownX 0 i.val)⁻¹ :=
  PresentedGroup.toGroup.of _

theorem toBrown_x0 : toBrown x0 = (brownX 0 0)⁻¹ := toBrown_of 0

theorem toBrown_x1 : toBrown x1 = (brownX 0 1)⁻¹ := toBrown_of 1

theorem toBrown_conj (n : ℕ) :
    ((brownX 0 0)⁻¹ ^ n)⁻¹ * (brownX 0 1)⁻¹ * (brownX 0 0)⁻¹ ^ n = (brownX 0 (n + 1))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [conj_pow_succ, ih, inv_inv]
    exact brownX_inv_conj (by omega)

theorem toBrown_xn : ∀ k : ℕ, toBrown (xn k) = (brownX 0 k)⁻¹
  | 0 => toBrown_x0
  | n + 1 => by
    rw [xn_succ, map_mul, map_mul, map_inv, map_pow, toBrown_x0, toBrown_x1]
    exact toBrown_conj n

theorem lift_brownWord_xn (k : ℕ) :
    FreeGroup.lift (fun i : Fin (0 + 2) => (xn i.val)⁻¹) (brownWord 0 k) = (xn k)⁻¹ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k < 0 + 2
    · rw [brownWord_of_lt 0 h, FreeGroup.lift_apply_of]
    · rw [brownWord_of_ge 0 (not_lt.mp h), map_mul, map_mul, map_inv, FreeGroup.lift_apply_of,
        ih (k - (0 + 1)) (by omega)]
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      rw [show n + 2 - (0 + 1) = n + 1 by omega]
      show x0⁻¹ * ((x0 ^ n)⁻¹ * x1 * x0 ^ n)⁻¹ * (x0⁻¹)⁻¹ =
        ((x0 ^ (n + 1))⁻¹ * x1 * x0 ^ (n + 1))⁻¹
      group

theorem brownRels_xn :
    ∀ r ∈ brownRels 0, FreeGroup.lift (fun i : Fin (0 + 2) => (xn i.val)⁻¹) r = 1 := by
  rintro r ⟨i, j, h1, h2, h3, h4, rfl⟩
  simp only [map_mul, map_inv, lift_brownWord_xn, inv_inv]
  obtain rfl : i = 1 := by omega
  obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
  · show (xn 1)⁻¹ * (xn 2)⁻¹ * xn 1 * xn 3 = 1
    rw [← xn_conj_one_two]
    group
  · show (xn 1)⁻¹ * (xn 3)⁻¹ * xn 1 * xn 4 = 1
    rw [← xn_conj_one_three]
    group

/-- `X_i ↦ x_i⁻¹`, from Brown's group to `F`. -/
def fromBrown : BrownGroup 0 →* ThompsonF :=
  PresentedGroup.toGroup brownRels_xn

theorem fromBrown_X (k : ℕ) : fromBrown (brownX 0 k) = (xn k)⁻¹ :=
  lift_brownWord_xn k

/-- **`F` is Brown's group `F_{2,∞}`.** -/
def thompsonEquivBrown : ThompsonF ≃* BrownGroup 0 :=
  MonoidHom.toMulEquiv toBrown fromBrown
    (PresentedGroup.ext fun i => by
      show fromBrown (toBrown (PresentedGroup.of i)) = PresentedGroup.of i
      rw [toBrown_of, map_inv, fromBrown_X, inv_inv, xn_of])
    (PresentedGroup.ext fun i => by
      have e : (PresentedGroup.of i : BrownGroup 0) = brownX 0 i.val := brownX_of_fin 0 i
      show toBrown (fromBrown (PresentedGroup.of i)) = PresentedGroup.of i
      rw [e, fromBrown_X, map_inv, toBrown_xn, inv_inv])

theorem thompsonEquivBrown_apply (g : ThompsonF) : thompsonEquivBrown g = toBrown g := rfl

theorem thompsonEquivBrown_symm_apply (h : BrownGroup 0) :
    thompsonEquivBrown.symm h = fromBrown h := rfl

@[simp] theorem thompsonEquivBrown_x0 : thompsonEquivBrown x0 = (brownX 0 0)⁻¹ := toBrown_x0

@[simp] theorem thompsonEquivBrown_x1 : thompsonEquivBrown x1 = (brownX 0 1)⁻¹ := toBrown_x1

theorem toBrown_injective : Function.Injective toBrown := thompsonEquivBrown.injective

/-! ## The action on `ℚ` -/

/-- `F` acting on `ℚ` through Brown's group: `x_k` acts as `X_k⁻¹`. -/
def ev : ThompsonF →* Equiv.Perm ℚ :=
  (brownEval 0).comp toBrown

theorem ev_apply (g : ThompsonF) : ev g = brownEval 0 (toBrown g) := rfl

theorem ev_xn (k : ℕ) : ev (xn k) = (xg 0 k)⁻¹ := by
  rw [ev_apply, toBrown_xn, map_inv, brownEval_X]

theorem ev_injective : Function.Injective ev :=
  (brownEval_injective 0).comp toBrown_injective

theorem ev_mem_geoF (g : ThompsonF) : ev g ∈ geoF 0 := by
  apply brownF_le_geoF 0
  exact MonoidHom.mem_range.mpr ⟨toBrown g, rfl⟩

theorem ev_strictMono (g : ThompsonF) : StrictMono (ev g) :=
  (ev_mem_geoF g).1.1

theorem ev_fix (g : ThompsonF) {t : ℚ} (ht : t ≤ 0) : ev g t = t :=
  (ev_mem_geoF g).2.1 t ht

/-- Every element of `geoF 0` is the action of an element of `F`. -/
theorem exists_ev_eq {f : Equiv.Perm ℚ} (hf : f ∈ geoF 0) : ∃ g, ev g = f := by
  rw [geoF_eq_brownF] at hf
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hf
  exact ⟨fromBrown h, congrArg (brownEval 0) (thompsonEquivBrown.apply_symm_apply h)⟩

end

end ThompsonOre
end GroupApproximation

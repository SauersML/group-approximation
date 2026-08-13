import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Countable.Basic

/-!
# The mapping telescope of an injective group endomorphism

Given an injective endomorphism `α : Γ →* Γ`, this file constructs the
ascending union `L` of the system `Γ →α Γ →α ⋯` as a quotient of `ℕ × Γ`,
together with:

* level embeddings `level n : Γ →* Telescope α hα`, all injective;
* the shift automorphism `shift`, acting as `α` at every level, whose inverse
  moves an element one level up; and
* the range characterisation `level_succ_mem_range_level_iff`: a level-`n+1`
  element lies in the level-`n` copy exactly when it lies in the range of `α`.

The pair `(shift, level 0)` realises the ascending-HNN conjugation relation
`t γ t⁻¹ = α γ` inside `Telescope α hα ⋊ ℤ` without any normal-form theory:
the non-membership needed for the marked non-MF word reduces to the range
characterisation above.

The equivalence used to define the quotient is the exact crossed relation
`(n, x) ≈ (m, y) ↔ α^[m] x = α^[n] y`; transitivity is where injectivity of
`α` enters.
-/

namespace GroupApproximation
namespace MappingTelescope

universe u

variable {Γ : Type u} [Group Γ]

/-! ## Iterates of an endomorphism -/

/-- The `n`-fold iterate of an endomorphism, bundled as a homomorphism. -/
def iterateHom (α : Γ →* Γ) : ℕ → Γ →* Γ
  | 0 => MonoidHom.id Γ
  | n + 1 => (iterateHom α n).comp α

@[simp] theorem iterateHom_zero_apply (α : Γ →* Γ) (x : Γ) :
    iterateHom α 0 x = x := rfl

theorem iterateHom_succ_apply (α : Γ →* Γ) (n : ℕ) (x : Γ) :
    iterateHom α (n + 1) x = iterateHom α n (α x) := rfl

theorem iterateHom_add_apply (α : Γ →* Γ) (m n : ℕ) (x : Γ) :
    iterateHom α (m + n) x = iterateHom α m (iterateHom α n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [← Nat.add_assoc, iterateHom_succ_apply, iterateHom_succ_apply, ih]

theorem iterateHom_comm_apply (α : Γ →* Γ) (m n : ℕ) (x : Γ) :
    iterateHom α m (iterateHom α n x) = iterateHom α n (iterateHom α m x) := by
  rw [← iterateHom_add_apply, ← iterateHom_add_apply, Nat.add_comm]

theorem iterateHom_apply_hom (α : Γ →* Γ) (n : ℕ) (x : Γ) :
    iterateHom α n (α x) = α (iterateHom α n x) := by
  have h := iterateHom_comm_apply α n 1 x
  simpa [iterateHom_succ_apply] using h

theorem iterateHom_injective {α : Γ →* Γ} (hα : Function.Injective α) :
    ∀ n : ℕ, Function.Injective (iterateHom α n)
  | 0 => fun _ _ h => h
  | n + 1 => fun x y h => by
      have h' : iterateHom α n (α x) = iterateHom α n (α y) := h
      exact hα (iterateHom_injective hα n h')

/-! ## The telescope -/

variable (α : Γ →* Γ) (hα : Function.Injective α)

/-- The crossed-iterate equivalence identifying `(n, x)` with
`(n + 1, α x)`. -/
def telescopeSetoid : Setoid (ℕ × Γ) where
  r p q := iterateHom α q.1 p.2 = iterateHom α p.1 q.2
  iseqv := by
    refine ⟨fun p => rfl, fun {p q} h => h.symm, ?_⟩
    intro p q r hpq hqr
    apply iterateHom_injective hα q.1
    calc iterateHom α q.1 (iterateHom α r.1 p.2)
        = iterateHom α r.1 (iterateHom α q.1 p.2) :=
          iterateHom_comm_apply α q.1 r.1 p.2
      _ = iterateHom α r.1 (iterateHom α p.1 q.2) := by rw [hpq]
      _ = iterateHom α p.1 (iterateHom α r.1 q.2) :=
          iterateHom_comm_apply α r.1 p.1 q.2
      _ = iterateHom α p.1 (iterateHom α q.1 r.2) := by rw [hqr]
      _ = iterateHom α q.1 (iterateHom α p.1 r.2) :=
          iterateHom_comm_apply α p.1 q.1 r.2

/-- The mapping telescope of the injective endomorphism `α`. -/
def Telescope : Type u := Quotient (telescopeSetoid α hα)

/-- The class of the level-`n` element `x`. -/
def mk (n : ℕ) (x : Γ) : Telescope α hα :=
  Quotient.mk (telescopeSetoid α hα) (n, x)

theorem mk_surjective : Function.Surjective (fun p : ℕ × Γ => mk α hα p.1 p.2) :=
  fun q => Quotient.inductionOn q (fun p => ⟨p, rfl⟩)

theorem mk_eq_mk_iff {n m : ℕ} {x y : Γ} :
    mk α hα n x = mk α hα m y ↔ iterateHom α m x = iterateHom α n y :=
  ⟨fun h => Quotient.exact (s := telescopeSetoid α hα) h,
    fun h => Quotient.sound (s := telescopeSetoid α hα) h⟩

/-- Raising the level along an iterate does not change the class. -/
theorem mk_add_iterate (n k : ℕ) (x : Γ) :
    mk α hα n x = mk α hα (n + k) (iterateHom α k x) := by
  rw [mk_eq_mk_iff]
  exact iterateHom_add_apply α n k x

instance : One (Telescope α hα) := ⟨mk α hα 0 1⟩

theorem one_def : (1 : Telescope α hα) = mk α hα 0 1 := rfl

/-- Multiplication lifts the two factors to the sum of their levels. -/
instance : Mul (Telescope α hα) :=
  ⟨Quotient.map₂ (fun p q => (p.1 + q.1, iterateHom α q.1 p.2 * iterateHom α p.1 q.2))
    (by
      rintro ⟨n, x⟩ ⟨n', x'⟩ (hx : iterateHom α n' x = iterateHom α n x')
        ⟨m, y⟩ ⟨m', y'⟩ (hy : iterateHom α m' y = iterateHom α m y')
      show iterateHom α (n' + m') (iterateHom α m x * iterateHom α n y) =
        iterateHom α (n + m) (iterateHom α m' x' * iterateHom α n' y')
      rw [map_mul, map_mul]
      congr 1
      · calc iterateHom α (n' + m') (iterateHom α m x)
            = iterateHom α (m' + m) (iterateHom α n' x) := by
              rw [← iterateHom_add_apply, ← iterateHom_add_apply,
                show n' + m' + m = m' + m + n' by omega]
        _ = iterateHom α (m' + m) (iterateHom α n x') := by rw [hx]
        _ = iterateHom α (n + m) (iterateHom α m' x') := by
              rw [← iterateHom_add_apply, ← iterateHom_add_apply,
                show m' + m + n = n + m + m' by omega]
      · calc iterateHom α (n' + m') (iterateHom α n y)
            = iterateHom α (n' + n) (iterateHom α m' y) := by
              rw [← iterateHom_add_apply, ← iterateHom_add_apply,
                show n' + m' + n = n' + n + m' by omega]
        _ = iterateHom α (n' + n) (iterateHom α m y') := by rw [hy]
        _ = iterateHom α (n + m) (iterateHom α n' y') := by
              rw [← iterateHom_add_apply, ← iterateHom_add_apply,
                show n' + n + m = n + m + n' by omega])⟩

theorem mk_mul_mk (n m : ℕ) (x y : Γ) :
    mk α hα n x * mk α hα m y =
      mk α hα (n + m) (iterateHom α m x * iterateHom α n y) := rfl

/-- Same-level multiplication is multiplication of representatives. -/
theorem mk_mul_mk_same (n : ℕ) (x y : Γ) :
    mk α hα n x * mk α hα n y = mk α hα n (x * y) := by
  rw [mk_mul_mk, mk_eq_mk_iff, map_mul, map_mul,
    ← iterateHom_add_apply, ← iterateHom_add_apply]

instance : Inv (Telescope α hα) :=
  ⟨Quotient.map (fun p => (p.1, p.2⁻¹))
    (by
      rintro ⟨n, x⟩ ⟨m, y⟩ (h : iterateHom α m x = iterateHom α n y)
      show iterateHom α m x⁻¹ = iterateHom α n y⁻¹
      rw [map_inv, map_inv, h])⟩

theorem mk_inv (n : ℕ) (x : Γ) : (mk α hα n x)⁻¹ = mk α hα n x⁻¹ := rfl

/-- The identity is represented at every level. -/
theorem one_eq_mk (n : ℕ) : (1 : Telescope α hα) = mk α hα n 1 := by
  rw [one_def, mk_eq_mk_iff, map_one, map_one]

/-- A level change along an explicit equality of levels. -/
theorem mk_congr_level {n m : ℕ} (h : n = m) (x : Γ) :
    mk α hα n x = mk α hα m x := by rw [h]

/-- Any two elements admit representatives at one common level. -/
theorem exists_common_level (a b : Telescope α hα) :
    ∃ (N : ℕ) (x y : Γ), a = mk α hα N x ∧ b = mk α hα N y := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  obtain ⟨n, x⟩ := p; obtain ⟨m, y⟩ := q
  refine ⟨n + m, iterateHom α m x, iterateHom α n y, ?_, ?_⟩
  · exact mk_add_iterate α hα n m x
  · exact (mk_add_iterate α hα m n y).trans
      (mk_congr_level α hα (Nat.add_comm m n) _)

/-- Any three elements admit representatives at one common level. -/
theorem exists_common_level₃ (a b c : Telescope α hα) :
    ∃ (N : ℕ) (x y w : Γ),
      a = mk α hα N x ∧ b = mk α hα N y ∧ c = mk α hα N w := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  induction c using Quotient.inductionOn with | h r =>
  obtain ⟨n, x⟩ := p; obtain ⟨m, y⟩ := q; obtain ⟨k, w⟩ := r
  refine ⟨n + m + k, iterateHom α (m + k) x, iterateHom α (n + k) y,
    iterateHom α (n + m) w, ?_, ?_, ?_⟩
  · exact (mk_add_iterate α hα n (m + k) x).trans
      (mk_congr_level α hα (by omega) _)
  · exact (mk_add_iterate α hα m (n + k) y).trans
      (mk_congr_level α hα (by omega) _)
  · exact (mk_add_iterate α hα k (n + m) w).trans
      (mk_congr_level α hα (by omega) _)

instance : Group (Telescope α hα) where
  mul_assoc a b c := by
    obtain ⟨N, x, y, w, rfl, rfl, rfl⟩ := exists_common_level₃ α hα a b c
    rw [mk_mul_mk_same, mk_mul_mk_same, mk_mul_mk_same, mk_mul_mk_same,
      mul_assoc]
  one_mul a := by
    induction a using Quotient.inductionOn with | h p =>
    obtain ⟨n, x⟩ := p
    show (1 : Telescope α hα) * mk α hα n x = mk α hα n x
    rw [one_eq_mk α hα n, mk_mul_mk_same, one_mul]
  mul_one a := by
    induction a using Quotient.inductionOn with | h p =>
    obtain ⟨n, x⟩ := p
    show mk α hα n x * (1 : Telescope α hα) = mk α hα n x
    rw [one_eq_mk α hα n, mk_mul_mk_same, mul_one]
  inv_mul_cancel a := by
    induction a using Quotient.inductionOn with | h p =>
    obtain ⟨n, x⟩ := p
    show (mk α hα n x)⁻¹ * mk α hα n x = 1
    rw [mk_inv, mk_mul_mk_same, inv_mul_cancel, one_eq_mk α hα n]

/-! ## Levels, the shift, and ranges -/

/-- The level-`n` embedding of `Γ` into the telescope. -/
def level (n : ℕ) : Γ →* Telescope α hα where
  toFun x := mk α hα n x
  map_one' := (one_eq_mk α hα n).symm
  map_mul' x y := (mk_mul_mk_same α hα n x y).symm

@[simp] theorem level_apply (n : ℕ) (x : Γ) : level α hα n x = mk α hα n x := rfl

include hα in
theorem level_injective (n : ℕ) : Function.Injective (level α hα n) := by
  intro x y h
  rw [level_apply, level_apply, mk_eq_mk_iff] at h
  exact iterateHom_injective hα n h

/-- The next level restricts to the current one along `α`. -/
theorem level_succ_comp (n : ℕ) :
    (level α hα (n + 1)).comp α = level α hα n := by
  ext x
  show mk α hα (n + 1) (α x) = mk α hα n x
  rw [mk_eq_mk_iff]
  exact (iterateHom_succ_apply α n x).symm

theorem level_succ_apply_hom (n : ℕ) (x : Γ) :
    level α hα (n + 1) (α x) = level α hα n x :=
  DFunLike.congr_fun (level_succ_comp α hα n) x

/-- The shift automorphism: `α` applied levelwise.  Its inverse moves an
element one level up. -/
def shift : Telescope α hα ≃* Telescope α hα where
  toFun := Quotient.map (fun p => (p.1, α p.2))
    (by
      rintro ⟨n, x⟩ ⟨m, y⟩ (h : iterateHom α m x = iterateHom α n y)
      show iterateHom α m (α x) = iterateHom α n (α y)
      rw [iterateHom_apply_hom, iterateHom_apply_hom, h])
  invFun := Quotient.map (fun p => (p.1 + 1, p.2))
    (by
      rintro ⟨n, x⟩ ⟨m, y⟩ (h : iterateHom α m x = iterateHom α n y)
      show iterateHom α (m + 1) x = iterateHom α (n + 1) y
      rw [iterateHom_succ_apply, iterateHom_succ_apply, iterateHom_apply_hom,
        iterateHom_apply_hom, h])
  left_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    obtain ⟨n, x⟩ := p
    show mk α hα (n + 1) (α x) = mk α hα n x
    rw [mk_eq_mk_iff]
    exact (iterateHom_succ_apply α n x).symm
  right_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    obtain ⟨n, x⟩ := p
    show mk α hα (n + 1) (α x) = mk α hα n x
    rw [mk_eq_mk_iff]
    exact (iterateHom_succ_apply α n x).symm
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
    obtain ⟨n, x⟩ := p; obtain ⟨m, y⟩ := q
    show mk α hα (n + m) (α (iterateHom α m x * iterateHom α n y)) =
      mk α hα n (α x) * mk α hα m (α y)
    rw [mk_mul_mk, map_mul, iterateHom_apply_hom, iterateHom_apply_hom]

@[simp] theorem shift_apply_mk (n : ℕ) (x : Γ) :
    shift α hα (mk α hα n x) = mk α hα n (α x) := rfl

@[simp] theorem shift_symm_apply_mk (n : ℕ) (x : Γ) :
    (shift α hα).symm (mk α hα n x) = mk α hα (n + 1) x := rfl

/-- The shift compresses each level copy of `Γ` along `α`. -/
theorem shift_level (n : ℕ) (x : Γ) :
    shift α hα (level α hα n x) = level α hα n (α x) := rfl

include hα in
/-- The range characterisation: one level up lies in the level-`n` copy
exactly on the range of `α`.  This is the whole content of Britton's lemma
needed by the marked non-MF word. -/
theorem level_succ_mem_range_level_iff (n : ℕ) (x : Γ) :
    level α hα (n + 1) x ∈ (level α hα n).range ↔ x ∈ α.range := by
  constructor
  · rintro ⟨y, hy⟩
    rw [level_apply, level_apply, mk_eq_mk_iff] at hy
    rw [iterateHom_succ_apply] at hy
    exact ⟨y, iterateHom_injective hα n hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (level_succ_apply_hom α hα n y).symm⟩

instance [Countable Γ] : Countable (Telescope α hα) :=
  Function.Surjective.countable (mk_surjective α hα)

end MappingTelescope
end GroupApproximation

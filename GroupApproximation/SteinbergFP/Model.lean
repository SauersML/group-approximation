import GroupApproximation.SteinbergFP.ResolventRing
import Mathlib.Algebra.Module.LinearMap.End

/-!
# `R_L` is not the zero ring

The ring `R_L` acts on the space `ℕ → ℚ` of rational sequences.  With `λ(m)` the number of
trailing `1` bits of `m`, put

    (t_b f)(n) = f(2n + b),   (s_b f)(m) = [m ≡ b mod 2] f(⌊m/2⌋),
    (N f)(m) = λ(m) f(m),     (A f)(m) = (λ(m) + 1)⁻¹ f(m),

with `s₁ = s_1`, `s₂ = s_0`, `t₁ = t_1`, `t₂ = t_0`.  These operators satisfy the nine resolvent
relations (`model_isResolventTuple`), because `λ(2n + 1) = λ(n) + 1` and `λ(2n) = 0`.  So every
relator of `R_L` acts as zero, and `R_L` maps to the nonzero ring `End_ℚ(ℕ → ℚ)`
(`resolventRing_nontrivial`).  In particular `ℚ → R_L` is injective.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

/-! ## Relators vanish under any resolvent tuple -/

section Lift

variable {B : Type*} [Ring B] {s₁ s₂ t₁ t₂ N A : B}

/-- The ring homomorphism `ℤ⟨X⟩ → B` sending the generators to a resolvent tuple. -/
def tupleLift (s₁ s₂ t₁ t₂ N A : B) : FreeAlgebra ℤ (Fin 6) →+* B :=
  (FreeAlgebra.lift ℤ ![s₁, s₂, t₁, t₂, N, A]).toRingHom

theorem tupleLift_gen (i : Fin 6) :
    tupleLift s₁ s₂ t₁ t₂ N A (gen i) = (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) i :=
  FreeAlgebra.lift_ι_apply _ _

theorem tupleLift_relator (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) {x : FreeAlgebra ℤ (Fin 6)}
    (hx : x ∈ resolventRelatorList) : tupleLift s₁ s₂ t₁ t₂ N A x = 0 := by
  have e0 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 0 = s₁ := rfl
  have e1 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 1 = s₂ := rfl
  have e2 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 2 = t₁ := rfl
  have e3 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 3 = t₂ := rfl
  have e4 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 4 = N := rfl
  have e5 : (![s₁, s₂, t₁, t₂, N, A] : Fin 6 → B) 5 = A := rfl
  simp only [resolventRelatorList, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_sub, map_mul, map_add, map_one, tupleLift_gen, e0, e1, e2, e3, e4, e5]
  · rw [h.t₁s₁, sub_self]
  · exact h.t₁s₂
  · exact h.t₂s₁
  · rw [h.t₂s₂, sub_self]
  · rw [h.sum, sub_self]
  · rw [h.Ns₁]; noncomm_ring
  · exact h.Ns₂
  · calc A * N + A - 1 = A * (N + 1) - 1 := by noncomm_ring
      _ = 0 := by rw [h.AN, sub_self]
  · calc N * A + A - 1 = (N + 1) * A - 1 := by noncomm_ring
      _ = 0 := by rw [h.NA, sub_self]

/-- A resolvent tuple in a nonzero ring makes `R_L` nonzero. -/
theorem resolventRing_nontrivial_of [Nontrivial B] (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) :
    Nontrivial ResolventRing := by
  have hle : TwoSidedIdeal.span resolventRelators ≤
      TwoSidedIdeal.ker (tupleLift s₁ s₂ t₁ t₂ N A) := by
    rw [TwoSidedIdeal.span_le]
    intro x hx
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
    exact tupleLift_relator h hx
  refine ⟨⟨0, 1, fun h01 ↦ ?_⟩⟩
  have h1 : (1 : FreeAlgebra ℤ (Fin 6)) ∈ TwoSidedIdeal.ker resolventMk := by
    rw [TwoSidedIdeal.mem_ker, map_one]
    exact h01.symm
  rw [ker_resolventMk] at h1
  have h2 := (TwoSidedIdeal.mem_ker _).mp (hle h1)
  rw [map_one] at h2
  exact one_ne_zero h2

end Lift

/-! ## The sequence model -/

/-- The number of trailing `1` bits. -/
def trailOnes (m : ℕ) : ℕ :=
  if _h : m % 2 = 1 then trailOnes (m / 2) + 1 else 0
decreasing_by omega

theorem trailOnes_odd (n : ℕ) : trailOnes (2 * n + 1) = trailOnes n + 1 := by
  rw [trailOnes, dif_pos (show (2 * n + 1) % 2 = 1 by omega),
    show (2 * n + 1) / 2 = n by omega]

theorem trailOnes_even (n : ℕ) : trailOnes (2 * n) = 0 := by
  rw [trailOnes, dif_neg (show ¬ (2 * n) % 2 = 1 by omega)]

/-- `(t_b f)(n) = f(2n + b)`. -/
def modelT (b : ℕ) : Module.End ℚ (ℕ → ℚ) where
  toFun f n := f (2 * n + b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `(s_b f)(m) = [m % 2 = b] f(m / 2)`. -/
def modelS (b : ℕ) : Module.End ℚ (ℕ → ℚ) where
  toFun f m := if m % 2 = b then f (m / 2) else 0
  map_add' f g := by
    funext m
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- Multiplication by a sequence of weights. -/
def modelD (w : ℕ → ℚ) : Module.End ℚ (ℕ → ℚ) where
  toFun f m := w m * f m
  map_add' f g := by
    funext m
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem modelT_apply (b : ℕ) (f : ℕ → ℚ) (n : ℕ) : modelT b f n = f (2 * n + b) := rfl
@[simp] theorem modelS_apply (b : ℕ) (f : ℕ → ℚ) (m : ℕ) :
    modelS b f m = if m % 2 = b then f (m / 2) else 0 := rfl
@[simp] theorem modelD_apply (w : ℕ → ℚ) (f : ℕ → ℚ) (m : ℕ) : modelD w f m = w m * f m := rfl

/-- The operator `N`. -/
abbrev modelN : Module.End ℚ (ℕ → ℚ) := modelD fun m ↦ (trailOnes m : ℚ)

/-- The operator `A = (N + 1)⁻¹`. -/
abbrev modelA : Module.End ℚ (ℕ → ℚ) := modelD fun m ↦ ((trailOnes m : ℚ) + 1)⁻¹

theorem model_ext {P Q : Module.End ℚ (ℕ → ℚ)} (h : ∀ f m, P f m = Q f m) : P = Q :=
  LinearMap.ext fun f ↦ funext fun m ↦ h f m

theorem modelS_apply_two_mul_add (b c n : ℕ) (hc : c < 2) (f : ℕ → ℚ) :
    modelS b f (2 * n + c) = if c = b then f n else 0 := by
  rw [modelS_apply, show (2 * n + c) % 2 = c by omega, show (2 * n + c) / 2 = n by omega]

theorem exists_two_mul_add (m : ℕ) : ∃ q r, r < 2 ∧ m = 2 * q + r :=
  ⟨m / 2, m % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 2).symm⟩

theorem inv_mul_add_self' (a b : ℚ) (ha : a + 1 ≠ 0) : (a + 1)⁻¹ * (a * b + b) = b := by
  rw [show a * b + b = (a + 1) * b by ring, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem mul_inv_add_self' (a b : ℚ) (ha : a + 1 ≠ 0) :
    a * ((a + 1)⁻¹ * b) + (a + 1)⁻¹ * b = b := by
  rw [show a * ((a + 1)⁻¹ * b) + (a + 1)⁻¹ * b = (a + 1) * ((a + 1)⁻¹ * b) by ring,
    mul_inv_cancel_left₀ ha]

/-- **The sequence model satisfies the resolvent relations.** -/
theorem model_isResolventTuple :
    IsResolventTuple (modelS 1) (modelS 0) (modelT 1) (modelT 0) modelN modelA := by
  have hne : ∀ m, ((trailOnes m : ℚ) + 1) ≠ 0 := fun m ↦ by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine model_ext fun f n ↦ ?_
    change modelS 1 f (2 * n + 1) = f n
    rw [modelS_apply_two_mul_add 1 1 n (by norm_num), if_pos rfl]
  · refine model_ext fun f n ↦ ?_
    change modelS 0 f (2 * n + 1) = 0
    rw [modelS_apply_two_mul_add 0 1 n (by norm_num), if_neg one_ne_zero]
  · refine model_ext fun f n ↦ ?_
    change modelS 1 f (2 * n + 0) = 0
    rw [modelS_apply_two_mul_add 1 0 n (by norm_num), if_neg zero_ne_one]
  · refine model_ext fun f n ↦ ?_
    change modelS 0 f (2 * n + 0) = f n
    rw [modelS_apply_two_mul_add 0 0 n (by norm_num), if_pos rfl]
  · refine model_ext fun f m ↦ ?_
    change modelS 1 (modelT 1 f) m + modelS 0 (modelT 0 f) m = f m
    obtain ⟨q, r, hr, rfl⟩ := exists_two_mul_add m
    rw [modelS_apply_two_mul_add 1 r q hr, modelS_apply_two_mul_add 0 r q hr, modelT_apply,
      modelT_apply]
    interval_cases r <;> simp
  · refine model_ext fun f m ↦ ?_
    change (trailOnes m : ℚ) * modelS 1 f m = modelS 1 ((modelN + 1) f) m
    obtain ⟨q, r, hr, rfl⟩ := exists_two_mul_add m
    rw [modelS_apply_two_mul_add 1 r q hr, modelS_apply_two_mul_add 1 r q hr]
    interval_cases r
    · simp
    · rw [if_pos rfl, if_pos rfl, trailOnes_odd, LinearMap.add_apply, Pi.add_apply,
        modelD_apply, Module.End.one_apply]
      push_cast
      ring
  · refine model_ext fun f m ↦ ?_
    change (trailOnes m : ℚ) * modelS 0 f m = 0
    obtain ⟨q, r, hr, rfl⟩ := exists_two_mul_add m
    rw [modelS_apply_two_mul_add 0 r q hr]
    interval_cases r
    · rw [if_pos rfl, add_zero, trailOnes_even, Nat.cast_zero, zero_mul]
    · rw [if_neg one_ne_zero, mul_zero]
  · refine model_ext fun f m ↦ ?_
    change ((trailOnes m : ℚ) + 1)⁻¹ * ((trailOnes m : ℚ) * f m + f m) = f m
    exact inv_mul_add_self' _ _ (hne m)
  · refine model_ext fun f m ↦ ?_
    change (trailOnes m : ℚ) * (((trailOnes m : ℚ) + 1)⁻¹ * f m) +
      ((trailOnes m : ℚ) + 1)⁻¹ * f m = f m
    exact mul_inv_add_self' _ _ (hne m)

/-- **`R_L` is not the zero ring.** -/
instance resolventRing_nontrivial : Nontrivial ResolventRing :=
  resolventRing_nontrivial_of model_isResolventTuple

/-- **`ℚ ⊆ R_L`.** -/
theorem resolventRatHom_injective : Function.Injective isResolventTuple.ratHom :=
  isResolventTuple.ratHom.injective

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.resolventRing_nontrivial
#audit_axioms GroupApproximation.SteinbergFP.resolventRatHom_injective

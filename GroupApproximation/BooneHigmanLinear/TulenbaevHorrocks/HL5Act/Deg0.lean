import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL5.Torsor
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.B0Maps
import GroupApproximation.Meta.AxiomGuard

/-!
# H.L5: the operators of degree `≤ 0` on `V̄_T` (lane pal-q111)

Lavrenov–Sinchuk, arXiv:1909.02637, formula (5.19), transported to k2-hl25b's `HL5.VbarT` by
(5.16).  Over a local ring `A` with maximal ideal `𝔪`, an element `σ` of `St_N(B₀)`,
`B₀ = A + 𝔪 X A[X]` (`Graded.horrB0 𝔪`), acts by
`σ · [p, h, u] = [ι(σ) · p · j(σ₀)⁻¹, i₋(σ₀) · h, u]`.
Here `ι : St_N(B₀) → St_N(A[T,T⁻¹])` is the inclusion, `σ₀ ∈ St_N(A)` is `σ` at `X = 0`, `j` is
the constant map to `St_N(A[T,T⁻¹])` and `i₋` the constant map to `St_N(A[X])`.  On generators this
is `x_α(a + Xf) · [p, h, u] = [x_α(a + Xf) · p · x_α(-a), x_α(a) · h, u]`.

* `mem_gBar_B0`: `ι(σ) · j(σ₀)⁻¹ ∈ Ḡ^{≥0}_M`.  This is where `𝔪 X A[X] ⊆ B₀` is used: modulo `𝔪`,
  an element of `B₀` is its constant term (`Graded.resPoly_comp_toPolyB0`).
* `act0 A N : St_N(B₀) →* Equiv.Perm (V̄_T)`, the action.
* `act0_mk`: its value on `[p, h, u]`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL5Act

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev
open GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL5
open GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded

variable (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ)

/-- `B₀ = A + 𝔪 X A[X]`. -/
abbrev B0m : Subring (LaurentPolynomial A) :=
  horrB0 (IsLocalRing.maximalIdeal A)

/-- The inclusion `St_N(B₀) → St_N(A[T,T⁻¹])`. -/
abbrev iota0 : SteinbergGroup (Fin N) (B0m A) →* SteinbergGroup (Fin N) (LaurentPolynomial A) :=
  ringMap (B0m A).subtype

/-- Evaluation at `X = 0`, `St_N(B₀) → St_N(A)`. -/
abbrev ev0 : SteinbergGroup (Fin N) (B0m A) →* SteinbergGroup (Fin N) A :=
  ringMap (ev0B0 (IsLocalRing.maximalIdeal A))

/-- The constants in `St_N(A[T,T⁻¹])`. -/
abbrev jC : SteinbergGroup (Fin N) A →* SteinbergGroup (Fin N) (LaurentPolynomial A) :=
  ringMap (LaurentPolynomial.C : A →+* LaurentPolynomial A)

/-- The constants in `St_N(A[X])`. -/
abbrev iC : SteinbergGroup (Fin N) A →* SteinbergGroup (Fin N) A[X] :=
  ringMap (Polynomial.C : A →+* A[X])

variable {A N}

theorem jC_eq (γ : SteinbergGroup (Fin N) A) :
    jC A N γ = ringMap (toLaurentPos A) (iC A N γ) := by
  rw [ringMap_ringMap, toLaurentPos_comp_C]

theorem conj_mem_gBar (y : SteinbergGroup (Fin N) A[X])
    {p : SteinbergGroup (Fin N) (LaurentPolynomial A)} (hp : p ∈ gBar A N) :
    ringMap (toLaurentPos A) y * p * (ringMap (toLaurentPos A) y)⁻¹ ∈ gBar A N := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hp
  refine Subgroup.mem_map.mpr ⟨y * k * y⁻¹, (MonoidHom.normal_ker _).conj_mem k hk y, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem jC_mem_gBar {γ : SteinbergGroup (Fin N) A} (hγ : γ ∈ gZero A N) : jC A N γ ∈ gBar A N := by
  refine Subgroup.mem_map.mpr ⟨iC A N γ, ?_, (jC_eq γ).symm⟩
  rw [MonoidHom.mem_ker, ringMap_ringMap, Polynomial.mapRingHom_comp_C, ← ringMap_ringMap]
  change ringMap Polynomial.C (ringMap (IsLocalRing.residue A) γ) = 1
  rw [MonoidHom.mem_ker.mp hγ, map_one]

/-- **`ι(σ) · j(σ₀)⁻¹ ∈ Ḡ^{≥0}_M`** for `σ ∈ St_N(B₀)`. -/
theorem mem_gBar_B0 (σ : SteinbergGroup (Fin N) (B0m A)) :
    iota0 A N σ * (jC A N (ev0 A N σ))⁻¹ ∈ gBar A N := by
  have hτ : iota0 A N σ =
      ringMap (toLaurentPos A) (ringMap (toPolyB0 (IsLocalRing.maximalIdeal A)) σ) := by
    rw [ringMap_ringMap, toLaurentPos_comp_toPolyB0]
  have hker : ringMap (toPolyB0 (IsLocalRing.maximalIdeal A)) σ * (iC A N (ev0 A N σ))⁻¹ ∈
      (ringMap (I := Fin N) (resPoly A)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, ringMap_ringMap,
      resPoly_comp_toPolyB0, ringMap_ringMap, ringMap_ringMap, ← RingHom.comp_assoc,
      Polynomial.mapRingHom_comp_C]
  refine Subgroup.mem_map.mpr ⟨_, hker, ?_⟩
  rw [map_mul, map_inv, ← hτ, ← jC_eq]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL5Act.mem_gBar_B0

/-- The new first coordinate of `σ · [p, h, u]`. -/
theorem act0_mem (σ : SteinbergGroup (Fin N) (B0m A)) (p : gBar A N) :
    iota0 A N σ * (p : SteinbergGroup (Fin N) (LaurentPolynomial A)) *
      (jC A N (ev0 A N σ))⁻¹ ∈ gBar A N := by
  have h1 := mem_gBar_B0 σ
  have h2 := conj_mem_gBar (iC A N (ev0 A N σ)) p.2
  rw [← jC_eq] at h2
  have heq : iota0 A N σ * (p : SteinbergGroup (Fin N) (LaurentPolynomial A)) *
      (jC A N (ev0 A N σ))⁻¹ = (iota0 A N σ * (jC A N (ev0 A N σ))⁻¹) *
        (jC A N (ev0 A N σ) * p * (jC A N (ev0 A N σ))⁻¹) := by
    group
  rw [heq]
  exact (gBar A N).mul_mem h1 h2

variable (A N)

/-- `σ · (p, h, u)` on triples. -/
noncomputable def act0Triple (σ : SteinbergGroup (Fin N) (B0m A)) (t : Triple A N) : Triple A N :=
  (⟨iota0 A N σ * t.1 * (jC A N (ev0 A N σ))⁻¹, act0_mem σ t.1⟩,
    iC A N (ev0 A N σ) * t.2.1, t.2.2)

variable {A N}

theorem act0Triple_rel (σ : SteinbergGroup (Fin N) (B0m A)) {t t' : Triple A N}
    (h : Rel A N t t') : Rel A N (act0Triple A N σ t) (act0Triple A N σ t') := by
  obtain ⟨hu, γ, hγ, h1, h2⟩ := h
  refine ⟨hu, ev0 A N σ * γ * (ev0 A N σ)⁻¹,
    (MonoidHom.normal_ker _).conj_mem γ hγ (ev0 A N σ), ?_, ?_⟩
  · change iota0 A N σ * (t'.1 : SteinbergGroup (Fin N) (LaurentPolynomial A)) *
        (jC A N (ev0 A N σ))⁻¹ =
      iota0 A N σ * t.1 * (jC A N (ev0 A N σ))⁻¹ * jC A N (ev0 A N σ * γ * (ev0 A N σ)⁻¹)
    rw [h1]
    simp only [map_mul, map_inv]
    group
  · change iC A N (ev0 A N σ) * t'.2.1 =
      (iC A N (ev0 A N σ * γ * (ev0 A N σ)⁻¹))⁻¹ * (iC A N (ev0 A N σ) * t.2.1)
    rw [h2]
    simp only [map_mul, map_inv]
    group

theorem act0Triple_one (t : Triple A N) : act0Triple A N 1 t = t := by
  obtain ⟨p, h, u⟩ := t
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · change iota0 A N 1 * (p : SteinbergGroup (Fin N) (LaurentPolynomial A)) *
      (jC A N (ev0 A N 1))⁻¹ = p
    simp only [map_one, inv_one, one_mul, mul_one]
  · change iC A N (ev0 A N 1) * h = h
    simp only [map_one, one_mul]

theorem act0Triple_mul (σ τ : SteinbergGroup (Fin N) (B0m A)) (t : Triple A N) :
    act0Triple A N (σ * τ) t = act0Triple A N σ (act0Triple A N τ t) := by
  obtain ⟨p, h, u⟩ := t
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · change iota0 A N (σ * τ) * (p : SteinbergGroup (Fin N) (LaurentPolynomial A)) *
      (jC A N (ev0 A N (σ * τ)))⁻¹ =
        iota0 A N σ * (iota0 A N τ * p * (jC A N (ev0 A N τ))⁻¹) * (jC A N (ev0 A N σ))⁻¹
    simp only [map_mul]
    group
  · change iC A N (ev0 A N (σ * τ)) * h = iC A N (ev0 A N σ) * (iC A N (ev0 A N τ) * h)
    simp only [map_mul, mul_assoc]

variable (A N)

/-- `σ · -` on `V̄_T`. -/
noncomputable def act0Fun (σ : SteinbergGroup (Fin N) (B0m A)) : VbarT A N → VbarT A N :=
  Quotient.map (act0Triple A N σ) fun _ _ h => act0Triple_rel σ h

variable {A N}

theorem act0Fun_mk (σ : SteinbergGroup (Fin N) (B0m A)) (t : Triple A N) :
    act0Fun A N σ (Quotient.mk (setoid A N) t) = Quotient.mk (setoid A N) (act0Triple A N σ t) :=
  rfl

theorem act0Fun_one (v : VbarT A N) : act0Fun A N 1 v = v := by
  induction v using Quotient.inductionOn with
  | h t => rw [act0Fun_mk, act0Triple_one]

theorem act0Fun_mul (σ τ : SteinbergGroup (Fin N) (B0m A)) (v : VbarT A N) :
    act0Fun A N (σ * τ) v = act0Fun A N σ (act0Fun A N τ v) := by
  induction v using Quotient.inductionOn with
  | h t => rw [act0Fun_mk, act0Fun_mk, act0Fun_mk, act0Triple_mul]

variable (A N)

/-- **The degree-`≤ 0` operators** (L–S (5.19)) as a homomorphism `St_N(B₀) →* Perm(V̄_T)`. -/
noncomputable def act0 : SteinbergGroup (Fin N) (B0m A) →* Equiv.Perm (VbarT A N) where
  toFun σ :=
    { toFun := act0Fun A N σ
      invFun := act0Fun A N σ⁻¹
      left_inv := fun v => by rw [← act0Fun_mul, inv_mul_cancel, act0Fun_one]
      right_inv := fun v => by rw [← act0Fun_mul, mul_inv_cancel, act0Fun_one] }
  map_one' := Equiv.ext fun v => act0Fun_one v
  map_mul' σ τ := Equiv.ext fun v => act0Fun_mul σ τ v

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL5Act.act0

variable {A N}

/-- **(5.19) in the `V̄_T` form**:
`σ · [p, h, u] = [ι(σ) · p · j(σ₀)⁻¹, i₋(σ₀) · h, u]`. -/
theorem act0_mk (σ : SteinbergGroup (Fin N) (B0m A)) (p : gBar A N)
    (h : SteinbergGroup (Fin N) A[X]) (u : unitsOneAddM A) :
    act0 A N σ (mk A N p h u) =
      mk A N ⟨iota0 A N σ * p * (jC A N (ev0 A N σ))⁻¹, act0_mem σ p⟩
        (iC A N (ev0 A N σ) * h) u :=
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL5Act.act0_mk

end HL5Act
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation

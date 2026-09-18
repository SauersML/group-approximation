import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylConj
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 3: the constant torus against `W` and `τ`

Lane `bh-met-93d`.  `t(γ) = k2PolyDeg_torus γ = C(h_mL(γ))` for `γ ∈ F_pˣ`, `W = w_mL(-1)`:

* `k2PolyNagaoWeyl_W_conj_torus`: `W⁻¹ t(γ) W = t(γ⁻¹)` (computed over the field `F_p`,
  `k2PolyNagaoWeyl_field_w_conj_h`, then transported along `C`);
* `k2PolyNagaoWeyl_W_mul_W`: `W W = t(-1)`;
* `k2PolyNagaoWeyl_torus_mul_x`: `t(δ) x'(f) = x'(δ⁻² f) t(δ)`;
* `k2PolyNagaoWeyl_tau_C`: `τ(C β) = t(β)⁻¹`, and every unit of `F_p[X]` is some `C β`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)

variable {I : Type} [Fintype I] [DecidableEq I]

section Field

variable {F : Type*} [Field F] (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

/-- Over a field, `w(1) w(u) w(1)⁻¹ = w(u⁻¹)`. -/
theorem k2PolyNagaoWeyl_field_w_conj_w (u : Fˣ) :
    w i j hij (1 : Fˣ) * w i j hij u * (w i j hij (1 : Fˣ))⁻¹ = w i j hij u⁻¹ := by
  rw [show w i j hij u = x i j hij (u : F) * x j i hij.symm (-((u⁻¹ : Fˣ) : F)) *
      x i j hij (u : F) from rfl, FieldK2.conj_mul_three,
    FieldK2.w_conj_x_self i j k hij hik hjk (1 : Fˣ),
    FieldK2.w_conj_x_self_symm i j k hij hik hjk (1 : Fˣ),
    FieldK2.w_eq_alt i j k hij hik hjk u⁻¹]
  simp only [Units.val_one, inv_one, one_mul, mul_one, neg_neg, inv_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_field_w_conj_w

/-- Over a field, `w(1) h(u) w(1)⁻¹ = h(u⁻¹)`. -/
theorem k2PolyNagaoWeyl_field_w_conj_h (u : Fˣ) :
    w i j hij (1 : Fˣ) * h i j hij u * (w i j hij (1 : Fˣ))⁻¹ = h i j hij u⁻¹ := by
  have e : w i j hij (1 : Fˣ) * h i j hij u * (w i j hij (1 : Fˣ))⁻¹ =
      (w i j hij (1 : Fˣ) * w i j hij u * (w i j hij (1 : Fˣ))⁻¹) *
        (w i j hij (1 : Fˣ) * w i j hij (-1 : Fˣ) * (w i j hij (1 : Fˣ))⁻¹) := by
    rw [show h i j hij u = w i j hij u * w i j hij (-1 : Fˣ) from rfl]
    group
  rw [e, k2PolyNagaoWeyl_field_w_conj_w i j k hij hik hjk u,
    k2PolyNagaoWeyl_field_w_conj_w i j k hij hik hjk (-1 : Fˣ), inv_neg, inv_one]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_field_w_conj_h

end Field

variable {p : ℕ} [Fact p.Prime]

/-- `C` sends the unit `-1` to `-1`. -/
theorem k2PolyNagaoWeyl_units_map_neg_one :
    Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom (-1) = -1 :=
  Units.ext (show Polynomial.C (-(1 : ZMod p)) = -(1 : Polynomial (ZMod p)) by
    rw [map_neg, map_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_units_map_neg_one

/-- Every unit of `F_p[X]` is a constant `C β`. -/
theorem k2PolyNagaoWeyl_exists_C_of_isUnit {b : Polynomial (ZMod p)} (hb : IsUnit b) :
    ∃ β : (ZMod p)ˣ, b = Polynomial.C (β : ZMod p) := by
  obtain ⟨r, hr, hrb⟩ := Polynomial.isUnit_iff.1 hb
  exact ⟨hr.unit, by rw [hr.unit_spec, hrb]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_exists_C_of_isUnit

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

/-- The torus is `C ∘ h_mL` on the nose. -/
theorem k2PolyNagaoWeyl_torus_eq (γ : (ZMod p)ˣ) :
    k2PolyDeg_torus p m L n hmL hmn hLn γ =
      ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p)) (h m L hmL γ) := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_torus_eq

/-- `W⁻¹ t(γ) W = t(γ⁻¹)`. -/
theorem k2PolyNagaoWeyl_W_conj_torus (γ : (ZMod p)ˣ) :
    (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ * k2PolyDeg_torus p m L n hmL hmn hLn γ *
      w m L hmL (-1 : (Polynomial (ZMod p))ˣ) = k2PolyDeg_torus p m L n hmL hmn hLn γ⁻¹ := by
  have hW : ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p))
      (w m L hmL (1 : (ZMod p)ˣ)) = (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ := by
    rw [k2PolyDeg_ringMap_w, map_one, w_inv, neg_neg]
  have hW' : w m L hmL (-1 : (Polynomial (ZMod p))ˣ) =
      (ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p))
        (w m L hmL (1 : (ZMod p)ˣ)))⁻¹ := by
    rw [hW, inv_inv]
  rw [k2PolyNagaoWeyl_torus_eq, k2PolyNagaoWeyl_torus_eq, ← hW, hW', ← map_inv, ← map_mul,
    ← map_mul, k2PolyNagaoWeyl_field_w_conj_h m L n hmL hmn hLn γ]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_W_conj_torus

/-- `W W = t(-1)`. -/
theorem k2PolyNagaoWeyl_W_mul_W :
    w m L hmL (-1 : (Polynomial (ZMod p))ˣ) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) =
      k2PolyDeg_torus p m L n hmL hmn hLn (-1) := by
  rw [k2PolyDeg_torus_apply, k2PolyNagaoWeyl_units_map_neg_one]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_W_mul_W

/-- `t(δ) x'(f) = x'(δ⁻¹ f δ⁻¹) t(δ)`. -/
theorem k2PolyNagaoWeyl_torus_mul_x (δ : (ZMod p)ˣ) (f : Polynomial (ZMod p)) :
    k2PolyDeg_torus p m L n hmL hmn hLn δ * x L m hmL.symm f =
      x L m hmL.symm (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * f *
        Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p)) * k2PolyDeg_torus p m L n hmL hmn hLn δ := by
  have e : k2PolyDeg_torus p m L n hmL hmn hLn δ * x L m hmL.symm f *
      (k2PolyDeg_torus p m L n hmL hmn hLn δ)⁻¹ =
      x L m hmL.symm (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * f *
        Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
    rw [k2PolyDeg_torus_apply]
    exact k2PolyNagaoWeyl_h_conj hmL hmn hLn _ f
  rw [← e]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_torus_mul_x

/-- `τ(C β) = t(β)⁻¹`. -/
theorem k2PolyNagaoWeyl_tau_C (β : (ZMod p)ˣ) :
    k2PolyNagaoSigma_tau p m L hmL (Polynomial.C (β : ZMod p)) =
      (k2PolyDeg_torus p m L n hmL hmn hLn β)⁻¹ := by
  by_cases h1 : Polynomial.C (β : ZMod p) = 1
  · have hβ : β = 1 := Units.ext (Polynomial.C_injective (h1.trans Polynomial.C_1.symm))
    rw [k2PolyNagaoSigma_tau, if_pos h1, hβ, map_one, inv_one]
  · have hu : IsUnit (Polynomial.C (β : ZMod p)) := β.isUnit.map Polynomial.C
    have e : hu.unit = Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom β :=
      Units.ext hu.unit_spec
    rw [k2PolyNagaoSigma_tau, if_neg h1, dif_pos hu, k2PolyDeg_torus_apply, e]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_tau_C

end GroupApproximation.BooneHigman.Metabelian.ElemFP

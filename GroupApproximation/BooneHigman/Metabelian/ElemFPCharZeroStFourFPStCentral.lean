import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStScale
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers of torus elements and a central element of `St_I(R)` (bh-met-91m)

* `czStFourFP_H_zpow_conj`: `H_ab(v)ⁿ x_ij(r) H_ab(v)⁻ⁿ = x_ij((v ^ χ)ⁿ r)`.
* `czStFourFP_H_central`: `(H_cd(w) H_ab(v))⁻¹ (H_ab(v) H_cd(w))` is central in `St_I(R)`.
  Conjugation by `H_ab(v) H_cd(w)` and by `H_cd(w) H_ab(v)` agree on every generator, since
  both scale `x_ij` by `v ^ χ_ab(i,j) w ^ χ_cd(i,j)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- Conjugation by a product. -/
theorem czStFourFP_conj_prod {G : Type*} [Group G] (g₁ g₂ y : G) :
    g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_prod

/-- If conjugation by `p` and by `q` agree on `y`, then `y` commutes with `q⁻¹ p`. -/
theorem czStFourFP_comm_of_conj_eq {G : Type*} [Group G] {p q y : G}
    (h : p * y * p⁻¹ = q * y * q⁻¹) : y * (q⁻¹ * p) = q⁻¹ * p * y := by
  calc y * (q⁻¹ * p) = q⁻¹ * (q * y * q⁻¹) * p := by
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = q⁻¹ * (p * y * p⁻¹) * p := by rw [h]
    _ = q⁻¹ * p * y := by simp only [mul_assoc, inv_mul_cancel, mul_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_comm_of_conj_eq

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- Integer powers of a torus element. -/
theorem czStFourFP_H_zpow_conj (hthird : ∀ a b : I, ∃ k, k ≠ a ∧ k ≠ b) (a b : I)
    (hab : a ≠ b) (v : Rˣ) (i j : I) (hij : i ≠ j) (n : ℤ) (r : R) :
    czStFourFP_H a b hab v ^ n * SteinbergGroup.x i j hij r * (czStFourFP_H a b hab v ^ n)⁻¹ =
      SteinbergGroup.x i j hij ((((v ^ czStFourFP_chi a b i j) ^ n : Rˣ) : R) * r) :=
  czStFourFP_conj_zpow_iter (f := SteinbergGroup.x i j hij)
    (czStFourFP_H_conj hthird a b hab v i j hij) n r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_zpow_conj

/-- Conjugations by `H_ab(v) H_cd(w)` and by `H_cd(w) H_ab(v)` agree on generators. -/
theorem czStFourFP_H_conj_comm (hthird : ∀ a b : I, ∃ k, k ≠ a ∧ k ≠ b) (a b c d : I)
    (hab : a ≠ b) (hcd : c ≠ d) (v w : Rˣ) (i j : I) (hij : i ≠ j) (r : R) :
    czStFourFP_H a b hab v * czStFourFP_H c d hcd w * SteinbergGroup.x i j hij r *
        (czStFourFP_H a b hab v * czStFourFP_H c d hcd w)⁻¹ =
      czStFourFP_H c d hcd w * czStFourFP_H a b hab v * SteinbergGroup.x i j hij r *
        (czStFourFP_H c d hcd w * czStFourFP_H a b hab v)⁻¹ := by
  rw [czStFourFP_conj_prod, czStFourFP_conj_prod, czStFourFP_H_conj hthird c d hcd w,
    czStFourFP_H_conj hthird a b hab v, czStFourFP_H_conj hthird a b hab v,
    czStFourFP_H_conj hthird c d hcd w, mul_left_comm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_conj_comm

/-- **Centrality.**  `(H_cd(w) H_ab(v))⁻¹ (H_ab(v) H_cd(w))` is central in `St_I(R)`. -/
theorem czStFourFP_H_central (hthird : ∀ a b : I, ∃ k, k ≠ a ∧ k ≠ b) (a b c d : I)
    (hab : a ≠ b) (hcd : c ≠ d) (v w : Rˣ) (g : SteinbergGroup I R) :
    g * ((czStFourFP_H c d hcd w * czStFourFP_H a b hab v)⁻¹ *
        (czStFourFP_H a b hab v * czStFourFP_H c d hcd w)) =
      (czStFourFP_H c d hcd w * czStFourFP_H a b hab v)⁻¹ *
        (czStFourFP_H a b hab v * czStFourFP_H c d hcd w) * g :=
  czStFourFP_commute_of_commute_of (fun gen => by
    obtain ⟨i, j, hij, r⟩ := gen
    exact czStFourFP_comm_of_conj_eq
      (czStFourFP_H_conj_comm hthird a b c d hab hcd v w i j hij r)) g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_central

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

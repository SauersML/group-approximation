import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresAdj
import GroupApproximation.Meta.AxiomGuard

/-!
# `ψ` is surjective (k2-poly, piece F.3, part 3)

Tulenbaev, proof of Prop 1.6.
* `psi_conj`: `ψ(y) X_{v,w} ψ(y)⁻¹ = X_{π(y) v, w π(y)⁻¹}`, by induction on `y`.
* `inr_mem_range`: `ψ(xᵢⱼ(ι b)) = xᵢⱼ(b)`.
* `inl_mem_range`: write `v = g eᵢ` with `g = π(y) ∈ E(A)`. Then `X_{v,w}` is `ψ(y)`-conjugate to
  `X_{eᵢ, w g}`. The row `u = w g` has `uᵢ = 0` and entries in `ker ρ`, so
  `X_{eᵢ,u} = ∏ⱼ X_{eᵢ, uⱼ eⱼ} = ∏ⱼ ψ(xᵢⱼ(uⱼ))`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair stdPair)

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  (ι : B →+* A) (ρ : A →+* B) (hρ : ∀ b, ρ (ι b) = b)

theorem inr_conj_inl (g : SteinbergGroup I B) (n : RelSt I A (RingHom.ker ρ)) :
    (SemidirectProduct.inr g : SD I ι ρ) * SemidirectProduct.inl n * (SemidirectProduct.inr g)⁻¹ =
      SemidirectProduct.inl (stAct ι ρ g n) := by
  rw [inr_mul_inl, mul_inv_cancel_right]

#audit_axioms inr_conj_inl

/-- **Conjugation by `ψ(y)`** acts on the generators through `π(y) ∈ E(A)`. -/
theorem psi_conj (y : SteinbergGroup I A) (q : (I → A) × (I → A))
    (hq : RMem (RingHom.ker ρ) q) :
    psi ι ρ hρ y * SemidirectProduct.inl (X q hq) * (psi ι ρ hρ y)⁻¹ =
      SemidirectProduct.inl (X (smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)
        q) (smulPair_mem (projection y).2 hq)) := by
  let S : Subgroup (SteinbergGroup I A) :=
    { carrier := {y | ∀ q (hq : RMem (RingHom.ker ρ) q),
        psi ι ρ hρ y * SemidirectProduct.inl (X q hq) * (psi ι ρ hρ y)⁻¹ =
          SemidirectProduct.inl (X (smulPair ((projection y : elementaryGroup I A) :
            (Matrix I I A)ˣ) q) (smulPair_mem (projection y).2 hq))}
      one_mem' := fun q hq => by
        rw [map_one (psi ι ρ hρ), one_mul, inv_one, mul_one]
        exact congrArg _ (X_congr (by rw [map_one]; exact (smulPair_one q).symm) _ _)
      mul_mem' := fun {y z} hy hz q hq => by
        rw [map_mul (psi ι ρ hρ), mul_inv_rev, show psi ι ρ hρ y * psi ι ρ hρ z *
          SemidirectProduct.inl (X q hq) * ((psi ι ρ hρ z)⁻¹ * (psi ι ρ hρ y)⁻¹) =
          psi ι ρ hρ y * (psi ι ρ hρ z * SemidirectProduct.inl (X q hq) * (psi ι ρ hρ z)⁻¹) *
            (psi ι ρ hρ y)⁻¹ by group, hz, hy]
        exact congrArg _ (X_congr (by rw [map_mul, Subgroup.coe_mul, smulPair_mul]) _ _)
      inv_mem' := fun {y} hy q hq => by
        have h := hy (smulPair ((projection y⁻¹ : elementaryGroup I A) : (Matrix I I A)ˣ) q)
          (smulPair_mem (projection y⁻¹).2 hq)
        rw [X_congr (show smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)
          (smulPair ((projection y⁻¹ : elementaryGroup I A) : (Matrix I I A)ˣ) q) = q by
            rw [← smulPair_mul, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
              Subgroup.coe_one, smulPair_one]) _ hq] at h
        rw [map_inv (psi ι ρ hρ) y, inv_inv, ← h]
        group }
  have hy : y ∈ S := by
    refine PresentedGroup.generated_by _ S ?_ y
    rintro ⟨k, l, hkl, a⟩
    show ∀ q (hq : RMem (RingHom.ker ρ) q), _
    intro q hq
    change psi ι ρ hρ (x k l hkl a) * SemidirectProduct.inl (X q hq) *
        (psi ι ρ hρ (x k l hkl a))⁻¹ =
      SemidirectProduct.inl (X (smulPair ((projection (x k l hkl a) : elementaryGroup I A) :
        (Matrix I I A)ˣ) q) (smulPair_mem (projection (x k l hkl a)).2 hq))
    have hc1 := rmem_conjPair_std (𝔄 := RingHom.ker ρ) hkl (ι (ρ a)) hq
    have hc2 := rmem_conjPair_std (𝔄 := RingHom.ker ρ) hkl (a - ι (ρ a)) hc1
    rw [psi_x]
    unfold psiX
    rw [show ∀ (m n : SD I ι ρ), m * n * SemidirectProduct.inl (X q hq) * (m * n)⁻¹ =
        m * (n * SemidirectProduct.inl (X q hq) * n⁻¹) * m⁻¹ from fun m n => by group,
      inr_conj_inl, stAct_x ι ρ hkl (ρ a) q hq hc1, ← map_inv, ← map_mul, ← map_mul,
      X_conj _ _ (rmem_std hkl (sub_mem_ker ι ρ hρ a)) hc1 hc2]
    refine congrArg _ (X_congr ?_ _ _)
    rw [projection_x, elementaryRoot_val, ← smulPair_elementaryUnit hkl,
      ← smulPair_elementaryUnit hkl, ← smulPair_mul, elementaryUnit_mul, sub_add_cancel]
  exact (show ∀ q (hq : RMem (RingHom.ker ρ) q),
    psi ι ρ hρ y * SemidirectProduct.inl (X q hq) * (psi ι ρ hρ y)⁻¹ =
      SemidirectProduct.inl (X (smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)
        q) (smulPair_mem (projection y).2 hq)) from hy) q hq

#audit_axioms psi_conj

include hρ in
theorem inr_mem_range (g : SteinbergGroup I B) :
    (SemidirectProduct.inr g : SD I ι ρ) ∈ (psi ι ρ hρ).range := by
  refine PresentedGroup.generated_by _ ((psi ι ρ hρ).range.comap SemidirectProduct.inr) ?_ g
  rintro ⟨i, j, hij, b⟩
  refine Subgroup.mem_comap.mpr (MonoidHom.mem_range.mpr ⟨x i j hij (ι b), ?_⟩)
  change psi ι ρ hρ (x i j hij (ι b)) = SemidirectProduct.inr (x i j hij b)
  rw [psi_x]
  unfold psiX
  have hz : X (stdPair i j (ι b - ι (ρ (ι b)))) (rmem_std hij (sub_mem_ker ι ρ hρ (ι b))) = 1 := by
    rw [X_congr (show stdPair i j (ι b - ι (ρ (ι b))) = (Pi.single i (1 : A), (0 : I → A)) by
      rw [hρ, sub_self]; simp [stdPair]) _ (rmem_std hij (sub_mem_ker ι ρ hρ (ι b))).zero]
    exact X_zero _ _
  rw [hz, map_one, one_mul, hρ]

#audit_axioms inr_mem_range

include hρ in
/-- `X_{eᵢ, uⱼ eⱼ}` is `ψ(xᵢⱼ(uⱼ))` when `uⱼ ∈ ker ρ` (and trivial when `j = i`, `uᵢ = 0`). -/
theorem inl_single_mem_range (i j : I) {c : A} (hc : c ∈ RingHom.ker ρ) (hji : j = i → c = 0)
    (h : RMem (RingHom.ker ρ) (Pi.single i (1 : A), Pi.single j c)) :
    (SemidirectProduct.inl (X _ h) : SD I ι ρ) ∈ (psi ι ρ hρ).range := by
  by_cases hij : i = j
  · have hc0 := hji hij.symm
    rw [X_congr (show (Pi.single i (1 : A), Pi.single j c) = (Pi.single i 1, (0 : I → A)) by
      rw [hc0, Pi.single_zero]) h h.zero, X_zero, map_one]
    exact one_mem _
  · refine MonoidHom.mem_range.mpr ⟨x i j hij c, ?_⟩
    rw [psi_x]
    unfold psiX
    have hρc : ρ c = 0 := RingHom.mem_ker.mp hc
    rw [X_congr (show stdPair i j (c - ι (ρ c)) = (Pi.single i (1 : A), Pi.single j c) by
      rw [hρc, map_zero, sub_zero]) _ h, hρc, x_zero, map_one, mul_one]

#audit_axioms inl_single_mem_range

include hρ in
theorem inl_mem_range (n : RelSt I A (RingHom.ker ρ)) :
    (SemidirectProduct.inl n : SD I ι ρ) ∈ (psi ι ρ hρ).range := by
  refine PresentedGroup.generated_by _ ((psi ι ρ hρ).range.comap SemidirectProduct.inl) ?_ n
  rintro ⟨p, hp⟩
  change SemidirectProduct.inl (X p hp) ∈ (psi ι ρ hρ).range
  have hp' := hp
  obtain ⟨⟨g, hg, i, hv⟩, hw, hwv⟩ := hp'
  obtain ⟨y, hy⟩ := projection_surjective (I := I) (R := A) ⟨g, hg⟩
  have hum : ∀ k, (p.2 ᵥ* (g : Matrix I I A)) k ∈ RingHom.ker ρ := vecMul_mem _ hw
  have hui : (p.2 ᵥ* (g : Matrix I I A)) i = 0 := by
    have h : (p.2 ᵥ* (g : Matrix I I A)) ⬝ᵥ Pi.single i 1 = (p.2 ᵥ* (g : Matrix I I A)) i * 1 := by
      rw [dotProduct_single]
    rw [mul_one, ← dotProduct_mulVec, ← hv, hwv] at h
    exact h.symm
  have hsingle : ∀ j, RMem (RingHom.ker ρ)
      (Pi.single i (1 : A), Pi.single j ((p.2 ᵥ* (g : Matrix I I A)) j)) := fun j =>
    ⟨isEColumn_single i, fun k => by
      by_cases hk : k = j
      · rw [hk, Pi.single_eq_same]
        exact hum j
      · rw [Pi.single_eq_of_ne hk]
        exact zero_mem _, by
      change Pi.single j _ ⬝ᵥ Pi.single i 1 = 0
      rw [single_dotProduct]
      by_cases hj : j = i
      · rw [hj, hui, zero_mul]
      · rw [Pi.single_eq_of_ne hj, mul_zero]⟩
  have main : ∀ s : Finset I, ∃ h : RMem (RingHom.ker ρ) (Pi.single i (1 : A),
      ∑ j ∈ s, Pi.single j ((p.2 ᵥ* (g : Matrix I I A)) j)),
      (SemidirectProduct.inl (X _ h) : SD I ι ρ) ∈ (psi ι ρ hρ).range := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : RMem (RingHom.ker ρ) (Pi.single i (1 : A), (0 : I → A)) := (hsingle i).zero
      have e : (Pi.single i (1 : A), ∑ j ∈ (∅ : Finset I),
          Pi.single j ((p.2 ᵥ* (g : Matrix I I A)) j)) = (Pi.single i 1, 0) := by simp
      refine ⟨e ▸ h0, ?_⟩
      rw [X_congr e _ h0, X_zero, map_one]
      exact one_mem _
    · intro j s hj ih
      obtain ⟨hs, hrs⟩ := ih
      have hsum := (hsingle j).add hs
      have e : (Pi.single i (1 : A), ∑ k ∈ insert j s,
          Pi.single k ((p.2 ᵥ* (g : Matrix I I A)) k)) = (Pi.single i 1,
          Pi.single j ((p.2 ᵥ* (g : Matrix I I A)) j) +
            ∑ k ∈ s, Pi.single k ((p.2 ᵥ* (g : Matrix I I A)) k)) := by
        rw [Finset.sum_insert hj]
      refine ⟨e ▸ hsum, ?_⟩
      rw [X_congr e _ hsum, ← X_add _ _ _ (hsingle j) hs hsum, map_mul]
      exact mul_mem (inl_single_mem_range ι ρ hρ i j (hum j)
        (fun hji => by rw [hji]; exact hui) (hsingle j)) hrs
  obtain ⟨hu, hru⟩ := main Finset.univ
  have hq : RMem (RingHom.ker ρ) (Pi.single i (1 : A), p.2 ᵥ* (g : Matrix I I A)) := by
    rw [← Finset.univ_sum_single (p.2 ᵥ* (g : Matrix I I A))]
    exact hu
  have hX : (SemidirectProduct.inl (X _ hq) : SD I ι ρ) ∈ (psi ι ρ hρ).range := by
    rw [X_congr (congrArg (Prod.mk _) (Finset.univ_sum_single _)).symm hq hu]
    exact hru
  have key : (SemidirectProduct.inl (X p hp) : SD I ι ρ) =
      psi ι ρ hρ y * SemidirectProduct.inl (X _ hq) * (psi ι ρ hρ y)⁻¹ := by
    rw [psi_conj]
    refine congrArg _ (X_congr ?_ _ _)
    rw [hy]
    refine Prod.ext ?_ ?_
    · exact hv
    · change p.2 = (p.2 ᵥ* (g : Matrix I I A)) ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)
      rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
  rw [key]
  exact mul_mem (mul_mem ((psi ι ρ hρ).mem_range_self y) hX)
    (inv_mem ((psi ι ρ hρ).mem_range_self y))

#audit_axioms inl_mem_range

include hρ in
/-- **`ψ` is surjective** (Tulenbaev, Prop 1.6). -/
theorem psi_surjective : Function.Surjective (psi (I := I) ι ρ hρ) := by
  intro z
  have h : z ∈ (psi ι ρ hρ).range := by
    rw [← SemidirectProduct.inl_left_mul_inr_right z]
    exact mul_mem (inl_mem_range ι ρ hρ _) (inr_mem_range ι ρ hρ _)
  exact MonoidHom.mem_range.mp h

#audit_axioms psi_surjective

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation

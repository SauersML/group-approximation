import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresPsi
import GroupApproximation.Meta.AxiomGuard

/-!
# The adjacent relation for `ψ`, and `ψ` itself (k2-poly, piece F.3, part 2)

With `a' = a - ιρa`, `c' = c - ιρc`, `α = ιρa`, `γ = ιρc`, the four commutators of the factors of
`ψ(xᵢⱼ(a)) = X_{eᵢ,a'eⱼ} xᵢⱼ(ρa)` and `ψ(xⱼₖ(c)) = X_{eⱼ,c'eₖ} xⱼₖ(ρc)` are root elements in the
`ik` position:
* `⁅xᵢⱼ(ρa), X_{eⱼ,c'eₖ}⁆ = X_{eᵢ, αc' eₖ}`, by (1.3) (`comm_inr_inl`);
* `⁅X_{eᵢ,a'eⱼ}, X_{eⱼ,c'eₖ}⁆ = X_{eᵢ, a'c' eₖ}` (`X_std_adjacent`);
* `⁅xᵢⱼ(ρa), xⱼₖ(ρc)⁆ = xᵢₖ(ρa ρc)`;
* `⁅X_{eᵢ,a'eⱼ}, xⱼₖ(ρc)⁆ = X_{eᵢ, a'γ eₖ}` (`comm_inl_inr`).
Then `comm_mul_mul` gives `psiX_adjacent`, and `psi : St(A) →* St(A, ker ρ) ⋊ St(B)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair stdPair)
open scoped commutatorElement

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  (ι : B →+* A) (ρ : A →+* B)

theorem rmem_conjPair_std {𝔄 : Ideal A} {i j : I} (hij : i ≠ j) (t : A)
    {q : (I → A) × (I → A)} (hq : RMem 𝔄 q) : RMem 𝔄 (conjPair (stdPair i j t) q) :=
  smulPair_elementaryUnit hij t q ▸ smulPair_mem (elementaryUnit_mem i j hij t) hq

#audit_axioms rmem_conjPair_std

/-- `⁅xᵢⱼ(s), X_{eⱼ, c eₖ}⁆ = X_{eᵢ, (ιs) c eₖ}`. -/
theorem comm_inr_inl {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s : B) {c : A}
    (hc : c ∈ RingHom.ker ρ) :
    ⁅(SemidirectProduct.inr (x i j hij s) : SD I ι ρ),
      (SemidirectProduct.inl (X (stdPair j k c) (rmem_std hjk hc)) : SD I ι ρ)⁆ =
      SemidirectProduct.inl (X (stdPair i k (ι s * c))
        (rmem_std hik ((RingHom.ker ρ).mul_mem_left (ι s) hc))) := by
  have hP : conjPair (stdPair i j (ι s)) (stdPair j k c) =
      (ι s • Pi.single i 1 + Pi.single j 1, Pi.single k c) := by
    refine Prod.ext ?_ ?_
    · change Pi.single j 1 + (Pi.single j (ι s) ⬝ᵥ Pi.single j 1) • Pi.single i 1 = _
      rw [single_dotProduct, Pi.single_eq_same, mul_one, add_comm]
    · change Pi.single k c - (Pi.single k c ⬝ᵥ Pi.single i 1) • Pi.single j (ι s) = _
      rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero, zero_smul, sub_zero]
  have hmem := rmem_conjPair_std (𝔄 := RingHom.ker ρ) hij (ι s) (rmem_std hjk hc)
  have h₁ : RMem (RingHom.ker ρ) (ι s • Pi.single i 1 + Pi.single j (1 : A), Pi.single k c) :=
    hP ▸ hmem
  have h₂ : RMem (RingHom.ker ρ) (Pi.single i (1 : A), ι s • Pi.single k c) :=
    (rmem_std hik hc).smul (ι s)
  have hf := X_frame (Pi.single i 1) (Pi.single j 1) (Pi.single k c) (Pi.single j 1) (ι s)
    (by rw [single_dotProduct, Pi.single_eq_of_ne hij.symm, mul_zero])
    (by rw [single_dotProduct, Pi.single_eq_same, mul_one])
    (by rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero]) h₁ h₂ (rmem_std hjk hc)
  have hN : stAct ι ρ (x i j hij s) (X (stdPair j k c) (rmem_std hjk hc)) *
      (X (stdPair j k c) (rmem_std hjk hc))⁻¹ =
      X (stdPair i k (ι s * c)) (rmem_std hik ((RingHom.ker ρ).mul_mem_left (ι s) hc)) := by
    rw [stAct_x ι ρ hij s _ _ hmem, X_congr hP _ h₁, hf, mul_inv_cancel_right]
    exact X_congr (by
      show ((Pi.single i 1, ι s • Pi.single k c) : (I → A) × (I → A)) =
        (Pi.single i 1, Pi.single k (ι s * c))
      rw [← smul_eq_mul, Pi.single_smul']) _ _
  rw [commutatorElement_def, inr_mul_inl, mul_inv_cancel_right, ← map_inv, ← map_mul, hN]

#audit_axioms comm_inr_inl

/-- `⁅X_{eᵢ, a eⱼ}, xⱼₖ(s)⁆ = X_{eᵢ, a (ιs) eₖ}`. -/
theorem comm_inl_inr {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s : B) {a : A}
    (ha : a ∈ RingHom.ker ρ) :
    ⁅(SemidirectProduct.inl (X (stdPair i j a) (rmem_std hij ha)) : SD I ι ρ),
      (SemidirectProduct.inr (x j k hjk s) : SD I ι ρ)⁆ =
      SemidirectProduct.inl (X (stdPair i k (a * ι s))
        (rmem_std hik ((RingHom.ker ρ).mul_mem_right (ι s) ha))) := by
  have ht : -(a * ι s) ∈ RingHom.ker ρ := neg_mem ((RingHom.ker ρ).mul_mem_right (ι s) ha)
  have hP : conjPair (stdPair j k (ι s)) (stdPair i j a) =
      (Pi.single i 1, Pi.single j a + Pi.single k (-(a * ι s))) := by
    refine Prod.ext ?_ ?_
    · change Pi.single i 1 + (Pi.single k (ι s) ⬝ᵥ Pi.single i 1) • Pi.single j 1 = _
      rw [single_dotProduct, Pi.single_eq_of_ne hik.symm, mul_zero, zero_smul, add_zero]
    · change Pi.single j a - (Pi.single j a ⬝ᵥ Pi.single j 1) • Pi.single k (ι s) = _
      rw [single_dotProduct, Pi.single_eq_same, mul_one, ← smul_eq_mul, Pi.single_neg,
        Pi.single_smul', sub_eq_add_neg]
  have hmem := rmem_conjPair_std (𝔄 := RingHom.ker ρ) hjk (ι s) (rmem_std hij ha)
  have hsum : RMem (RingHom.ker ρ)
      (Pi.single i (1 : A), Pi.single j a + Pi.single k (-(a * ι s))) := hP ▸ hmem
  have hadd := X_add (Pi.single i 1) (Pi.single j a) (Pi.single k (-(a * ι s)))
    (rmem_std hij ha) (rmem_std hik ht) hsum
  have hcomm := commute_of_conjPair (rmem_std hij ha) (rmem_std hik ht)
    (conjPair_std_std hij.symm hik.symm a (-(a * ι s)))
  have hneg : (X (stdPair i k (-(a * ι s))) (rmem_std hik ht))⁻¹ =
      X (stdPair i k (a * ι s)) (rmem_std hik ((RingHom.ker ρ).mul_mem_right (ι s) ha)) := by
    rw [← X_neg (Pi.single i 1) (Pi.single k (-(a * ι s))) (rmem_std hik ht)
      (rmem_std hik ht).neg]
    exact X_congr (by
      show ((Pi.single i 1, -Pi.single k (-(a * ι s))) : (I → A) × (I → A)) =
        (Pi.single i 1, Pi.single k (a * ι s))
      rw [← Pi.single_neg, neg_neg]) _ _
  have hN : X (stdPair i j a) (rmem_std hij ha) *
      stAct ι ρ (x j k hjk s) (X (stdPair i j a) (rmem_std hij ha))⁻¹ =
      X (stdPair i k (a * ι s)) (rmem_std hik ((RingHom.ker ρ).mul_mem_right (ι s) ha)) := by
    rw [map_inv, stAct_x ι ρ hjk s _ _ hmem, X_congr hP _ hsum, ← hadd, mul_inv_rev,
      ← mul_assoc, hcomm.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one, hneg]
  calc ⁅(SemidirectProduct.inl (X (stdPair i j a) (rmem_std hij ha)) : SD I ι ρ),
        (SemidirectProduct.inr (x j k hjk s) : SD I ι ρ)⁆ =
      SemidirectProduct.inl (X (stdPair i j a) (rmem_std hij ha)) *
        (SemidirectProduct.inr (x j k hjk s) *
          SemidirectProduct.inl (X (stdPair i j a) (rmem_std hij ha))⁻¹) *
        (SemidirectProduct.inr (x j k hjk s))⁻¹ := by
        rw [commutatorElement_def, map_inv]
        group
    _ = _ := by
      rw [inr_mul_inl, ← mul_assoc, mul_inv_cancel_right, ← map_mul, hN]

#audit_axioms comm_inl_inr

variable (hρ : ∀ b, ρ (ι b) = b)

theorem psiX_adjacent {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a c : A) :
    ⁅psiX ι ρ hρ i j hij a, psiX ι ρ hρ j k hjk c⁆ = psiX ι ρ hρ i k hik (a * c) := by
  have ha := sub_mem_ker ι ρ hρ a
  have hc := sub_mem_ker ι ρ hρ c
  have ht₁ := (RingHom.ker ρ).mul_mem_left (ι (ρ a)) hc
  have ht₃ := (RingHom.ker ρ).mul_mem_right (ι (ρ c)) ha
  have c1 := comm_inr_inl ι ρ hij hjk hik (ρ a) hc
  have c2 : ⁅(SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a))) (rmem_std hij ha)) :
      SD I ι ρ),
      (SemidirectProduct.inl (X (stdPair j k (c - ι (ρ c))) (rmem_std hjk hc)) : SD I ι ρ)⁆ =
      SemidirectProduct.inl (X (stdPair i k ((a - ι (ρ a)) * (c - ι (ρ c))))
        (rmem_std hik ((RingHom.ker ρ).mul_mem_left _ hc))) := by
    rw [← map_commutatorElement, X_std_adjacent hij hjk hik ha hc]
  have c3 : ⁅(SemidirectProduct.inr (x i j hij (ρ a)) : SD I ι ρ),
      (SemidirectProduct.inr (x j k hjk (ρ c)) : SD I ι ρ)⁆ =
      SemidirectProduct.inr (x i k hik (ρ a * ρ c)) := by
    rw [← map_commutatorElement, x_commutator]
  have c4 := comm_inl_inr ι ρ hij hjk hik (ρ c) ha
  have h1 : Commute (SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a))) (rmem_std hij ha)) :
      SD I ι ρ) (SemidirectProduct.inl (X (stdPair i k (ι (ρ a) * (c - ι (ρ c))))
        (rmem_std hik ht₁))) :=
    (commute_of_conjPair (rmem_std hij ha) (rmem_std hik ht₁)
      (conjPair_std_std hij.symm hik.symm _ _)).map SemidirectProduct.inl
  have h2 := (commute_inr_inl ι ρ hik hik.symm hij.symm (ρ a * ρ c) (rmem_std hij ha)).symm
  have h3 := (commute_inr_inl ι ρ hik hjk.symm hik.symm (ρ a * ρ c) (rmem_std hjk hc)).symm
  have h4 : Commute (SemidirectProduct.inl (X (stdPair j k (c - ι (ρ c))) (rmem_std hjk hc)) :
      SD I ι ρ) (SemidirectProduct.inl (X (stdPair i k ((a - ι (ρ a)) * ι (ρ c)))
        (rmem_std hik ht₃))) :=
    (commute_of_conjPair (rmem_std hjk hc) (rmem_std hik ht₃)
      (conjPair_std_std hik.symm hjk.symm _ _)).map SemidirectProduct.inl
  have key := comm_mul_mul
    (SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a))) (rmem_std hij ha)) : SD I ι ρ)
    (SemidirectProduct.inr (x i j hij (ρ a)))
    (SemidirectProduct.inl (X (stdPair j k (c - ι (ρ c))) (rmem_std hjk hc)))
    (SemidirectProduct.inr (x j k hjk (ρ c)))
    (by rw [c1]; exact h1) (by rw [c3]; exact h2) (by rw [c3]; exact h3) (by rw [c4]; exact h4)
  unfold psiX
  rw [key, c1, c2, c3, c4, (commute_inr_inl ι ρ hik hik.symm hik.symm (ρ a * ρ c)
    (rmem_std hik ht₃)).eq, ← mul_assoc, ← map_mul, ← map_mul,
    X_std_add' hik ht₁ ((RingHom.ker ρ).mul_mem_left _ hc),
    X_std_add' hik (add_mem ht₁ ((RingHom.ker ρ).mul_mem_left _ hc)) ht₃]
  refine congrArg₂ (· * ·) (congrArg _ (X_congr ?_ _ _)) (congrArg _ ?_)
  · rw [show ι (ρ a) * (c - ι (ρ c)) + (a - ι (ρ a)) * (c - ι (ρ c)) +
      (a - ι (ρ a)) * ι (ρ c) = a * c - ι (ρ (a * c)) by rw [map_mul, map_mul]; ring]
  · rw [map_mul]

#audit_axioms psiX_adjacent

/-- **The splitting map** `ψ : St(A) →* St(A, ker ρ) ⋊ St(B)` (Tulenbaev, Prop 1.6). -/
noncomputable def psi : SteinbergGroup I A →* SD I ι ρ :=
  PresentedGroup.toGroup
    (f := fun g : SteinbergGenerator I A =>
      psiX ι ρ hρ g.row g.column g.row_ne_column g.coefficient)
    (by
      intro w hw
      change SteinbergGroup.IsRelation w at hw
      cases hw with
      | add i j hij a b =>
          simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
          change psiX ι ρ hρ i j hij a * psiX ι ρ hρ i j hij b *
            (psiX ι ρ hρ i j hij (a + b))⁻¹ = 1
          rw [psiX_add, mul_inv_cancel]
      | commute i j k l hij hkl hjk hli a b =>
          simp only [map_commutatorElement, FreeGroup.lift_apply_of]
          exact (psiX_commute ι ρ hρ hij hkl hjk hli a b).commutator_eq
      | adjacent i j k hij hjk hik a b =>
          simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
          change ⁅psiX ι ρ hρ i j hij a, psiX ι ρ hρ j k hjk b⁆ *
            (psiX ι ρ hρ i k hik (a * b))⁻¹ = 1
          rw [psiX_adjacent ι ρ hρ hij hjk hik, mul_inv_cancel])

theorem psi_x (i j : I) (hij : i ≠ j) (a : A) :
    psi ι ρ hρ (x i j hij a) = psiX ι ρ hρ i j hij a :=
  PresentedGroup.toGroup.of _

#audit_axioms psi_x

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation

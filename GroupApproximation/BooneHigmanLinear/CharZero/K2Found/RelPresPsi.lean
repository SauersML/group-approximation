import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresAct
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.GroupTheory.SemidirectProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# The splitting map `ψ : St(A) → St(A, 𝔄) ⋊ St(B)` (k2-poly, piece F.3, part 1)

Tulenbaev, Prop 1.6. Let `ι : B → A` and `ρ : A → B` be ring maps with `ρ ∘ ι = id`, and let
`𝔄 = ker ρ`. `St(B)` acts on `St(A, 𝔄)` through `E(B) → E(A)` (`stAct`). The map

  `ψ (xᵢⱼ(a)) = X_{eᵢ, (a - ιρa) eⱼᵀ} · xᵢⱼ(ρ a)`

respects the Steinberg relations (`psi`). The adjacent relation uses `comm_mul_mul`: in any group,
`⁅x y, z w⁆ = ⁅y, z⁆ ⁅x, z⁆ ⁅y, w⁆ ⁅x, w⁆` once the relevant commutators commute with `x` and `z`.
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

/-- `⁅x y, z w⁆ = ⁅y, z⁆ ⁅x, z⁆ (⁅y, w⁆ ⁅x, w⁆)` when the commutators commute with `x`, `z`. -/
theorem comm_mul_mul {G : Type*} [Group G] (x y z w : G) (h1 : Commute x ⁅y, z⁆)
    (h2 : Commute x ⁅y, w⁆) (h3 : Commute z ⁅y, w⁆) (h4 : Commute z ⁅x, w⁆) :
    ⁅x * y, z * w⁆ = ⁅y, z⁆ * ⁅x, z⁆ * (⁅y, w⁆ * ⁅x, w⁆) := by
  have e1 : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅x * y, z * w⁆ = ⁅x * y, z⁆ * (z * ⁅x * y, w⁆ * z⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e3 : ⁅x * y, w⁆ = x * ⁅y, w⁆ * x⁻¹ * ⁅x, w⁆ := by
    simp only [commutatorElement_def]
    group
  have k1 : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by rw [h1.eq, mul_inv_cancel_right]
  have k2 : x * ⁅y, w⁆ * x⁻¹ = ⁅y, w⁆ := by rw [h2.eq, mul_inv_cancel_right]
  have k3 : z * (⁅y, w⁆ * ⁅x, w⁆) * z⁻¹ = ⁅y, w⁆ * ⁅x, w⁆ := by
    rw [(h3.mul_right h4).eq, mul_inv_cancel_right]
  rw [e2, e1, e3, k1, k2, k3]

#audit_axioms comm_mul_mul

section Psi

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  (ι : B →+* A) (ρ : A →+* B)

/-- `St(B)` acting on `St(A, ker ρ)` through `E(B) → E(A)`. -/
noncomputable def stAct : SteinbergGroup I B →* MulAut (RelSt I A (RingHom.ker ρ)) :=
  (actAut I A (RingHom.ker ρ)).comp ((elementaryGroupMap ι).comp projection)

variable (I) in
/-- `St(A, ker ρ) ⋊ St(B)`. -/
abbrev SD : Type _ :=
  RelSt I A (RingHom.ker ρ) ⋊[stAct ι ρ] SteinbergGroup I B

theorem stAct_x {i j : I} (hij : i ≠ j) (t : B) (q : (I → A) × (I → A))
    (hq : RMem (RingHom.ker ρ) q) (hc : RMem (RingHom.ker ρ) (conjPair (stdPair i j (ι t)) q)) :
    stAct ι ρ (x i j hij t) (X q hq) = X (conjPair (stdPair i j (ι t)) q) hc := by
  change actAut I A _ (elementaryGroupMap ι (projection (x i j hij t))) (X q hq) = _
  rw [projection_x, elementaryGroupMap_root, actAut_X]
  exact X_congr (smulPair_elementaryUnit hij (ι t) q) _ _

#audit_axioms stAct_x

theorem inr_mul_inl (g : SteinbergGroup I B) (n : RelSt I A (RingHom.ker ρ)) :
    (SemidirectProduct.inr g : SD I ι ρ) * SemidirectProduct.inl n =
      SemidirectProduct.inl (stAct ι ρ g n) * SemidirectProduct.inr g := by
  rw [SemidirectProduct.inl_aut, map_inv, inv_mul_cancel_right]

#audit_axioms inr_mul_inl

/-- `xᵢⱼ(t)` commutes with `X_{eₖ, c eₗᵀ}` when `j ≠ k` and `l ≠ i`. -/
theorem commute_inr_inl {i j k l : I} (hij : i ≠ j) (hjk : j ≠ k) (hli : l ≠ i) (t : B) {c : A}
    (hc : RMem (RingHom.ker ρ) (stdPair k l c)) :
    Commute (SemidirectProduct.inr (x i j hij t) : SD I ι ρ) (SemidirectProduct.inl (X _ hc)) := by
  change _ * _ = _ * _
  rw [inr_mul_inl, stAct_x ι ρ hij t _ hc ((conjPair_std_std hjk hli (ι t) c).symm ▸ hc),
    X_congr (conjPair_std_std hjk hli (ι t) c) _ hc]

#audit_axioms commute_inr_inl

theorem X_std_add' {i j : I} (hij : i ≠ j) {𝔄 : Ideal A} {a b : A} (ha : a ∈ 𝔄) (hb : b ∈ 𝔄) :
    X (stdPair i j a) (rmem_std hij ha) * X (stdPair i j b) (rmem_std hij hb) =
      X (stdPair i j (a + b)) (rmem_std hij (add_mem ha hb)) := by
  rw [X_add (Pi.single i 1) (Pi.single j a) (Pi.single j b) (rmem_std hij ha) (rmem_std hij hb)
    ((rmem_std hij ha).add (rmem_std hij hb))]
  exact X_congr (by simp [stdPair, Pi.single_add]) _ _

#audit_axioms X_std_add'

variable (hρ : ∀ b, ρ (ι b) = b)

include hρ in
theorem sub_mem_ker (a : A) : a - ι (ρ a) ∈ RingHom.ker ρ := by
  rw [RingHom.mem_ker, map_sub, hρ, sub_self]

#audit_axioms sub_mem_ker

/-- `ψ(xᵢⱼ(a)) = X_{eᵢ, (a - ιρa) eⱼᵀ} · xᵢⱼ(ρ a)`. -/
noncomputable def psiX (i j : I) (hij : i ≠ j) (a : A) : SD I ι ρ :=
  SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a))) (rmem_std hij (sub_mem_ker ι ρ hρ a))) *
    SemidirectProduct.inr (x i j hij (ρ a))

theorem psiX_add (i j : I) (hij : i ≠ j) (a b : A) :
    psiX ι ρ hρ i j hij a * psiX ι ρ hρ i j hij b = psiX ι ρ hρ i j hij (a + b) := by
  have hc := (commute_inr_inl ι ρ hij hij.symm hij.symm (ρ a)
    (rmem_std hij (sub_mem_ker ι ρ hρ b))).eq
  have hN : X (stdPair i j (a - ι (ρ a))) (rmem_std hij (sub_mem_ker ι ρ hρ a)) *
      X (stdPair i j (b - ι (ρ b))) (rmem_std hij (sub_mem_ker ι ρ hρ b)) =
      X (stdPair i j (a + b - ι (ρ (a + b)))) (rmem_std hij (sub_mem_ker ι ρ hρ (a + b))) := by
    rw [X_std_add' hij (sub_mem_ker ι ρ hρ a) (sub_mem_ker ι ρ hρ b)]
    exact X_congr (by
      rw [show a - ι (ρ a) + (b - ι (ρ b)) = a + b - ι (ρ (a + b)) by rw [map_add, map_add]; ring])
      _ _
  unfold psiX
  calc _ = SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a))) (rmem_std hij
        (sub_mem_ker ι ρ hρ a))) * (SemidirectProduct.inr (x i j hij (ρ a)) *
        SemidirectProduct.inl (X (stdPair i j (b - ι (ρ b))) (rmem_std hij
          (sub_mem_ker ι ρ hρ b)))) * SemidirectProduct.inr (x i j hij (ρ b)) := by group
    _ = _ := by
      rw [hc, ← mul_assoc, ← map_mul, hN, mul_assoc, ← map_mul, x_mul, ← map_add]

#audit_axioms psiX_add

theorem psiX_commute {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : A) : Commute (psiX ι ρ hρ i j hij a) (psiX ι ρ hρ k l hkl b) := by
  have h11 : Commute (SemidirectProduct.inl (X (stdPair i j (a - ι (ρ a)))
      (rmem_std hij (sub_mem_ker ι ρ hρ a))) : SD I ι ρ)
      (SemidirectProduct.inl (X (stdPair k l (b - ι (ρ b)))
        (rmem_std hkl (sub_mem_ker ι ρ hρ b)))) :=
    (commute_of_conjPair (rmem_std hij (sub_mem_ker ι ρ hρ a)) (rmem_std hkl (sub_mem_ker ι ρ hρ b))
      (conjPair_std_std hjk hli _ _)).map SemidirectProduct.inl
  have h12 := (commute_inr_inl ι ρ hkl hli hjk (ρ b)
    (rmem_std hij (sub_mem_ker ι ρ hρ a))).symm
  have h21 := commute_inr_inl ι ρ hij hjk hli (ρ a) (rmem_std hkl (sub_mem_ker ι ρ hρ b))
  have h22 : Commute (SemidirectProduct.inr (x i j hij (ρ a)) : SD I ι ρ)
      (SemidirectProduct.inr (x k l hkl (ρ b))) :=
    (x_commute_of_ne i j k l hij hkl hjk hli _ _).map SemidirectProduct.inr
  exact (h11.mul_right h12).mul_left (h21.mul_right h22)

#audit_axioms psiX_commute

end Psi

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation

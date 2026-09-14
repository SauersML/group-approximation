import GroupApproximation.Analysis.PauliHyperfiniteFactor

/-!
# Pauli operators in the hyperfinite II₁ factor

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  The matrix units of the finite Pauli stages of `𝓡`
(`Analysis/PauliMatrixUnits.lean`) are built from the operators proved here.

For a general sign cocycle:
* `twistedLeftOperator_one`: `λ₁ = 1`.
* `star_twistedLeftOperator_eq`: `λ_g⋆ = s(σ(g,g⁻¹)) λ_{g⁻¹}`.
* `coefficient_twistedLeftOperator`: `τ(λ_g) = [g = 1]` for the identity coefficient.

For the Pauli group, `pauliOp x z := λ_{(x,z)}`:
* `pauliOp_mul`: `pauliOp x z * pauliOp x' z' = s(z · x') pauliOp (x+x') (z+z')`.
* `star_pauliOp`: `(pauliOp x z)⋆ = s(z · x) pauliOp x z`.
* `pauliOp_zero`, `pauliOp_mem`, `coefficient_pauliOp`.
-/

namespace GroupApproximation
namespace TwistedGroupVonNeumann

open ReducedGroupCStarTrace

noncomputable section

universe u

variable {Γ : Type u} [Group Γ] (σ : Γ → Γ → ZMod 2)

local instance : DecidableEq Γ := Classical.decEq Γ

/-- `λ₁ = 1`. -/
theorem twistedLeftOperator_one (hσ : IsSignCocycle σ) : twistedLeftOperator σ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  change zsign (σ 1 (1⁻¹ * h)) * f (1⁻¹ * h) = f h
  rw [inv_one, one_mul, hσ.map_one_left, zsign_zero, one_mul]

/-- **The adjoint of a twisted left unitary**: `λ_g⋆ = s(σ(g,g⁻¹)) λ_{g⁻¹}`. -/
theorem star_twistedLeftOperator_eq (hσ : IsSignCocycle σ) (g : Γ) :
    star (twistedLeftOperator σ g) = zsign (σ g g⁻¹) • twistedLeftOperator σ g⁻¹ := by
  have hright : twistedLeftOperator σ g * (zsign (σ g g⁻¹) • twistedLeftOperator σ g⁻¹) = 1 := by
    rw [mul_smul_comm, twistedLeftOperator_mul σ hσ, mul_inv_cancel, twistedLeftOperator_one σ hσ,
      smul_smul, zsign_mul_self, one_smul]
  calc star (twistedLeftOperator σ g)
      = star (twistedLeftOperator σ g) *
          (twistedLeftOperator σ g * (zsign (σ g g⁻¹) • twistedLeftOperator σ g⁻¹)) := by
        rw [hright, mul_one]
    _ = (star (twistedLeftOperator σ g) * twistedLeftOperator σ g) *
          (zsign (σ g g⁻¹) • twistedLeftOperator σ g⁻¹) := by
        rw [mul_assoc]
    _ = zsign (σ g g⁻¹) • twistedLeftOperator σ g⁻¹ := by
        rw [star_mul_twistedLeftOperator, one_mul]

/-- **The trace of a twisted left unitary**: `τ(λ_g) = [g = 1]`. -/
theorem coefficient_twistedLeftOperator (hσ : IsSignCocycle σ) (g : Γ) :
    (twistedLeftOperator σ g (deltaOne Γ)) 1 = if g = 1 then 1 else 0 := by
  rw [twistedLeftOperator_deltaOne σ hσ, lp.single_apply, Pi.single_apply]
  by_cases hg : g = 1
  · subst hg
    simp
  · rw [if_neg (Ne.symm hg), if_neg hg]

end

end TwistedGroupVonNeumann

namespace Hyperfinite

open TwistedGroupVonNeumann ReducedGroupCStarTrace

noncomputable section

local instance : DecidableEq PauliGroup := Classical.decEq PauliGroup

theorem zmod_two_neg (c : ZMod 2) : -c = c := by
  revert c
  decide

theorem pauliCoord_neg (v : PauliCoord) : -v = v := by
  ext i
  rw [Finsupp.neg_apply, zmod_two_neg]

/-- **The Pauli operator** `λ_{(x,z)}`, the Pauli word `Π_i X_i^{x_i} Z_i^{z_i}`. -/
def pauliOp (x z : PauliCoord) : GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup :=
  twistedLeftOperator pauliCocycle (Multiplicative.ofAdd (x, z))

theorem pauliOp_mem (x z : PauliCoord) : pauliOp x z ∈ hyperfiniteFactor :=
  twistedLeftOperator_mem pauliCocycle _

theorem pauliOp_zero : pauliOp 0 0 = 1 := by
  rw [pauliOp, Prod.mk_zero_zero, ofAdd_zero, twistedLeftOperator_one pauliCocycle
    pauliCocycle_isSignCocycle]

/-- **The Pauli product rule** `pauliOp x z * pauliOp x' z' = s(z·x') pauliOp (x+x') (z+z')`. -/
theorem pauliOp_mul (x z x' z' : PauliCoord) :
    pauliOp x z * pauliOp x' z' = zsign (dot z x') • pauliOp (x + x') (z + z') := by
  rw [pauliOp, pauliOp, pauliOp, twistedLeftOperator_mul pauliCocycle pauliCocycle_isSignCocycle,
    ← ofAdd_add, Prod.mk_add_mk]
  rfl

/-- **The adjoint of a Pauli operator** `(pauliOp x z)⋆ = s(z·x) pauliOp x z`. -/
theorem star_pauliOp (x z : PauliCoord) :
    star (pauliOp x z) = zsign (dot z x) • pauliOp x z := by
  rw [pauliOp, star_twistedLeftOperator_eq pauliCocycle pauliCocycle_isSignCocycle]
  have hinv : (Multiplicative.ofAdd (x, z) : PauliGroup)⁻¹ = Multiplicative.ofAdd (x, z) := by
    rw [← ofAdd_neg, Prod.neg_mk, pauliCoord_neg, pauliCoord_neg]
  rw [hinv]
  rfl

/-- **The trace of a Pauli operator**: `τ(pauliOp x z) = [x = 0 ∧ z = 0]`. -/
theorem coefficient_pauliOp (x z : PauliCoord) :
    (pauliOp x z (deltaOne PauliGroup)) 1 = if x = 0 ∧ z = 0 then 1 else 0 := by
  rw [pauliOp, coefficient_twistedLeftOperator pauliCocycle pauliCocycle_isSignCocycle]
  have hiff : (Multiplicative.ofAdd (x, z) : PauliGroup) = 1 ↔ x = 0 ∧ z = 0 := by
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, Prod.mk_eq_zero]
  by_cases h : x = 0 ∧ z = 0
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' ↦ h (hiff.mp h')), if_neg h]

end

#audit_axioms TwistedGroupVonNeumann.star_twistedLeftOperator_eq
#audit_axioms pauliOp_mul
#audit_axioms star_pauliOp
#audit_axioms coefficient_pauliOp

end Hyperfinite
end GroupApproximation

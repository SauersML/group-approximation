import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarInjConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative elementary subgroup `H(J)` of a Steinberg group: easy conjugations

Lane `bh-met-92f`.  For a commutative ring `R` and an ideal `J`, put
`z_ij(a, r) = x_ji(r) · x_ij(a) · x_ji(r)⁻¹` (`a ∈ J`, `r ∈ R` arbitrary) and let
`H(J) = ⟨z_ij(a, r)⟩ ⊆ St(ι, R)` (`k2KarNorm_H`).  This module proves, from the Steinberg
relations only, that conjugation by a root `x_kl(s)` keeps each `z_ij(a, r)` inside `H(J)` in
every configuration except `(k, l) = (i, j)`.  That case uses a third index and is in
`ElemFPK2KarNormHard`.  Matrix sanity checks (random `ℤ/7`, `n = 4`; `|H| = 256` for `ℤ/4`,
`J = (2)`, `n = 3`) are in the lane scratch directory.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarNormGroup

variable {G : Type*} [Group G]

theorem k2KarNorm_conj_mul (g a b : G) : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_mul

theorem k2KarNorm_conj_inv (g a : G) : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_inv

theorem k2KarNorm_conj_conj (g h a : G) : g * h * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_conj

theorem k2KarNorm_conj_z3 (g a b : G) :
    g * (a * b * a⁻¹) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z3

theorem k2KarNorm_conj_of_commute {g a : G} (hc : Commute g a) : g * a * g⁻¹ = a := by
  rw [hc.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_of_commute

theorem k2KarNorm_conj_commutator (g a b : G) : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_commutator

end KarNormGroup

section KarNormDefs

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- `z_ij(a, r) = x_ji(r) · x_ij(a) · x_ji(r)⁻¹`. -/
def k2KarNorm_z (i j : ι) (hij : i ≠ j) (a r : R) : SteinbergGroup ι R :=
  x j i hij.symm r * x i j hij a * (x j i hij.symm r)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_z

/-- The generators `z_ij(a, r)`, `a ∈ J`, `r ∈ R`. -/
def k2KarNorm_gens (ι : Type*) [Fintype ι] [DecidableEq ι] (J : Ideal R) :
    Set (SteinbergGroup ι R) :=
  {g | ∃ i j : ι, ∃ hij : i ≠ j, ∃ a ∈ J, ∃ r : R, k2KarNorm_z i j hij a r = g}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_gens

/-- `H(J) = ⟨z_ij(a, r) : a ∈ J, r ∈ R⟩`. -/
def k2KarNorm_H (ι : Type*) [Fintype ι] [DecidableEq ι] (J : Ideal R) :
    Subgroup (SteinbergGroup ι R) :=
  Subgroup.closure (k2KarNorm_gens ι J)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_H

variable {J : Ideal R}

theorem k2KarNorm_z_mem (i j : ι) (hij : i ≠ j) {a : R} (ha : a ∈ J) (r : R) :
    k2KarNorm_z i j hij a r ∈ k2KarNorm_H ι J :=
  Subgroup.subset_closure ⟨i, j, hij, a, ha, r, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_z_mem

theorem k2KarNorm_x_mem (i j : ι) (hij : i ≠ j) {a : R} (ha : a ∈ J) :
    x i j hij a ∈ k2KarNorm_H ι J := by
  have h := k2KarNorm_z_mem i j hij ha 0
  rwa [k2KarNorm_z, x_zero, inv_one, one_mul, mul_one] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_x_mem

/-- Root `x_jl` against `x_ij`: the conjugate is `x_il(-(a s)) · x_ij(a)`. -/
theorem k2KarNorm_C1 (i j l : ι) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a s : R) :
    x j l hjl s * x i j hij a * (x j l hjl s)⁻¹ = x i l hil (-(a * s)) * x i j hij a := by
  rw [x_neg, ← x_commutator i j l hij hjl hil a s, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_C1

/-- Root `x_ki` against `x_ij`: the conjugate is `x_kj(s a) · x_ij(a)`. -/
theorem k2KarNorm_C2 (i j k : ι) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a s : R) :
    x k i hki s * x i j hij a * (x k i hki s)⁻¹ = x k j hkj (s * a) * x i j hij a := by
  rw [← x_commutator k i j hki hij hkj s a, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_C2

/-- Every conjugate of `x_pq(a)`, `a ∈ J`, by a root `x_kl(s)` lies in `H(J)`. -/
theorem k2KarNorm_conj_x (k l : ι) (hkl : k ≠ l) (s : R) (i j : ι) (hij : i ≠ j) {a : R}
    (ha : a ∈ J) : x k l hkl s * x i j hij a * (x k l hkl s)⁻¹ ∈ k2KarNorm_H ι J := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hli : l = i
    · subst hli
      exact k2KarNorm_z_mem _ _ hij ha s
    · rw [k2KarNorm_C1 _ _ _ hij hkl (Ne.symm hli) a s]
      exact mul_mem (k2KarNorm_x_mem _ _ _ (neg_mem (Ideal.mul_mem_right s J ha)))
        (k2KarNorm_x_mem _ _ hij ha)
  · by_cases hli : l = i
    · subst hli
      rw [k2KarNorm_C2 _ _ _ hij hkl (Ne.symm hjk) a s]
      exact mul_mem (k2KarNorm_x_mem _ _ _ (Ideal.mul_mem_left J s ha))
        (k2KarNorm_x_mem _ _ hij ha)
    · rw [k2KarNorm_conj_of_commute (x_commute_of_ne k l i j hkl hij hli hjk s a)]
      exact k2KarNorm_x_mem i j hij ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_x

end KarNormDefs

end GroupApproximation.BooneHigman.Metabelian.ElemFP

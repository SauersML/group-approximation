import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative generation for a split ring retraction

Lane `bh-met-91g`, generation module.  Let `c : R₀ →+* R` and `e : R →+* R₀` with `e ∘ c = id`.

* `k2PullRel_genSet c e`: the conjugates `c(d) · x_ij(b) · c(d)⁻¹` with `d ∈ St(R₀)` and
  `e b = 0`.
* `k2PullRel_conj_mem`: the subgroup they generate is stable under conjugation by `c(St(R₀))`.
* `k2PullRel_mem_closure_of_ringMap_eq_one`: every `z ∈ St(R)` with `e(z) = 1` lies in that
  subgroup.  Proof: `z · c(e(z))⁻¹` lies in it for every `z`, because these elements form a
  subgroup (`k2PullRel_retractSub`) that contains every generator,
  `x_ij(b) · x_ij(c(e b))⁻¹ = x_ij(b - c(e b))`.

The pullback modules use this with `R = P`, `R₀ = A`, `e = fst` and `c = const`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullRelGen

variable {I R₀ R : Type*} [Fintype I] [DecidableEq I] [Ring R₀] [Ring R]

/-- The relative generators: `c(d) · x_ij(b) · c(d)⁻¹` with `e b = 0`. -/
def k2PullRel_genSet (c : R₀ →+* R) (e : R →+* R₀) : Set (SteinbergGroup I R) :=
  {g | ∃ (d : SteinbergGroup I R₀) (i j : I) (hij : i ≠ j) (b : R), e b = 0 ∧
    g = ringMap c d * x i j hij b * (ringMap c d)⁻¹}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_genSet

/-- The relative subgroup is stable under conjugation by `c(St(R₀))`. -/
theorem k2PullRel_conj_mem (c : R₀ →+* R) (e : R →+* R₀) (d : SteinbergGroup I R₀)
    {y : SteinbergGroup I R} (hy : y ∈ Subgroup.closure (k2PullRel_genSet c e)) :
    ringMap c d * y * (ringMap c d)⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e) := by
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨d', i, j, hij, b, hb, rfl⟩ := hg
    apply Subgroup.subset_closure
    refine ⟨d * d', i, j, hij, b, hb, ?_⟩
    simp only [map_mul]
    group
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul g h _ _ ihg ihh =>
    have hgh := mul_mem ihg ihh
    convert hgh using 1
    group
  | inv g _ ih =>
    have hg := inv_mem ih
    convert hg using 1
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_conj_mem

/-- The elements `z` with `z · c(e(z))⁻¹` in the relative subgroup. -/
def k2PullRel_retractSub (c : R₀ →+* R) (e : R →+* R₀) : Subgroup (SteinbergGroup I R) where
  carrier := {z | z * (ringMap c (ringMap e z))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e)}
  one_mem' := by
    change 1 * (ringMap c (ringMap e (1 : SteinbergGroup I R)))⁻¹ ∈
      Subgroup.closure (k2PullRel_genSet c e)
    rw [map_one, map_one, inv_one, mul_one]
    exact one_mem _
  mul_mem' := by
    intro z w hz hw
    have hz' : z * (ringMap c (ringMap e z))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e) := hz
    have hw' : w * (ringMap c (ringMap e w))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e) := hw
    change z * w * (ringMap c (ringMap e (z * w)))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e)
    have hgh := mul_mem hz' (k2PullRel_conj_mem c e (ringMap e z) hw')
    simp only [map_mul]
    convert hgh using 1
    group
  inv_mem' := by
    intro z hz
    have hz' : z * (ringMap c (ringMap e z))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e) := hz
    change z⁻¹ * (ringMap c (ringMap e z⁻¹))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e)
    have hconj := k2PullRel_conj_mem c e (ringMap e z)⁻¹ (inv_mem hz')
    simp only [map_inv] at hconj ⊢
    convert hconj using 1
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_retractSub

theorem k2PullRel_mem_retractSub_iff (c : R₀ →+* R) (e : R →+* R₀) (z : SteinbergGroup I R) :
    z ∈ k2PullRel_retractSub c e ↔
      z * (ringMap c (ringMap e z))⁻¹ ∈ Subgroup.closure (k2PullRel_genSet c e) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_mem_retractSub_iff

/-- Every element lies in `k2PullRel_retractSub`: it contains the generators. -/
theorem k2PullRel_mem_retractSub (c : R₀ →+* R) (e : R →+* R₀) (hce : ∀ a, e (c a) = a)
    (z : SteinbergGroup I R) : z ∈ k2PullRel_retractSub c e := by
  refine PresentedGroup.generated_by _ _ ?_ z
  rintro ⟨i, j, hij, b⟩
  change x i j hij b ∈ k2PullRel_retractSub c e
  rw [k2PullRel_mem_retractSub_iff, ringMap_x, ringMap_x, ← x_neg, x_mul]
  apply Subgroup.subset_closure
  refine ⟨1, i, j, hij, b + -c (e b), ?_, ?_⟩
  · rw [map_add, map_neg, hce, add_neg_cancel]
  · rw [map_one, one_mul, inv_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_mem_retractSub

/-- **Relative generation**: `e(z) = 1` puts `z` in the relative subgroup. -/
theorem k2PullRel_mem_closure_of_ringMap_eq_one (c : R₀ →+* R) (e : R →+* R₀)
    (hce : ∀ a, e (c a) = a) {z : SteinbergGroup I R} (hz : ringMap e z = 1) :
    z ∈ Subgroup.closure (k2PullRel_genSet c e) := by
  have h := (k2PullRel_mem_retractSub_iff c e z).mp (k2PullRel_mem_retractSub c e hce z)
  rwa [hz, map_one, inv_one, mul_one] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_mem_closure_of_ringMap_eq_one

end PullRelGen

end GroupApproximation.BooneHigman.Metabelian.ElemFP

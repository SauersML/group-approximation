import Mathlib.RingTheory.Ideal.Maximal
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateSt
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal
import GroupApproximation.Meta.AxiomGuard

/-!
# The local Quillen subgroup of `St(N, B[t])` at a prime

Lane `bh-met-85`, second helper module.  For an ideal `𝔪` of a commutative ring `B` put

  `T_𝔪 = {g ∈ St(N, B[t]) : ∃ a ∉ 𝔪, v_a(g) dies after padding}`   (`cubeDiagDilate_LocalSet`).

* If `𝔪` is prime, `T_𝔪` is a subgroup (`cubeDiagDilate_localSubgroup`).  `1 ∈ T_𝔪` with `a = 1`.
  For products, use `a b ∉ 𝔪`, the scaling `μ_c v_a = v_{c a}`, the crossed-homomorphism identity
  `v(g₁ g₂) = v(g₁) · C(g₁) v(g₂) C(g₁)⁻¹` and conjugation invariance of dying.  For inverses,
  use `v(g⁻¹) = C(g)⁻¹ v(g)⁻¹ C(g)`.  No normality of `K₂` or of `E` is used.
* So `closure T_𝔪 = T_𝔪` (`cubeDiagDilate_closure_localSet_le`).
* `T_𝔪` contains the constants `C(St(N, B))` and every element that dies after padding.
* The `K₂` bridge: dying after padding and Quillen differences in `K₂(N, B[t])` agree with the
  Steinberg-level notions on the underlying elements.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section LocalSubgroup

variable {B : Type*} [CommRing B] {N : ℕ}

/-- `T_𝔪 = {g ∈ St(N, B[t]) : ∃ a ∉ 𝔪, v_a(g) = g(t + a y) g(t)⁻¹ dies after padding}`. -/
def cubeDiagDilate_LocalSet (𝔪 : Ideal B) : Set (SteinbergGroup (Fin N) (Polynomial B)) :=
  {g | ∃ a : B, a ∉ 𝔪 ∧ cubeDiagDilate_StDies (cubeDiagDilate_stDiff g a)}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_LocalSet

theorem cubeDiagDilate_mem_localSet_iff (𝔪 : Ideal B) (g : SteinbergGroup (Fin N) (Polynomial B)) :
    g ∈ cubeDiagDilate_LocalSet 𝔪 ↔
      ∃ a : B, a ∉ 𝔪 ∧ cubeDiagDilate_StDies (cubeDiagDilate_stDiff g a) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_mem_localSet_iff

theorem cubeDiagDilate_stDies_stDiff_mul (g : SteinbergGroup (Fin N) (Polynomial B)) (c : B)
    {a : B} (ha : cubeDiagDilate_StDies (cubeDiagDilate_stDiff g a)) :
    cubeDiagDilate_StDies (cubeDiagDilate_stDiff g (c * a)) := by
  rw [← cubeDiagDilate_ringMap_quillenScale_stDiff g c a]
  exact cubeDiagDilate_stDies_ringMap (quillenScale B c) ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_stDiff_mul

theorem cubeDiagDilate_one_mem_localSet {𝔪 : Ideal B} (h𝔪 : 𝔪 ≠ ⊤) :
    (1 : SteinbergGroup (Fin N) (Polynomial B)) ∈ cubeDiagDilate_LocalSet 𝔪 :=
  (cubeDiagDilate_mem_localSet_iff 𝔪 1).mpr ⟨1, (Ideal.ne_top_iff_one 𝔪).mp h𝔪, by
    rw [cubeDiagDilate_stDiff_one]
    exact cubeDiagDilate_stDies_one⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_one_mem_localSet

theorem cubeDiagDilate_mul_mem_localSet {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    {g₁ g₂ : SteinbergGroup (Fin N) (Polynomial B)} (h₁ : g₁ ∈ cubeDiagDilate_LocalSet 𝔪)
    (h₂ : g₂ ∈ cubeDiagDilate_LocalSet 𝔪) : g₁ * g₂ ∈ cubeDiagDilate_LocalSet 𝔪 := by
  obtain ⟨a, ha, hda⟩ := (cubeDiagDilate_mem_localSet_iff 𝔪 g₁).mp h₁
  obtain ⟨b, hb, hdb⟩ := (cubeDiagDilate_mem_localSet_iff 𝔪 g₂).mp h₂
  have e₁ : cubeDiagDilate_StDies (cubeDiagDilate_stDiff g₁ (a * b)) := by
    rw [mul_comm a b]
    exact cubeDiagDilate_stDies_stDiff_mul g₁ b hda
  have e₂ : cubeDiagDilate_StDies (cubeDiagDilate_stDiff g₂ (a * b)) :=
    cubeDiagDilate_stDies_stDiff_mul g₂ a hdb
  refine (cubeDiagDilate_mem_localSet_iff 𝔪 (g₁ * g₂)).mpr
    ⟨a * b, fun hab ↦ (h𝔪.mem_or_mem hab).elim ha hb, ?_⟩
  rw [cubeDiagDilate_stDiff_mul]
  exact cubeDiagDilate_stDies_mul e₁ (cubeDiagDilate_stDies_conj _ e₂)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_mul_mem_localSet

theorem cubeDiagDilate_inv_mem_localSet {𝔪 : Ideal B} {g : SteinbergGroup (Fin N) (Polynomial B)}
    (hg : g ∈ cubeDiagDilate_LocalSet 𝔪) : g⁻¹ ∈ cubeDiagDilate_LocalSet 𝔪 := by
  obtain ⟨a, ha, hda⟩ := (cubeDiagDilate_mem_localSet_iff 𝔪 g).mp hg
  refine (cubeDiagDilate_mem_localSet_iff 𝔪 g⁻¹).mpr ⟨a, ha, ?_⟩
  have h := cubeDiagDilate_stDies_conj
    (SteinbergGroup.ringMap (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) g)⁻¹
    (cubeDiagDilate_stDies_inv hda)
  rw [inv_inv] at h
  rw [cubeDiagDilate_stDiff_inv]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_inv_mem_localSet

/-- **The local Quillen subgroup** `T_𝔪 ≤ St(N, B[t])` at a prime `𝔪`. -/
def cubeDiagDilate_localSubgroup (𝔪 : Ideal B) (h𝔪 : 𝔪.IsPrime) :
    Subgroup (SteinbergGroup (Fin N) (Polynomial B)) where
  carrier := cubeDiagDilate_LocalSet 𝔪
  mul_mem' := fun {g₁ g₂} h₁ h₂ ↦ cubeDiagDilate_mul_mem_localSet (g₁ := g₁) (g₂ := g₂) h𝔪 h₁ h₂
  one_mem' := cubeDiagDilate_one_mem_localSet h𝔪.ne_top
  inv_mem' := fun {g} hg ↦ cubeDiagDilate_inv_mem_localSet (𝔪 := 𝔪) (g := g) hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_localSubgroup

theorem cubeDiagDilate_mem_localSubgroup_iff (𝔪 : Ideal B) (h𝔪 : 𝔪.IsPrime)
    (g : SteinbergGroup (Fin N) (Polynomial B)) :
    g ∈ cubeDiagDilate_localSubgroup 𝔪 h𝔪 ↔ g ∈ cubeDiagDilate_LocalSet 𝔪 :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_mem_localSubgroup_iff

/-- `closure T_𝔪 ≤ T_𝔪`: products of local Quillen elements are local Quillen elements. -/
theorem cubeDiagDilate_closure_localSet_le (𝔪 : Ideal B) (h𝔪 : 𝔪.IsPrime) :
    Subgroup.closure (cubeDiagDilate_LocalSet (N := N) 𝔪) ≤ cubeDiagDilate_localSubgroup 𝔪 h𝔪 :=
  (Subgroup.closure_le _).mpr fun g hg ↦ (cubeDiagDilate_mem_localSubgroup_iff 𝔪 h𝔪 g).mpr hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_closure_localSet_le

end LocalSubgroup

end GroupApproximation.BooneHigman.Metabelian.ElemFP

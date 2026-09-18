import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabRow
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability from a column / row / column factorization (lane bh-met-54)

Here `R` is an arbitrary unital ring.  Put `P = stab St_n · padCol R^n`, the parabolic subgroup
fixing the last row, and `Q = stab St_n · padRow R^n`, the one fixing the last column.

* (A) If `p q ∈ K₂(n+1)` with `p ∈ P` and `q ∈ Q`, the last-row functional `e = (0, 1)` forces
  `q ∈ stab St_n`, so `p q ∈ P`.
* (B) `K₂(n+1) ∩ P ⊆ stab K₂(n)`.  From `padMat (stab g · padCol v) = 1`, acting on `(u, 0)`
  gives `padMat g = 1`, and acting on `(0, 1)` gives `v = 0`.
* (C) If `z x z⁻¹ = p q p'`, then `p' (z x z⁻¹) p'⁻¹ = (p' p) q ∈ K₂ ∩ P Q`, which lies in
  `stab K₂(n)` by (A) and (B).  `stab K₂(n)` is central (`map_stab_K2_le_center`), so
  conjugation does nothing and `x ∈ stab K₂(n)`.

Endpoint: `surjStab_k2_le_map_of_conjTriple`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (map_stab_K2_le_center)

section Group

variable {G : Type*} [Group G]

theorem surjStab_eq_conj_of_mem_center {a z : G} (h : z * a * z⁻¹ ∈ Subgroup.center G) :
    a = z * a * z⁻¹ := by
  have h2 := Subgroup.mem_center_iff.mp h z
  rw [inv_mul_cancel_right] at h2
  exact (mul_left_cancel h2).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_eq_conj_of_mem_center

theorem surjStab_conj_triple (a b c : G) : c * (a * b * c) * c⁻¹ = c * a * b := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_conj_triple

theorem surjStab_mul_swap_mid {a c s c' d : G} (hc : c * s = s * c') :
    a * c * (s * d) = a * s * (c' * d) := by
  rw [mul_assoc a c, ← mul_assoc c s d, hc, mul_assoc s c' d, ← mul_assoc a s]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_mul_swap_mid

end Group

variable {R : Type*} [Ring R] {n : ℕ}

/-- A Steinberg element with trivial elementary matrix lies in `K₂`. -/
theorem surjStab_mem_K2_of_padMat_eq_one {g : St n R} (h : padMat g = 1) :
    g ∈ K2 (Fin n) R :=
  (mem_K2_iff g).mpr (Subtype.ext (Units.ext h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_mem_K2_of_padMat_eq_one

/-- (B) `K₂(n+1) ∩ (stab St_n · padCol R^n) ⊆ stab K₂(n)`. -/
theorem surjStab_stab_mul_padCol_mem_map {g : St n R} {v : Fin n → R}
    (hk : stab n R g * padCol v ∈ K2 (Fin (n + 1)) R) :
    stab n R g * padCol v ∈ (K2 (Fin n) R).map (stab n R) := by
  have hmat : padMat (stab n R g) * padMat (padCol v) = 1 := by
    rw [← map_mul padMat (stab n R g) (padCol v)]
    exact padMat_of_mem_K2 hk
  have hg1 : padMat g = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have e : (padMat (stab n R g) * padMat (padCol v)) *ᵥ surjStabVec (Pi.single i (1 : R)) 0 =
        surjStabVec (Pi.single i (1 : R)) 0 := by
      rw [hmat, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, surjStab_padCol_mulVec_zero, surjStab_stab_mulVec] at e
    rw [Matrix.one_mulVec]
    exact surjStabVec_inj e
  have hv : v = 0 := by
    have e : (padMat (stab n R g) * padMat (padCol v)) *ᵥ surjStabVec (0 : Fin n → R) 1 =
        surjStabVec 0 1 := by
      rw [hmat, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, surjStab_padCol_mulVec_one, surjStab_stab_mulVec, hg1,
      Matrix.one_mulVec, zero_add] at e
    exact surjStabVec_inj e
  subst hv
  rw [padCol_zero, mul_one]
  exact Subgroup.mem_map_of_mem (stab n R) (surjStab_mem_K2_of_padMat_eq_one hg1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_stab_mul_padCol_mem_map

/-- (A)+(B) `K₂(n+1) ∩ P Q ⊆ stab K₂(n)`. -/
theorem surjStab_col_row_mem_map {g h : St n R} {v w : Fin n → R}
    (hk : stab n R g * padCol v * (stab n R h * padRow w) ∈ K2 (Fin (n + 1)) R) :
    stab n R g * padCol v * (stab n R h * padRow w) ∈ (K2 (Fin n) R).map (stab n R) := by
  have hrow : surjStabVec (0 : Fin n → R) (1 : R) ᵥ*
      padMat (stab n R g * padCol v * (stab n R h * padRow w)) = surjStabVec 0 1 := by
    rw [padMat_of_mem_K2 hk, Matrix.vecMul_one]
  simp only [map_mul, ← Matrix.vecMul_vecMul] at hrow
  rw [surjStab_vecMul_stab, surjStab_vecMul_padCol, surjStab_vecMul_stab,
    surjStab_vecMul_padRow, zero_add] at hrow
  have hw : w = 0 := surjStabVec_inj hrow
  subst hw
  rw [padRow_zero, mul_one] at hk ⊢
  rw [mul_assoc, surjStab_padCol_mul_stab, ← mul_assoc, ← map_mul (stab n R) g h] at hk ⊢
  exact surjStab_stab_mul_padCol_mem_map hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_col_row_mem_map

/-- `x` has a conjugate of the form `(stab g₁ · padCol v₁)(stab g₂ · padRow w)(stab g₃ · padCol v₃)`,
i.e. a conjugate in `P Q P`. -/
def SurjStabConjTriple (x : St (n + 1) R) : Prop :=
  ∃ (z : St (n + 1) R) (g₁ g₂ g₃ : St n R) (v₁ w v₃ : Fin n → R),
    z * x * z⁻¹ =
      stab n R g₁ * padCol v₁ * (stab n R g₂ * padRow w) * (stab n R g₃ * padCol v₃)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabConjTriple

/-- (C) A `K₂` element with a conjugate in `P Q P` lies in `stab K₂(n)`. -/
theorem surjStab_mem_map_of_conjTriple {x : St (n + 1) R} (hx : x ∈ K2 (Fin (n + 1)) R)
    (h : SurjStabConjTriple x) : x ∈ (K2 (Fin n) R).map (stab n R) := by
  obtain ⟨z, g₁, g₂, g₃, v₁, w, v₃, hz⟩ := h
  have hN : (K2 (Fin (n + 1)) R).Normal := inferInstance
  have hyK : z * x * z⁻¹ ∈ K2 (Fin (n + 1)) R := hN.conj_mem x hx z
  have e : stab n R (g₃ * g₁) * padCol (padMat g₁⁻¹ *ᵥ v₃ + v₁) * (stab n R g₂ * padRow w) =
      (stab n R g₃ * padCol v₃) * (z * x * z⁻¹) * (stab n R g₃ * padCol v₃)⁻¹ := by
    rw [hz, surjStab_conj_triple (stab n R g₁ * padCol v₁) (stab n R g₂ * padRow w)
        (stab n R g₃ * padCol v₃), map_mul (stab n R) g₃ g₁, padCol_add,
      surjStab_mul_swap_mid (surjStab_padCol_mul_stab g₁ v₃)]
  have hk' : stab n R (g₃ * g₁) * padCol (padMat g₁⁻¹ *ᵥ v₃ + v₁) * (stab n R g₂ * padRow w) ∈
      K2 (Fin (n + 1)) R := by
    rw [e]
    exact hN.conj_mem _ hyK _
  have hmap := surjStab_col_row_mem_map hk'
  rw [e] at hmap
  have hy : z * x * z⁻¹ ∈ (K2 (Fin n) R).map (stab n R) := by
    rw [surjStab_eq_conj_of_mem_center (map_stab_K2_le_center hmap)]
    exact hmap
  rw [surjStab_eq_conj_of_mem_center (map_stab_K2_le_center hy)]
  exact hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_mem_map_of_conjTriple

/-- Surjective `K₂` stability from `P Q P` conjugates, over any ring. -/
theorem surjStab_k2_le_map_of_conjTriple
    (h : ∀ x ∈ K2 (Fin (n + 1)) R, SurjStabConjTriple x) :
    K2 (Fin (n + 1)) R ≤ (K2 (Fin n) R).map (stab n R) := by
  intro x hx
  exact surjStab_mem_map_of_conjTriple hx (h x hx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_k2_le_map_of_conjTriple

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

import Mathlib.Tactic.Group
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenComp
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg-level Quillen differences and dying after padding

Lane `bh-met-85`, first helper module.  `ElemFPK2LocalQuillenIdeal` works with the Quillen
difference of an element of `K₂(N, B[t])`.  Here the same construction is made for an arbitrary
element `g ∈ St(N, B[t])`, which need not lie in `K₂`:

  `v_a(g) = σ_a(g) · C(g)⁻¹ = g(t + a y) · g(t)⁻¹ ∈ St(N, B[t][y])`   (`cubeDiagDilate_stDiff`).

* `cubeDiagDilate_StDies g`: some padding `St(N) → St(M)` sends `g` to `1`.  This set is closed
  under `1`, products, inverses, conjugation by any element, coefficient maps, and padding in
  either direction.  None of this uses a normality theorem.
* `v_0 = 1`, `v_a(1) = 1`, `v_a(C h) = 1`, `μ_c v_a = v_{c a}` and `v_{a+b} = τ_b(v_a) · v_b`,
  exactly as for `K₂`.
* The crossed-homomorphism identities `v_a(g₁ g₂) = v_a(g₁) · C(g₁) v_a(g₂) C(g₁)⁻¹` and
  `v_a(g⁻¹) = C(g)⁻¹ v_a(g)⁻¹ C(g)`.
* Padding commutes with `v_a`.

Everything here is formal: functoriality of `St(N, -)`, padding, and group identities.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section StDies

variable {R : Type*} [Ring R] {N : ℕ}

/-- `g ∈ St(N, R)` dies after padding: some padding `St(N, R) → St(M, R)` sends it to `1`. -/
def cubeDiagDilate_StDies (g : SteinbergGroup (Fin N) R) : Prop :=
  ∃ M : ℕ, ∃ hNM : N ≤ M, SteinbergGroup.indexMap (R := R) (Fin.castLEEmb hNM) g = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_StDies

theorem cubeDiagDilate_indexMap_eq_one_of_le {M₁ M : ℕ} (h₁ : N ≤ M₁) (hM : M₁ ≤ M) (h : N ≤ M)
    {g : SteinbergGroup (Fin N) R} (hg : SteinbergGroup.indexMap (Fin.castLEEmb h₁) g = 1) :
    SteinbergGroup.indexMap (Fin.castLEEmb h) g = 1 := by
  have h2 := GroupApproximation.Full.LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ hM g
  rw [hg, map_one] at h2
  exact h2.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_indexMap_eq_one_of_le

theorem cubeDiagDilate_stDies_one : cubeDiagDilate_StDies (1 : SteinbergGroup (Fin N) R) :=
  ⟨N, le_rfl, map_one _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_one

theorem cubeDiagDilate_stDies_mul {g₁ g₂ : SteinbergGroup (Fin N) R}
    (h₁ : cubeDiagDilate_StDies g₁) (h₂ : cubeDiagDilate_StDies g₂) :
    cubeDiagDilate_StDies (g₁ * g₂) := by
  obtain ⟨M₁, hN₁, hM₁⟩ := h₁
  obtain ⟨M₂, hN₂, hM₂⟩ := h₂
  have e₁ : SteinbergGroup.indexMap (Fin.castLEEmb (hN₁.trans (le_max_left M₁ M₂))) g₁ = 1 :=
    cubeDiagDilate_indexMap_eq_one_of_le hN₁ (le_max_left M₁ M₂) _ hM₁
  have e₂ : SteinbergGroup.indexMap (Fin.castLEEmb (hN₁.trans (le_max_left M₁ M₂))) g₂ = 1 :=
    cubeDiagDilate_indexMap_eq_one_of_le hN₂ (le_max_right M₁ M₂) _ hM₂
  exact ⟨max M₁ M₂, hN₁.trans (le_max_left M₁ M₂), by rw [map_mul, e₁, e₂, one_mul]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_mul

theorem cubeDiagDilate_stDies_inv {g : SteinbergGroup (Fin N) R} (hg : cubeDiagDilate_StDies g) :
    cubeDiagDilate_StDies g⁻¹ := by
  obtain ⟨M, hNM, hM⟩ := hg
  exact ⟨M, hNM, by rw [map_inv, hM, inv_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_inv

/-- Dying after padding is invariant under conjugation by any element of `St(N, R)`. -/
theorem cubeDiagDilate_stDies_conj (k : SteinbergGroup (Fin N) R) {g : SteinbergGroup (Fin N) R}
    (hg : cubeDiagDilate_StDies g) : cubeDiagDilate_StDies (k * g * k⁻¹) := by
  obtain ⟨M, hNM, hM⟩ := hg
  exact ⟨M, hNM, by rw [map_mul, map_mul, hM, mul_one, map_inv, mul_inv_cancel]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_conj

theorem cubeDiagDilate_stDies_ringMap {S : Type*} [Ring S] (f : R →+* S)
    {g : SteinbergGroup (Fin N) R} (hg : cubeDiagDilate_StDies g) :
    cubeDiagDilate_StDies (SteinbergGroup.ringMap f g) := by
  obtain ⟨M, hNM, hM⟩ := hg
  exact ⟨M, hNM, by rw [GroupApproximation.Full.LVStableK2.indexMap_ringMap, hM, map_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_ringMap

/-- Dying after padding descends along a padding `St(N) → St(N')`. -/
theorem cubeDiagDilate_stDies_of_indexMap {N' : ℕ} (h : N ≤ N') {x : SteinbergGroup (Fin N) R}
    (hx : cubeDiagDilate_StDies (SteinbergGroup.indexMap (Fin.castLEEmb h) x)) :
    cubeDiagDilate_StDies x := by
  obtain ⟨M, hM, hM'⟩ := hx
  exact ⟨M, h.trans hM,
    (GroupApproximation.Full.LVH2GL3.indexMap_castLEEmb_castLEEmb h hM x).symm.trans hM'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_of_indexMap

/-- Dying after padding is preserved by a padding `St(N) → St(N')`. -/
theorem cubeDiagDilate_stDies_indexMap {N' : ℕ} (h : N ≤ N') {x : SteinbergGroup (Fin N) R}
    (hx : cubeDiagDilate_StDies x) :
    cubeDiagDilate_StDies (SteinbergGroup.indexMap (Fin.castLEEmb h) x) := by
  obtain ⟨M, hNM, hM⟩ := hx
  have e : SteinbergGroup.indexMap (Fin.castLEEmb (h.trans (le_max_left N' M))) x = 1 :=
    cubeDiagDilate_indexMap_eq_one_of_le hNM (le_max_right N' M) _ hM
  exact ⟨max N' M, le_max_left N' M,
    (GroupApproximation.Full.LVH2GL3.indexMap_castLEEmb_castLEEmb h (le_max_left N' M) x).trans e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeDiagDilate_stDies_indexMap

end StDies

end GroupApproximation.BooneHigman.Metabelian.ElemFP

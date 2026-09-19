import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXa2
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 1.3(b): conjugation of `X_{v,w}(a)`

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Lemma 1.3(b). For `r ≥ 5`,
`α ∈ St_r(A)`, and `a, b` in the ideal of the coordinates of `v`:
`α X_{v,bw}(a) α⁻¹ = X_{αv, bwα⁻¹}(a)`.
Here `a = u_a v`, `b = u_b v`, and `X_{v,bw}(a) = Xa v ((u_b v) w) u_a` (`Xa_conj`).

Tulenbaev's proof, which is followed here: the canonical pieces of `b w` have `r - 2 ≥ 3` zeros.
So for a generator `x_ij(c)` each piece has a zero outside `{i, j}` (`ex_conj_fix`), and each
conjugated piece still has two zeros (`Xa_conj_x`). General `α` follows by induction on words;
at each step the row is decomposed again (`Xa_eq_prod`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)

/-- The matrix of `π(y)`. -/
abbrev pm (y : SteinbergGroup I A) : Matrix I I A :=
  (((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) : Matrix I I A)

theorem pm_mul (y z : SteinbergGroup I A) : pm (y * z) = pm y * pm z := by
  simp only [pm, map_mul, Subgroup.coe_mul, Units.val_mul]

theorem pm_one : pm (1 : SteinbergGroup I A) = 1 := by
  simp only [pm, map_one, OneMemClass.coe_one, Units.val_one]

theorem pm_inv_mul (y : SteinbergGroup I A) : pm y⁻¹ * pm y = 1 := by
  rw [← pm_mul, inv_mul_cancel, pm_one]

theorem coe_inv_pm (y : SteinbergGroup I A) :
    ((((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) :
      Matrix I I A) = pm y⁻¹ := by
  rw [pm, map_inv, Subgroup.coe_inv]

theorem dot_transform (y : SteinbergGroup I A) (x z : I → A) :
    (x ᵥ* pm y⁻¹) ⬝ᵥ (pm y *ᵥ z) = x ⬝ᵥ z := by
  rw [dotProduct_mulVec, vecMul_vecMul, pm_inv_mul, vecMul_one]

theorem E_conj_pm (y : SteinbergGroup I A) {v w : I → A} (h : (v, w) ∈ U I A) :
    y * E hX v w * y⁻¹ = E hX (pm y *ᵥ v) (w ᵥ* pm y⁻¹) := by
  rw [E_conj_st hX y h, coe_inv_pm]

/-- Conjugation of `X_r(v, w)` by `y` when `π(y)` fixes `e_r` and the `r`-th coordinate of `v`. -/
theorem ex_conj_fix (y : SteinbergGroup I A) {r : I} {v w : I → A} (hr : w r = 0)
    (hw : w ⬝ᵥ v = 0) (hMr : pm y *ᵥ Pi.single r 1 = Pi.single r 1)
    (hMv : (pm y *ᵥ v) r = v r) :
    y * ex hX r v w * y⁻¹ = ex hX r (pm y *ᵥ v) (w ᵥ* pm y⁻¹) := by
  have hq1 : (Pi.single r (1 : A), (v r - 1) • w) ∈ U I A :=
    memU (isUnimodular_single r) (smul_dot _ (dot_single hr))
  have hq2 : (v + (1 - v r) • Pi.single r (1 : A), w) ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v r)) (dot_tl hr hw _)
  rw [ex, ex, conj_mul_conj, E_conj_pm hX y hq1, E_conj_pm hX y hq2, hMv, smul_vecMul,
    mulVec_add, mulVec_smul, hMr]

#audit_axioms ex_conj_fix

theorem mulVec_pm_x {i j : I} (hij : i ≠ j) (t : A) (v : I → A) :
    pm (x i j hij t) *ᵥ v = v + (Pi.single j t ⬝ᵥ v) • Pi.single i 1 := by
  have h := congrArg Prod.fst (RelPres.smulPair_elementaryUnit hij t (v, 0))
  rw [pm, projection_x]
  exact h

theorem vecMul_pm_x_inv {i j : I} (hij : i ≠ j) (t : A) (w : I → A) :
    w ᵥ* pm (x i j hij t)⁻¹ = w - (w ⬝ᵥ Pi.single i 1) • Pi.single j t := by
  have h := congrArg Prod.snd (RelPres.smulPair_elementaryUnit hij t (0, w))
  rw [← coe_inv_pm, projection_x]
  exact h

omit [DecidableEq I] in
theorem exists_not_mem (L : List I) (h : L.length + 1 ≤ Fintype.card I) : ∃ l, l ∉ L := by
  classical
  have hc : 0 < (Finset.univ \ L.toFinset).card := by
    have h1 := Finset.le_card_sdiff L.toFinset Finset.univ
    have h2 := List.toFinset_card_le (l := L)
    rw [Finset.card_univ] at h1
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hc
  exact ⟨l, fun h' => (Finset.mem_sdiff.mp hl).2 (List.mem_toFinset.mpr h')⟩

omit [DecidableEq I] in
theorem exists_two_not_mem (L : List I) (h : L.length + 2 ≤ Fintype.card I) :
    ∃ l m, l ≠ m ∧ l ∉ L ∧ m ∉ L := by
  classical
  have hc : 1 < (Finset.univ \ L.toFinset).card := by
    have h1 := Finset.le_card_sdiff L.toFinset Finset.univ
    have h2 := List.toFinset_card_le (l := L)
    rw [Finset.card_univ] at h1
    omega
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.mp hc
  exact ⟨l, m, hlm, fun h' => (Finset.mem_sdiff.mp hl).2 (List.mem_toFinset.mpr h'),
    fun h' => (Finset.mem_sdiff.mp hm).2 (List.mem_toFinset.mpr h')⟩

/-- **Conjugation of a piece by a generator**: if `y ⊥ v` vanishes off `{p, q}` and `|I| ≥ 5`,
then `x_ij(t) X(v, y) x_ij(-t) = X(x_ij(t) v, y x_ij(-t))`. -/
theorem tx_conj_x (h5 : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) (t : A) {v y : I → A}
    (hyv : y ⬝ᵥ v = 0) {p q : I} (hy : ∀ l, l ≠ p → l ≠ q → y l = 0) :
    x i j hij t * tx hX v y * (x i j hij t)⁻¹ =
      tx hX (pm (x i j hij t) *ᵥ v) (y ᵥ* pm (x i j hij t)⁻¹) := by
  obtain ⟨r, hr⟩ := exists_not_mem [p, q, i, j] (by simp only [List.length_cons,
    List.length_nil]; omega)
  simp at hr
  obtain ⟨hrp, hrq, hri, hrj⟩ := hr
  have hyr : y r = 0 := hy r hrp hrq
  have hMr : pm (x i j hij t) *ᵥ Pi.single r (1 : A) = Pi.single r 1 := by
    rw [mulVec_pm_x, single_dotProduct, Pi.single_eq_of_ne hrj.symm, mul_zero, zero_smul,
      add_zero]
  have hMv : (pm (x i j hij t) *ᵥ v) r = v r := by
    rw [mulVec_pm_x, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hri, smul_zero, add_zero]
  have hyr' : (y ᵥ* pm (x i j hij t)⁻¹) r = 0 := by
    rw [vecMul_pm_x_inv, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hrj, smul_zero,
      sub_zero, hyr]
  rw [tx_eq hX hyr hyv, ex_conj_fix hX _ hyr hyv hMr hMv,
    tx_eq hX (v := pm (x i j hij t) *ᵥ v) hyr' (by rw [dot_transform, hyv])]

#audit_axioms tx_conj_x

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation

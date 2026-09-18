import Mathlib.Tactic.LinearCombination
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriData
import GroupApproximation.Meta.AxiomGuard

/-!
# Triple lemma: a root, a rank-one datum and a root conjugate

Lane `bh-met-93k`, main module.  Let `R` be a commutative ring with no zero divisors,
`(y₂, α, ρ)` a rank-one datum with `ρ ⬝ᵥ α = 0` (for example `y₂ = h x_{i₂j₂}(c₂) h⁻¹`), and
`E = g₃ x_kl(c) g₃⁻¹`.

* **`k2KarTri_stab_triple`**: if `padMat (x_ij(b) y₂ E) = 1` then `stab (x_ij(b) y₂ E) = 1`.

Proof.  If `b = 0` apply `k2KarTri_stab_rankOne_mul_conj` to `y₂`.  Otherwise
`padMat (x_ij(b) y₂) = padMat E⁻¹ = 1 + V₃ W₃ᵀ` (`k2KarTri_padMat_left`), and comparing entries
with `(1 + b e_ij)(1 + α ρᵀ)` gives, for `p ≠ i`, `q ≠ j`, a vanishing `2 × 2` minor of `V₃ W₃ᵀ`
that equals `b α_p ρ_q` (`k2KarTri_entries_zero`).  Hence either `α` is supported on `{i}` or `ρ`
on `{j}`, and `k2KarTri_rowCase` / `k2KarTri_colCase` make `x_ij(b) y₂` a rank-one datum; conclude
with `k2KarTri_stab_rankOne_mul_conj`.  No `1 ≠ 0` and no relativity (`fst b = 0`) is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriMainRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- If `padMat (z · g x_kl(c) g⁻¹) = 1` then `padMat z = padMat (g x_kl(-c) g⁻¹)`. -/
theorem k2KarTri_padMat_left {z g₃ : St n R} {k l : Fin n} {hkl : k ≠ l} {c : R}
    (h : padMat (z * (g₃ * x k l hkl c * g₃⁻¹)) = 1) :
    padMat z = 1 + Matrix.vecMulVec (padMat g₃ *ᵥ Pi.single k (-c))
      (Pi.single l (1 : R) ᵥ* padMat g₃⁻¹) := by
  have hE : g₃ * x k l hkl c * g₃⁻¹ * (g₃ * x k l hkl (-c) * g₃⁻¹) = 1 := by
    have e : g₃ * x k l hkl c * g₃⁻¹ * (g₃ * x k l hkl (-c) * g₃⁻¹) =
        g₃ * (x k l hkl c * x k l hkl (-c)) * g₃⁻¹ := by group
    rw [e, x_mul, add_neg_cancel, x_zero, mul_one, mul_inv_cancel]
  have e : z = z * (g₃ * x k l hkl c * g₃⁻¹) * (g₃ * x k l hkl (-c) * g₃⁻¹) := by
    rw [mul_assoc z, hE, mul_one]
  rw [e, map_mul padMat _ (g₃ * x k l hkl (-c) * g₃⁻¹), h, one_mul, k2KarTri_padMat_conj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_left

end KarTriMainRing

section KarTriMainComm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Minor lemma.**  If `padMat (x_ij(b) y₂) = 1 + V₃ W₃ᵀ`, `padMat y₂ = 1 + α ρᵀ` and
`b ≠ 0`, then `α_p ρ_q = 0` for `p ≠ i`, `q ≠ j`. -/
theorem k2KarTri_entries_zero (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) {y₂ : St n R}
    {α ρ : Fin n → R} (hm₂ : padMat y₂ = 1 + Matrix.vecMulVec α ρ) {i j : Fin n} {hij : i ≠ j}
    {b : R} (hb : b ≠ 0) {V₃ W₃ : Fin n → R}
    (hy : padMat (x i j hij b * y₂) = 1 + Matrix.vecMulVec V₃ W₃) (p : Fin n) (hp : p ≠ i)
    (q : Fin n) (hq : q ≠ j) : α p * ρ q = 0 := by
  have E : ∀ p' q', padMat (x i j hij b * y₂) p' q' =
      (1 : Matrix (Fin n) (Fin n) R) p' q' + V₃ p' * W₃ q' := fun p' q' ↦ by
    rw [hy, Matrix.add_apply, Matrix.vecMulVec_apply]
  have M : ∀ p' q', padMat y₂ p' q' = (1 : Matrix (Fin n) (Fin n) R) p' q' + α p' * ρ q' :=
    fun p' q' ↦ by rw [hm₂, Matrix.add_apply, Matrix.vecMulVec_apply]
  have A1 : α p * ρ q = V₃ p * W₃ q := by
    have e := E p q
    rw [k2KarTri_padMat_x_mul_apply_of_ne y₂ i j hij b hp q, M] at e
    linear_combination e
  have A2 : α p * ρ j = V₃ p * W₃ j := by
    have e := E p j
    rw [k2KarTri_padMat_x_mul_apply_of_ne y₂ i j hij b hp j, M] at e
    linear_combination e
  have A3 : α i * ρ q + b * (α j * ρ q) = V₃ i * W₃ q := by
    have e := E i q
    rw [k2KarTri_padMat_x_mul_apply_same, M, M, Matrix.one_apply_ne (Ne.symm hq)] at e
    linear_combination e
  have A4 : α i * ρ j + b * (1 + α j * ρ j) = V₃ i * W₃ j := by
    have e := E i j
    rw [k2KarTri_padMat_x_mul_apply_same, M, M, Matrix.one_apply_eq] at e
    linear_combination e
  have key : b * (α p * ρ q) = 0 := by
    linear_combination A1 * (α i * ρ j + b * (1 + α j * ρ j)) + (V₃ p * W₃ q) * A4 -
      A2 * (α i * ρ q + b * (α j * ρ q)) - (V₃ p * W₃ j) * A3
  exact (hR _ _ key).resolve_left hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_entries_zero

/-- **Triple lemma.**  Over a commutative ring with no zero divisors, if `(y₂, α, ρ)` is a
rank-one datum with `ρ ⬝ᵥ α = 0` and `padMat (x_ij(b) y₂ · g₃ x_kl(c) g₃⁻¹) = 1`, then
`stab (x_ij(b) y₂ · g₃ x_kl(c) g₃⁻¹) = 1`. -/
theorem k2KarTri_stab_triple (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) (i j : Fin n)
    (hij : i ≠ j) (b : R) {y₂ : St n R} {α ρ : Fin n → R}
    (hs₂ : stab n R y₂ = ⁅padCol α, padRow ρ⁆) (hm₂ : padMat y₂ = 1 + Matrix.vecMulVec α ρ)
    (hd₂ : ρ ⬝ᵥ α = 0) (g₃ : St n R) (k l : Fin n) (hkl : k ≠ l) (c : R)
    (h : padMat (x i j hij b * y₂ * (g₃ * x k l hkl c * g₃⁻¹)) = 1) :
    stab n R (x i j hij b * y₂ * (g₃ * x k l hkl c * g₃⁻¹)) = 1 := by
  by_cases hb : b = 0
  · subst hb
    rw [x_zero, one_mul] at h ⊢
    exact k2KarTri_stab_rankOne_mul_conj hR hs₂ hm₂ g₃ k l hkl c h
  have hz := k2KarTri_entries_zero hR hm₂ hb (k2KarTri_padMat_left h)
  by_cases hα : ∀ p, p ≠ i → α p = 0
  · obtain ⟨hs, hm⟩ := k2KarTri_rowCase hR hs₂ hm₂ hd₂ i j hij b hα
    exact k2KarTri_stab_rankOne_mul_conj hR hs hm g₃ k l hkl c h
  · push Not at hα
    obtain ⟨p₀, hp₀, hα₀⟩ := hα
    obtain ⟨hs, hm⟩ := k2KarTri_colCase hR hs₂ hm₂ hd₂ i j hij b
      fun q hq ↦ (hR _ _ (hz p₀ hp₀ q hq)).resolve_left hα₀
    exact k2KarTri_stab_rankOne_mul_conj hR hs hm g₃ k l hkl c h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_triple

end KarTriMainComm

end GroupApproximation.BooneHigman.Metabelian.ElemFP

import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabGaussEuclid
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability: disjointness from the last row and Euclid (lane bh-met-82)

Target: `SurjStabFactorDisjStatement`.

## What is proved

* `surjStabGauss_dot_eq_zero` (any unital ring): if `x ∈ K₂(n+1)` and
  `z x z⁻¹ = stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`, then `w ⬝ᵥ c = 0`.
  The proof conjugates by `stab g₂` to get
  `y = A · padRow w'` with `A = stab (g₂ g₁) · padCol v · padRow w · padCol c`, and `y ∈ K₂`.
  So `padMat A = padMat (padRow (-w'))`.  Apply both sides to the last row `e = (0, 1)`.
  The left side gives `(w, 1 + w ⬝ᵥ c)` and the right side gives `(-w', 1)`.
  Comparing last coordinates gives `w ⬝ᵥ c = 0`.
* `surjStabGauss_factorDisj_of_single` (any ring without zero divisors): if the middle row is
  `w = e_i β`, then `β c_i = 0`.  So `c` and `w` have disjoint supports.
* `surjStabFactorDisj_of_surjStabGaussForm`: by `surjStabGauss_away_reach_single` (Euclid over
  `ℤ[1/m]`) and `surjStabGauss_form_move`, every middle row can be moved to a single.
  `ℤ[1/m]` is a domain.

## Remaining gap

`SurjStabGaussFormStatement`: every `x ∈ K₂(n+1, ℤ[1/m])` (`m > 0`, `n ≥ 4`) has *some*
conjugate `stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`, with no constraint
on supports.

Truth check.  TRUE.  `ℤ[1/m]` is Dedekind with `sr ≤ 2`, so Dennis / van der Kallen surjective
stability gives `K₂(n) ↠ K₂(n+1)`.  Every element of `stab K₂(n)` has the form with
`z = 1` and `v = w = c = w' = 0`.

LOUD: at the level of Statements, this is logically EQUIVALENT to `SurjStabFactorDisjStatement`
(`surjStabGaussForm_of_surjStabFactorDisj` drops the disjointness clause), because both are
theorems.  Per element it is strictly WEAKER: `SurjStabFactorDisj x → ∃ w, SurjStabGaussForm x w`
with no hypothesis.  It is strictly SMALLER in proof content, because the disjointness clause
(the part of the Gauss step that arranges supports) is derived here from the `K₂` hypothesis,
the last-row functional and Euclid.  What remains is the van der Kallen length reduction: write a
conjugate of a relation as a `P V U V H` word at all.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- The last-row functional forces `w ⬝ᵥ c = 0` in a `P V U V H` conjugate of a `K₂` element. -/
theorem surjStabGauss_dot_eq_zero {x z : St (n + 1) R} {g₁ g₂ : St n R} {v w c w' : Fin n → R}
    (hx : x ∈ K2 (Fin (n + 1)) R)
    (hz : z * x * z⁻¹ =
      stab n R g₁ * padCol v * padRow w * padCol c * padRow w' * stab n R g₂) :
    w ⬝ᵥ c = 0 := by
  have hN : (K2 (Fin (n + 1)) R).Normal := inferInstance
  have hyK : z * x * z⁻¹ ∈ K2 (Fin (n + 1)) R := hN.conj_mem x hx z
  have e : stab n R g₂ * (z * x * z⁻¹) * (stab n R g₂)⁻¹ =
      stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w' := by
    rw [hz, map_mul (stab n R) g₂ g₁]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hk : stab n R (g₂ * g₁) * padCol v * padRow w * padCol c * padRow w' ∈
      K2 (Fin (n + 1)) R := by
    rw [← e]
    exact hN.conj_mem _ hyK _
  have h1 : padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) *
      padMat (padRow w') = 1 := by
    rw [← map_mul padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) (padRow w')]
    exact padMat_of_mem_K2 hk
  have hA : padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) =
      padMat (padRow (-w')) := by
    calc padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c)
        = padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) *
            padMat (padRow w' * padRow (-w')) := by
          rw [← padRow_add, add_neg_cancel, padRow_zero, map_one, mul_one]
      _ = padMat (padRow (-w')) := by
          rw [map_mul padMat (padRow w') (padRow (-w')), ← mul_assoc, h1, one_mul]
  have h2 : surjStabVec (0 : Fin n → R) (1 : R) ᵥ*
      padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) = surjStabVec (-w') 1 := by
    rw [hA, surjStab_vecMul_padRow, zero_add]
  have h3 : surjStabVec (0 : Fin n → R) (1 : R) ᵥ*
      padMat (stab n R (g₂ * g₁) * padCol v * padRow w * padCol c) =
        surjStabVec w (1 + w ⬝ᵥ c) := by
    simp only [map_mul, ← Matrix.vecMul_vecMul]
    rw [surjStab_vecMul_stab, surjStab_vecMul_stab, surjStab_vecMul_padCol,
      surjStab_vecMul_padRow, zero_add, surjStabFactor_vecMul_padCol]
  have h4 := congrFun (h3.symm.trans h2) (Fin.last n)
  rw [surjStabVec_last, surjStabVec_last] at h4
  exact add_left_cancel (h4.trans (add_zero (1 : R)).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_dot_eq_zero

/-- A form with a single middle row, over a ring without zero divisors, is disjoint. -/
theorem surjStabGauss_factorDisj_of_single [NoZeroDivisors R] {x : St (n + 1) R}
    (hx : x ∈ K2 (Fin (n + 1)) R) {i : Fin n} {β : R}
    (hF : SurjStabGaussForm x (Pi.single i β)) : SurjStabFactorDisj x := by
  obtain ⟨z, g₁, g₂, v, c, w', hz⟩ := hF
  have hd := surjStabGauss_dot_eq_zero hx hz
  rw [single_dotProduct] at hd
  refine ⟨z, g₁, g₂, v, Pi.single i β, c, w', fun k => ?_, hz⟩
  by_cases hk : k = i
  · rw [hk]
    rcases mul_eq_zero.mp hd with h | h
    · exact Or.inr (by rw [Pi.single_eq_same]; exact h)
    · exact Or.inl h
  · exact Or.inr (Pi.single_eq_of_ne hk β)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_factorDisj_of_single

/-- **Remaining gap**: every `K₂` element over `ℤ[1/m]` (`m > 0`, `n ≥ 4`) has some
`P V U V H` conjugate, with no constraint on the supports. -/
def SurjStabGaussFormStatement : Prop :=
  ∀ m n : ℕ, 0 < m → 4 ≤ n → ∀ x ∈ K2 (Fin (n + 1)) (Localization.Away (m : ℤ)),
    ∃ w : Fin n → Localization.Away (m : ℤ), SurjStabGaussForm x w

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabGaussFormStatement

/-- **Endpoint**: the disjoint factorization statement from the unconstrained form statement. -/
theorem surjStabFactorDisj_of_surjStabGaussForm (h : SurjStabGaussFormStatement) :
    SurjStabFactorDisjStatement := by
  intro m n hm hn x hx
  haveI : IsDomain (Localization.Away (m : ℤ)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 hm.ne'))
  obtain ⟨w, hF⟩ := h m n hm hn x hx
  obtain ⟨i, β, hr⟩ := surjStabGauss_away_reach_single (m := m) (by omega : 0 < n) w
  exact surjStabGauss_factorDisj_of_single hx (surjStabGauss_form_of_reach hF hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactorDisj_of_surjStabGaussForm

/-- **Composite endpoint**: the `P Q P` statement from the unconstrained form statement. -/
theorem surjStabConjTriple_of_surjStabGaussForm (h : SurjStabGaussFormStatement) :
    SurjStabConjTripleStatement :=
  surjStabConjTriple_of_surjStabFactorDisj (surjStabFactorDisj_of_surjStabGaussForm h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabConjTriple_of_surjStabGaussForm

/-- LOUD equivalence: the gap follows back from `SurjStabFactorDisjStatement` by dropping the
disjointness clause. -/
theorem surjStabGaussForm_of_surjStabFactorDisj (h : SurjStabFactorDisjStatement) :
    SurjStabGaussFormStatement := by
  intro m n hm hn x hx
  obtain ⟨z, g₁, g₂, v, w, c, w', _, hz⟩ := h m n hm hn x hx
  exact ⟨w, z, g₁, g₂, v, c, w', hz⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGaussForm_of_surjStabFactorDisj

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

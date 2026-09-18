import GroupApproximation.BooneHigman.Metabelian.SuslinMonicNagataDeg
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagata's change of variables over an integral domain: the leading coefficient

Lane `bh-met-91n`, part 2.  Continuation of `SuslinMonicNagataDeg` (Nagata's proof from
Mathlib's `Mathlib/RingTheory/NoetherNormalization.lean`, Copyright (c) 2025 Sihan Su;
Apache 2.0; authors Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su), over an integral domain.

Over a field Mathlib concludes that the leading coefficient in `X_0` of `T f` is a unit.  Over
a domain the same computation shows that it is the CONSTANT `C a` with `a ≠ 0` the coefficient
of the monomial of `f` of largest weight (`suslinMonic_T_leadingCoeff_eq_C`).

`suslinMonic_nagata`: every nonzero `g ∈ R[s_0,…,s_{n-1}][X]` is sent by a ring automorphism
to a polynomial whose leading coefficient in `X` is a nonzero constant `C a`, `a ∈ R`.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) R)
variable (v : Fin (n + 1) →₀ ℕ)

section equivT

-- Mathlib's lakefile builds the original proofs with this option (core default: 1).
set_option maxSynthPendingDepth 3

theorem suslinMonic_leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv R n ((suslinMonic_T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap R _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv R n) ((suslinMonic_T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_leadingCoeff_finSuccEquiv_t

/-- `suslinMonic_T` maps `f ≠ 0` to a polynomial in `X_0` whose leading coefficient is a
nonzero constant. -/
theorem suslinMonic_T_leadingCoeff_eq_C (fne : f ≠ 0) :
    ∃ a : R, a ≠ 0 ∧
      (finSuccEquiv R n (suslinMonic_T f f)).leadingCoeff = MvPolynomial.C a := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (suslinMonic_T f ((monomial v) (coeff v f))).degreeOf 0)
    (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv R n ((suslinMonic_T f) (h x))).degree <
      (finSuccEquiv R n ((suslinMonic_T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using suslinMonic_degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff :
      (finSuccEquiv R n ((suslinMonic_T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv R n ((suslinMonic_T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv R n ((suslinMonic_T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  refine ⟨coeff v f, mem_support_iff.mp vin, ?_⟩
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [suslinMonic_leadingCoeff_finSuccEquiv_t] at coeff
  simp only [coeff, algebraMap_eq]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_T_leadingCoeff_eq_C

end equivT

/-- **Nagata's change of variables over an integral domain.**  Every nonzero
`g ∈ R[s_0,…,s_{n-1}][X]` is sent by some ring automorphism of `R[s_0,…,s_{n-1}][X]` to a
polynomial whose leading coefficient in `X` is a nonzero constant. -/
theorem suslinMonic_nagata (g : Polynomial (MvPolynomial (Fin n) R)) (hg : g ≠ 0) :
    ∃ φ : Polynomial (MvPolynomial (Fin n) R) ≃+* Polynomial (MvPolynomial (Fin n) R),
      ∃ a : R, a ≠ 0 ∧ (φ g).leadingCoeff = MvPolynomial.C a := by
  have hf : (finSuccEquiv R n).symm g ≠ 0 := by
    intro h
    exact hg (by simpa using congrArg (finSuccEquiv R n) h)
  obtain ⟨a, ha, hlc⟩ := suslinMonic_T_leadingCoeff_eq_C _ hf
  exact ⟨(((finSuccEquiv R n).symm.trans (suslinMonic_T ((finSuccEquiv R n).symm g))).trans
    (finSuccEquiv R n)).toRingEquiv, a, ha, hlc⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_nagata

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

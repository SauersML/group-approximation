import GroupApproximation.BooneHigman.Metabelian.SuslinKillLift
import GroupApproximation.BooneHigman.Metabelian.SuslinKillPhi
import GroupApproximation.BooneHigman.Metabelian.SuslinKillMonic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 6: the monic property of `R[x_0, …, x_{n-1}][X]`, by induction on `n`

Lane `bh-met-91t`.  `R` a PID domain, `A_n = R[x_0, …, x_{n-1}]` (a UFD).  `M(n)`: every ideal
`J ⊆ A_n[X]` lying in no principal prime contains an element that is monic after a ring
automorphism of `A_n[X]`.

* `M(0)`: `A_0 ≅ R` is a PID; `lc(J)` is nonzero and lies in no principal prime
  (`suslinKill_lc_avoid`), so `1 ∈ lc(J)`, i.e. `J` contains a monic polynomial.
* `M(n) → M(n+1)`: `I = lc(J) ⊆ A_{n+1}` lies in no principal prime, hence neither does its
  image `I'` in `A_n[x_0]` (via `fse = finSuccEquiv`).  `M(n)` gives `φ` and `q ∈ I'` with
  `φ q` monic in `x_0`; let `g ∈ J` have `lc g = fse⁻¹ q`.  With `ψ = fse⁻¹ ∘ φ ∘ fse`,
  `g' = ψ(g)` has `lc g' = fse⁻¹ (φ q)`, so `ρ (lc g')` is monic in `X`.  For `N` beyond all
  `deg ρ(g'_i)`, `Φ_N g' = g'.eval₂ ρ (X^N + x_0)` is monic (`suslinKill_monic_eval₂`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- `M(n)`: the monic-after-automorphism property of `R[x_0, …, x_{n-1}][X]`. -/
def suslinKill_M (R : Type*) [CommRing R] (n : ℕ) : Prop :=
  ∀ J : Ideal (Polynomial (MvPolynomial (Fin n) R)),
    (∀ π : Polynomial (MvPolynomial (Fin n) R), Prime π → ¬J ≤ Ideal.span {π}) →
      ∃ φ : Polynomial (MvPolynomial (Fin n) R) ≃+* Polynomial (MvPolynomial (Fin n) R),
        ∃ q ∈ J, (φ q).Monic

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_M

/-- An ideal of `C[X]` in no principal prime has a nonzero leading-coefficient ideal. -/
theorem suslinKill_lc_ne_bot {C : Type*} [CommRing C] [IsDomain C] (J : Ideal (Polynomial C))
    (hJ : ∀ π : Polynomial C, Prime π → ¬J ≤ Ideal.span {π}) : J.leadingCoeff ≠ ⊥ := by
  obtain ⟨g, hgJ, hg⟩ := SetLike.not_le_iff_exists.1 (hJ _ Polynomial.prime_X)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (Ideal.zero_mem _)
  intro h
  have hmem : g.leadingCoeff ∈ J.leadingCoeff := (Ideal.mem_leadingCoeff _ _).2 ⟨g, hgJ, rfl⟩
  rw [h, Ideal.mem_bot, Polynomial.leadingCoeff_eq_zero] at hmem
  exact hg0 hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_lc_ne_bot

/-- **Base case** `M(0)`. -/
theorem suslinKill_M_zero (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    suslinKill_M R 0 := by
  haveI : IsPrincipalIdealRing (MvPolynomial (Fin 0) R) :=
    IsPrincipalIdealRing.of_surjective (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.surjective
  intro J hJ
  have h1 := suslinKill_one_mem _ (suslinKill_lc_ne_bot J hJ) (suslinKill_lc_avoid J hJ)
  obtain ⟨q, hqJ, hq⟩ := (Ideal.mem_leadingCoeff _ _).1 h1
  exact ⟨RingEquiv.refl _, q, hqJ, hq⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_M_zero

/-- **Inductive step** `M(n) → M(n+1)`. -/
theorem suslinKill_M_succ (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (n : ℕ) (ih : suslinKill_M R n) : suslinKill_M R (n + 1) := by
  intro J hJ
  obtain ⟨φ, q, hq, hqm⟩ := ih _
    (suslinKill_comap_avoid (MvPolynomial.finSuccEquiv R n).toRingEquiv
      (suslinKill_lc_avoid J hJ))
  rw [Ideal.mem_comap, Ideal.mem_leadingCoeff] at hq
  obtain ⟨g, hgJ, hglc⟩ := hq
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Fin (n + 1)) R ≃+* MvPolynomial (Fin (n + 1)) R,
      ψ g.leadingCoeff = (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm (φ q) := by
    refine ⟨(MvPolynomial.finSuccEquiv R n).toRingEquiv.trans
      (φ.trans (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm), ?_⟩
    rw [hglc, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  have hs : ∀ x, (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm x =
      (MvPolynomial.finSuccEquiv R n).symm x := fun _ ↦ rfl
  have hinj : Function.Injective
      (ψ : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1)) R) := by
    rw [RingEquiv.coe_toRingHom]
    exact ψ.injective
  obtain ⟨g', hg'⟩ : ∃ g' : Polynomial (MvPolynomial (Fin (n + 1)) R),
      g' = g.map (ψ : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1)) R) :=
    ⟨_, rfl⟩
  have hlc : (suslinKill_rho R n g'.leadingCoeff).Monic := by
    rw [hg', Polynomial.leadingCoeff_map_of_injective hinj, RingEquiv.coe_toRingHom, hψ, hs,
      suslinKill_rho_symm]
    exact hqm.map _
  obtain ⟨N, hN⟩ : ∃ N, N = 1 + ∑ i ∈ Finset.range g'.natDegree,
      (suslinKill_rho R n (g'.coeff i)).natDegree := ⟨_, rfl⟩
  have hlow : ∀ i < g'.natDegree, (suslinKill_rho R n (g'.coeff i)).natDegree < N := by
    intro i hi
    have h : (suslinKill_rho R n (g'.coeff i)).natDegree ≤ ∑ j ∈ Finset.range g'.natDegree,
        (suslinKill_rho R n (g'.coeff j)).natDegree :=
      Finset.single_le_sum (f := fun j ↦ (suslinKill_rho R n (g'.coeff j)).natDegree)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.2 hi)
    omega
  have key : (suslinKill_phiEquiv R n N g').Monic := by
    rw [suslinKill_phiEquiv_apply]
    exact suslinKill_monic_eval₂ (suslinKill_rho R n) (MvPolynomial.X 0) N (by omega) g' hlc
      hlow
  refine ⟨(Polynomial.mapEquiv ψ).trans (suslinKill_phiEquiv R n N), g, hgJ, ?_⟩
  show (suslinKill_phiEquiv R n N (g.map
    (ψ : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1)) R))).Monic
  rw [← hg']
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_M_succ

/-- `M(n)` for every `n`, over any PID domain `R`. -/
theorem suslinKill_M_all (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    ∀ n, suslinKill_M R n := by
  intro n
  induction n with
  | zero => exact suslinKill_M_zero R
  | succ n ih => exact suslinKill_M_succ R n ih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_M_all

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

import GroupApproximation.BooneHigman.Metabelian.SuslinCongVacTrace
import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: the vacuity target for `SuslinCongLocPowStab`

Lane `bh-met-92a`.

* `SuslinCongVacIncl A` (**the lane target, as a Statement**): for every maximal `𝔪 ⊂ A` there is
  `N` such that EVERY `σ ∈ SL₂(A[X])` with `σ(0) = 1` and `σ ≡ 1 mod 𝔪^N` has localized image
  `σ_𝔪 ∈ SuslinCongLocGen A A_𝔪[X]`.  This says the extra premise `σ_𝔪 ∉ SuslinCongLocGen` of
  `SuslinCongLocPowStab A` is contradictory.
* `suslinCongVac_locPowStab_of_incl`: `SuslinCongVacIncl A → SuslinCongLocPowStab A` (vacuous).
* `SuslinCongVacGlobalStatement`, `suslinCongVac_locGlobal_of_global`,
  `suslinCongVac_indBase_of_global`: the two families, down to `SuslinR2IndBaseStatement`.

**LOUD status.**
* `SuslinCongVacIncl` is STRONGER than `SuslinCongLocPowStab` (it implies it; the converse is
  not known), and its TRUTH IS UNKNOWN to this lane.  It is NOT proved here, and it does not
  use `SL₃ = E₃`.
* PROVED partial inclusions (`SuslinCongVacRankOne`, `SuslinCongVacTrace`), for `A` a UFD (both
  families; `ℤ[1/m]` for `m ≠ 0`): `σ_𝔪 ∈ SuslinCongLocGen` as soon as `tr σ_𝔪 = 2`, or
  `a + d + b r = 2`, or `a + d + c r = 2` for some `r ∈ A_𝔪[X]`, where `σ_𝔪 = [[a, b], [c, d]]`.
  Also every element of the normal closure of the trace-2 elements of `SL₂` lies in it.  These are
  partial only: they do NOT make the premise contradictory.
* `k = 1` (`A = 𝔽_p[t]`): every ring map `ψ : 𝔽_p[t] → S` lands in `𝔽_p[f]`, and
  `SL₂(𝔽_p[f]) = E₂(𝔽_p[f])` (Euclidean), so the `ψ`-part of `SuslinCongLocGen` adds nothing.
  Over `A/𝔪^N`, a matrix `≡ 1 mod 𝔪` has unit `(1,1)` entry, so `SL₂((A/𝔪^N)[X]) = E₂`.  Lifting
  that `E₂` factorization shows that the target at `k = 1` is equivalent to "`SL₂(A[X])` maps into
  the `GL₂(A_𝔪[X])`-normal closure of `E₂(A_𝔪[X])` and the unipotents".  POSSIBLE OBSTRUCTION
  (not verified here): for the global ring `k[t, X]` the analogous normal closure is known to
  have infinite index in `SL₂`, via actions on trees where all these generators are elliptic.
  Whether localizing at `𝔪` kills this obstruction is unknown here.
* Truth check (sympy, `vac/core.py`, `vac/trace.py` in the lane scratchpad):
  * The gcd factorization behind `suslinCongVac_core` succeeded on 40 of 40 random nilpotent
    `2 × 2` matrices over `ℤ[x, y]`.
  * Over `𝔽_3[t, X]`, `N = 1`, a product of two random normalized congruence rank-one
    unipotents admits a one-step trace adjustment `E₁₂(s)E₂₁(r)` (`s` a monomial) in only 4 of 15
    trials.  So one-step trace adjustment does NOT decide the target, and multi-step E₂
    factorizations would be needed.
  * No counterexample to the target was found.  None was expected from these samples, since
    they are in `SuslinCongLocGen` by construction.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The vacuity target**: every normalized deep-congruence `σ ∈ SL₂(A[X])` has localized image
in `SuslinCongLocGen A A_𝔪[X]`.  STRONGER than `SuslinCongLocPowStab A`; truth unknown. -/
def SuslinCongVacIncl (A : Type*) [CommRing A] : Prop :=
  ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), ∃ N : ℕ,
    ∀ σ : Matrix.GeneralLinearGroup (Fin 2) (Polynomial A),
      Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial A)) = 1 →
        elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A)) σ = 1 →
          elementaryMatrixUnitMap (ι := Fin 2)
              (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ = 1 →
            elementaryMatrixUnitMap (ι := Fin 2)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∈
              SuslinCongLocGen A (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinCongVacIncl

/-- **The vacuity reduction**: the target makes the premise of `SuslinCongLocPowStab`
contradictory. -/
theorem suslinCongVac_locPowStab_of_incl {A : Type*} [CommRing A] (h : SuslinCongVacIncl A) :
    SuslinCongLocPowStab A := by
  intro 𝔪 h𝔪
  obtain ⟨N, hN⟩ := h 𝔪 h𝔪
  exact ⟨N, fun σ hdet h0 hπ hσ ↦ absurd (hN σ hdet h0 hπ) hσ⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_locPowStab_of_incl

/-- **The vacuity target for the two families** (same shape as `SuslinCongLocGlobalStatement`;
the level-`k` family hypothesis is kept for uniformity but is not needed by the reduction). -/
def SuslinCongVacGlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') →
        SuslinCongVacIncl (Chain.CharPPoly p k)) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') →
        SuslinCongVacIncl (Chain.SIntPoly m k)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinCongVacGlobalStatement

/-- The vacuity target gives the residual `SuslinCongLocGlobalStatement`. -/
theorem suslinCongVac_locGlobal_of_global (h : SuslinCongVacGlobalStatement) :
    SuslinCongLocGlobalStatement :=
  ⟨fun p _ k hk hA ↦ suslinCongVac_locPowStab_of_incl (h.1 p k hk hA),
    fun m k hA ↦ suslinCongVac_locPowStab_of_incl (h.2 m k hA)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_locGlobal_of_global

/-- The vacuity target gives the rank-3 base of R2. -/
theorem suslinCongVac_indBase_of_global (h : SuslinCongVacGlobalStatement) :
    SuslinR2IndBaseStatement :=
  suslinCongLoc_indBase_of_locGlobal (suslinCongVac_locGlobal_of_global h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_indBase_of_global

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

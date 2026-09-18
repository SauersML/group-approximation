import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocGen
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: the residual outside the local normal-closure class

Lane `bh-met-91u`.

* `SuslinCongLocPowStab A`: `SuslinBase3CongPowStab A 2` with the extra premise that the
  localized image `σ_𝔪 ∈ GL₂(A_𝔪[X])` is NOT in `SuslinCongLocGen A A_𝔪[X]` (the normal
  closure in `GL₂(A_𝔪[X])` of `E₂(A_𝔪[X])`, the rank-one unipotents `1 + x yᵀ` with
  `y ⬝ᵥ x = 0`, and all `ψ(SL₂(A))`, `ψ : A →+* A_𝔪[X]`).
* `suslinCongLoc_powStab_of_locPowStab` (**the reduction**): given `SL₃(A) = E₃(A)` (the family
  hypothesis at level `k`, NOT `k + 1`), `SuslinCongLocPowStab A → SuslinBase3CongPowStab A 2`.
  It uses `suslinCongLoc_gen_le` (Suslin normality of `E₃`, proved in the repo, plus the
  rank-one lemma `suslinNormal_inE_of_dot_zero`, proved in the repo).
* `suslinCongLoc_locPowStab_of_famPowStab`: the residual of lane `bh-met-91p`
  (`SuslinBase3FamPowStab A`) implies this one, since `SuslinBase3FamGen A` maps into
  `SuslinCongLocGen` (`suslinCongLoc_famGen_le`).
* `suslinCongLoc_locPowStab_of_powStab`: the trivial converse.

**LOUD status.**  Over a ring with `SL₃ = E₃` this residual is EQUIVALENT to
`SuslinBase3CongPowStab A 2` (and to `SuslinBase3FamPowStab A`).  It is NOT logically weaker on
the families; it is strictly smaller in PROOF CONTENT than `SuslinBase3FamPowStab`: besides the
images of `SuslinBase3FamGen A` it discharges all of `E₂(A_𝔪[X])` (not only the image of
`E₂(A[X])`), all rank-one unipotents, all `ψ(SL₂(A))` for ring maps `ψ : A → A_𝔪[X]` not
factoring through `A[X]`, and the full `GL₂(A_𝔪[X])`-normal closure of these.

Truth check (sympy): for `A = 𝔽_p[t]` (`k = 1`), `𝔪 = (t)`, `x = (X, -1)`, `y = t^N X (1, X)`,
`σ = 1 + x yᵀ = [[1 + t^N X², t^N X³], [-t^N X, 1 - t^N X²]]` has `det σ = 1`, `σ(0) = 1`,
`σ ≡ 1 mod 𝔪^N` and is rank-one unipotent, so it is discharged here.  For `k = 1`,
`SL₂(𝔽_p[t]) = E₂(𝔽_p[t])` (Euclidean), so `SuslinBase3FamGen A = E₂(A[X])`; whether this `σ`
lies in `E₂(A[X])` is NOT claimed (it is of Cohn type).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual**: the deep-congruence core at rank `2`, only for `σ` whose localized image
is outside `SuslinCongLocGen A A_𝔪[X]`. -/
def SuslinCongLocPowStab (A : Type*) [CommRing A] : Prop :=
  ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), ∃ N : ℕ,
    ∀ σ : Matrix.GeneralLinearGroup (Fin 2) (Polynomial A),
      Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial A)) = 1 →
        elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A)) σ = 1 →
          elementaryMatrixUnitMap (ι := Fin 2)
              (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ = 1 →
            elementaryMatrixUnitMap (ι := Fin 2)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∉
              SuslinCongLocGen A (Polynomial (Localization.AtPrime 𝔪)) →
              stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
                  (elementaryMatrixUnitMap (ι := Fin 2)
                    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ) ∈
                elementaryGroup (Fin 2 ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinCongLocPowStab

/-- **The reduction**: with `SL₃(A) = E₃(A)`, the residual gives the congruence core. -/
theorem suslinCongLoc_powStab_of_locPowStab {A : Type*} [CommRing A]
    (hSL : SpecialLinearInElementary A (2 + 1)) (h : SuslinCongLocPowStab A) :
    SuslinBase3CongPowStab A 2 := by
  intro 𝔪 h𝔪
  obtain ⟨N, hN⟩ := h 𝔪 h𝔪
  refine ⟨N, fun σ hdet h0 hπ ↦ ?_⟩
  by_cases hσ : elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∈
    SuslinCongLocGen A (Polynomial (Localization.AtPrime 𝔪))
  · exact Subgroup.mem_comap.mp (suslinCongLoc_gen_le hSL hσ)
  · exact hN σ hdet h0 hπ hσ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_powStab_of_locPowStab

/-- The residual of lane `bh-met-91p` implies this residual (no hypothesis on `A`). -/
theorem suslinCongLoc_locPowStab_of_famPowStab {A : Type*} [CommRing A]
    (h : SuslinBase3FamPowStab A) : SuslinCongLocPowStab A := by
  intro 𝔪 h𝔪
  obtain ⟨N, hN⟩ := h 𝔪 h𝔪
  refine ⟨N, fun σ hdet h0 hπ hσ ↦ hN σ hdet h0 hπ fun hfam ↦ hσ ?_⟩
  exact Subgroup.mem_comap.mp (suslinCongLoc_famGen_le
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) hfam)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_locPowStab_of_famPowStab

/-- The trivial converse (LOUD: equivalence over rings with `SL₃ = E₃`). -/
theorem suslinCongLoc_locPowStab_of_powStab {A : Type*} [CommRing A]
    (h : SuslinBase3CongPowStab A 2) : SuslinCongLocPowStab A :=
  fun 𝔪 h𝔪 ↦ (h 𝔪 h𝔪).imp fun _ hN σ hdet h0 hπ _ ↦ hN σ hdet h0 hπ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongLoc_locPowStab_of_powStab

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

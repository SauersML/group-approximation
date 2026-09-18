import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowWitness
import GroupApproximation.Meta.AxiomGuard

/-!
# The deep-congruence residual outside the Mennicke-closed class

Lane `bh-met-92r`.

* `suslinCongPow_Statement A`: `SuslinCongLocPowStab A` with ONE extra premise, that the
  localized image `σ_𝔪 ∈ GL₂(A_𝔪[X])` is NOT in `suslinCongPow_gen A_𝔪[X]` (the smallest
  normal, Mennicke-closed subgroup containing `E₂(A_𝔪[X])` and the rank-one unipotents).
* `suslinCongPow_locPowStab_of_statement` (**the reduction**, no hypothesis on `A`):
  `suslinCongPow_Statement A → SuslinCongLocPowStab A`.  The discharged case is
  `suslinCongPow_gen_le`, which rests on the rank-3 Mennicke identity
  `suslinCongPow_mennicke_eq` (proved here over every commutative ring).
* `suslinCongPow_congPowStab_of_statement`: with `SL₃(A) = E₃(A)`, the residual gives
  `SuslinBase3CongPowStab A 2` (through `suslinCongLoc_powStab_of_locPowStab`).
* `suslinCongPow_statement_of_locPowStab`: the trivial converse.

**LOUD status.**
1. The full target `SuslinCongLocPowStab A` for `Chain.CharPPoly p k` and `ℤ[1/m][t]` is NOT
   proved.  Its conclusion, `diag(σ_𝔪, 1) ∈ E₃(A_𝔪[X])` for `det σ = 1`, is an `SK₁`
   statement for the polynomial ring over the regular local ring `A_𝔪`.  All the known proofs
   go through `NK₁`-vanishing, i.e. homotopy invariance, which this lane is forbidden to use.
   Over a general (non-regular) local ring the analogous statement is FALSE, since `NK₁ ≠ 0`
   for the cusp, so no argument that uses only "local" can close it.  The monic-row lemma
   alone does not suffice either.
2. The residual is logically EQUIVALENT to `SuslinCongLocPowStab A`, for every `A`: both
   directions are proved here without hypotheses.  It is NOT logically weaker.  It is
   strictly smaller in PROOF CONTENT.  On top of what `SuslinCongLocPowStab` already
   discharges, it also discharges the Mennicke closure.  That closure contains:
   * every Cohn-type matrix `[[1 + t y, y²], [-t², 1 - t y]]`;
   * every Krstić–McCool-type matrix `h_{q,k}` and its images (`suslinCongPow_map_km_mem`);
   * the witnesses `σ_{q,k}` (`suslinCongPow_map_wit_mem_gen`).

   These witnesses are exactly the family that the repo's own (unproved, literature-backed)
   `suslinCongDecide_KMStatement` places OUTSIDE the unipotent class.  This file does not
   use that statement.
3. Truth: TRUE iff `SuslinCongLocPowStab A` is true, which holds for the regular families by
   the classical theory.  No such input is used.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The residual**: `SuslinCongLocPowStab A`, only for `σ` whose localized image is outside
the Mennicke-closed class `suslinCongPow_gen A_𝔪[X]`. -/
def suslinCongPow_Statement (A : Type*) [CommRing A] : Prop :=
  ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), ∃ N : ℕ,
    ∀ σ : Matrix.GeneralLinearGroup (Fin 2) (Polynomial A),
      Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial A)) = 1 →
        elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A)) σ = 1 →
          elementaryMatrixUnitMap (ι := Fin 2)
              (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ = 1 →
            elementaryMatrixUnitMap (ι := Fin 2)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∉
              SuslinCongLocGen A (Polynomial (Localization.AtPrime 𝔪)) →
              elementaryMatrixUnitMap (ι := Fin 2)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∉
                suslinCongPow_gen (Polynomial (Localization.AtPrime 𝔪)) →
                stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
                    (elementaryMatrixUnitMap (ι := Fin 2)
                      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ) ∈
                  elementaryGroup (Fin 2 ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_Statement

/-- **The reduction** (no hypothesis on `A`). -/
theorem suslinCongPow_locPowStab_of_statement {A : Type*} [CommRing A]
    (h : suslinCongPow_Statement A) : SuslinCongLocPowStab A := by
  intro 𝔪 h𝔪
  obtain ⟨N, hN⟩ := h 𝔪 h𝔪
  refine ⟨N, fun σ hdet h0 hπ hloc ↦ ?_⟩
  by_cases hg : elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∈
    suslinCongPow_gen (Polynomial (Localization.AtPrime 𝔪))
  · exact Subgroup.mem_comap.mp (suslinCongPow_gen_le _ hg)
  · exact hN σ hdet h0 hπ hloc hg

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_locPowStab_of_statement

/-- With `SL₃(A) = E₃(A)`, the residual gives the rank-2 congruence core. -/
theorem suslinCongPow_congPowStab_of_statement {A : Type*} [CommRing A]
    (hSL : SpecialLinearInElementary A (2 + 1)) (h : suslinCongPow_Statement A) :
    SuslinBase3CongPowStab A 2 :=
  suslinCongLoc_powStab_of_locPowStab hSL (suslinCongPow_locPowStab_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_congPowStab_of_statement

/-- The trivial converse (LOUD: the residual is logically equivalent to
`SuslinCongLocPowStab A`; it is smaller only in proof content). -/
theorem suslinCongPow_statement_of_locPowStab {A : Type*} [CommRing A]
    (h : SuslinCongLocPowStab A) : suslinCongPow_Statement A :=
  fun 𝔪 h𝔪 ↦ (h 𝔪 h𝔪).imp fun _ hN σ hdet h0 hπ hloc _ ↦ hN σ hdet h0 hπ hloc

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_statement_of_locPowStab

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

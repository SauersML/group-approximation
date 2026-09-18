import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, R1/R2 split: the two conjuncts of the split Statement

Lane `bh-met-90j`.  `SuslinHorrocksSplitLocal A N` (`SuslinHorrocksStatement.lean`) is, for each
normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, the conjunction of
* (R1) *monic production*: some `τ_𝔪 F`, with `F ∈ E_N(A_𝔪[X])`, has a monic entry
  (`SuslinR1MonicLocal`);
* (R2) *stabilizer step*: if a row `r` of some `τ_𝔪 F`, with `F ∈ E_N(A_𝔪[X])`, is `e_r`, then
  `τ_𝔪 ∈ E_N(A_𝔪[X])` (`SuslinR1StabLocal`).

This file states the two conjuncts separately, for the two coefficient families
(`SuslinHorrocksR1Statement`, `SuslinHorrocksR2Statement`), and proves that together they give
the split Statement (`suslinR1_split_of_R1_R2`), hence the gap `SuslinLocalHorrocksStatement`
(`suslinR1_localHorrocks_of_R1_R2`).  The split is a pure conjunction split: both directions are
definitional, and each of `R1`, `R2` is implied by the split Statement.

**Truth check.**  Both are TRUE for the families, since they follow from the local case
(`SuslinLocalCaseFamilyStatement`, true by Suslin's theorem, A. A. Suslin 1977): take
`F = τ_𝔪⁻¹` for R1, and R2 holds trivially.  As for the local case, both are only asserted for
the families.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **(R1) monic production**: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, some `τ_𝔪 F`,
with `F` elementary over `A_𝔪[X]`, has a monic entry. -/
def SuslinR1MonicLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          ∃ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∃ r t : Fin N,
            (((elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
                  (Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪)))ˣ) :
                Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r t).Monic

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1MonicLocal

/-- **(R2) stabilizer step**: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, if row `r` of some
`τ_𝔪 F`, with `F` elementary over `A_𝔪[X]`, is `e_r`, then `τ_𝔪` is elementary. -/
def SuslinR1StabLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          ∀ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∀ r : Fin N,
            (∀ c : Fin N, ((elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
                  (Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪)))ˣ) :
                Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r c =
                  if c = r then 1 else 0) →
              elementaryMatrixUnitMap (ι := Fin N)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
                elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1StabLocal

/-- R1 and R2 together are the split Statement. -/
theorem suslinR1_splitLocal_of_monic_stab {A : Type*} [CommRing A] {N : ℕ}
    (h1 : SuslinR1MonicLocal A N) (h2 : SuslinR1StabLocal A N) :
    SuslinHorrocksSplitLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  exact ⟨h1 τ hdet h0 𝔪 h𝔪, h2 τ hdet h0 𝔪 h𝔪⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_splitLocal_of_monic_stab

/-- The split Statement gives R1. -/
theorem suslinR1_monic_of_splitLocal {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinHorrocksSplitLocal A N) : SuslinR1MonicLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  exact (h τ hdet h0 𝔪 h𝔪).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_monic_of_splitLocal

/-- The split Statement gives R2. -/
theorem suslinR1_stab_of_splitLocal {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinHorrocksSplitLocal A N) : SuslinR1StabLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  exact (h τ hdet h0 𝔪 h𝔪).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_stab_of_splitLocal

/-- **The family R1 Statement**: `SuslinR1MonicLocal` for the two coefficient families, under
the hypotheses of `SuslinHorrocksSplitStatement`. -/
def SuslinHorrocksR1Statement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinR1MonicLocal (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinR1MonicLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinHorrocksR1Statement

/-- **The family R2 Statement**: `SuslinR1StabLocal` for the two coefficient families, under
the hypotheses of `SuslinHorrocksSplitStatement`. -/
def SuslinHorrocksR2Statement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinR1StabLocal (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinR1StabLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinHorrocksR2Statement

/-- **R1 and R2 give the split Statement.** -/
theorem suslinR1_split_of_R1_R2 (h1 : SuslinHorrocksR1Statement)
    (h2 : SuslinHorrocksR2Statement) : SuslinHorrocksSplitStatement :=
  ⟨fun p _ k N hk hA hN ↦
      suslinR1_splitLocal_of_monic_stab (h1.1 p k N hk hA hN) (h2.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR1_splitLocal_of_monic_stab (h1.2 m k N hA hN) (h2.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_split_of_R1_R2

/-- The converse: the split Statement gives R1. -/
theorem suslinR1_R1_of_split (h : SuslinHorrocksSplitStatement) : SuslinHorrocksR1Statement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR1_monic_of_splitLocal (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR1_monic_of_splitLocal (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_R1_of_split

/-- The converse: the split Statement gives R2. -/
theorem suslinR1_R2_of_split (h : SuslinHorrocksSplitStatement) : SuslinHorrocksR2Statement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR1_stab_of_splitLocal (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR1_stab_of_splitLocal (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_R2_of_split

/-- **The gap from R1 and R2**: `SuslinLocalHorrocksStatement`. -/
theorem suslinR1_localHorrocks_of_R1_R2 (h1 : SuslinHorrocksR1Statement)
    (h2 : SuslinHorrocksR2Statement) : SuslinLocalHorrocksStatement :=
  suslinHorrocks_localHorrocks_of_split (suslinR1_split_of_R1_R2 h1 h2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_localHorrocks_of_R1_R2

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

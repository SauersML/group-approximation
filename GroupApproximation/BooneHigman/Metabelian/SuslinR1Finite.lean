import GroupApproximation.BooneHigman.Metabelian.SuslinR1Statement
import GroupApproximation.BooneHigman.Metabelian.SuslinR1Columns
import GroupApproximation.Meta.AxiomGuard

/-!
# R1, part 2: R1 from a finiteness Statement

Lane `bh-met-90j`.  R1 (`SuslinR1MonicLocal`, monic production) is reduced to
`SuslinR1FiniteLocal`: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, some `τ_𝔪 F`, with `F`
elementary over `B[X]` (`B = A_𝔪`), has a row `r` and a column `t` such that
`B[X] / (entries of row r outside column t)` is a finite `B`-module.  The reduction
(`suslinR1_monicLocal_of_finite`) proves: finiteness makes the class of `X` integral, so the
ideal contains a monic `p = ∑_{j ≠ t} c_j f_j`; adding `X^n c_j` times column `j` to column `t`
makes the entry at `(r, t)` equal to `f_t + X^n p`, which is monic for large `n`
(`SuslinR1Columns.lean`).

**LOUD: logical strength.**  `SuslinR1FiniteLocal` is logically EQUIVALENT to
`SuslinR1MonicLocal`, not strictly weaker.  Converse on paper (not formalized): if the entry at
`(r, t')` of `τ_𝔪 F` is monic, pick `t ≠ t'` (`N ≥ 3`).  Then the ideal of the entries outside
column `t` contains that monic, so `B[X] / I` is a quotient of `B[X] / (monic)`, which is finite.
What the Statement removes is proof content: the integrality step, the choice of the monic
combination, and its realization by column operations (all proved here).  What is left is the
genuinely hard part of local Horrocks: finding an elementary `F` such that some `N-1` entries of
a row generate an ideal with finite (i.e. integral over `B`) quotient.

**Why `F` cannot be dropped.**  Over `B = k[y]_(y)` take the row
`(f₁, f₂, f₃) = ((1-yX)(1-2yX), yX(1-2yX), yX(1-yX))`, with `char k ≠ 2`.  It is unimodular
(python/sympy Groebner basis `[1]`, for `k = F_3, F_5, F_7`) and equals `(1, 0, 0)` at `X = 0`.
But no pair of its entries generates an ideal containing a monic, since
`(f₂, f₃) ⊆ (yX)`, `(f₁, f₃) ⊆ (1-yX)` and `(f₁, f₂) ⊆ (1-2yX)`, and every nonzero multiple of
`yX`, `1-yX` or `1-2yX` has leading coefficient in `(y)`, hence is not monic.  So the Statement
genuinely needs the elementary factor `F`.

**Truth check.**  TRUE for the families: the local case (`SuslinLocalCaseFamilyStatement`, true
by Suslin's theorem) gives R1 (take `F = τ_𝔪⁻¹`), and R1 gives the finiteness Statement by the
converse above.  Like R1, it is only asserted for the families.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **(R1, finite form)**: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, some `τ_𝔪 F`, with
`F` elementary over `A_𝔪[X]`, has a row `r` and a column `t` such that `A_𝔪[X]` modulo the ideal
of the entries of row `r` outside column `t` is a finite `A_𝔪`-module. -/
def SuslinR1FiniteLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          ∃ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∃ r t : Fin N,
            Module.Finite (Localization.AtPrime 𝔪)
              (Polynomial (Localization.AtPrime 𝔪) ⧸ Ideal.span (Set.range
                fun j : {j : Fin N // j ≠ t} ↦
                  (((elementaryMatrixUnitMap (ι := Fin N)
                    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
                      (Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪)))ˣ) :
                    Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r j)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1FiniteLocal

/-- **The reduction**: the finite form gives R1, in every rank and for every coefficient ring. -/
theorem suslinR1_monicLocal_of_finite {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinR1FiniteLocal A N) : SuslinR1MonicLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨F, hF, r, t, hfin⟩ := h τ hdet h0 𝔪 h𝔪
  obtain ⟨G, hG, hmon⟩ := suslinR1_monic_of_finite _ r t hfin
  refine ⟨F * G, Subgroup.mul_mem _ hF hG, r, t, ?_⟩
  rw [← mul_assoc]
  exact hmon

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_monicLocal_of_finite

/-- **The family finite Statement**: `SuslinR1FiniteLocal` for the two coefficient families,
under the hypotheses of `SuslinHorrocksR1Statement`. -/
def SuslinR1FiniteStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinR1FiniteLocal (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinR1FiniteLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1FiniteStatement

/-- **R1 from the finite Statement.** -/
theorem suslinR1_R1_of_finite (h : SuslinR1FiniteStatement) : SuslinHorrocksR1Statement :=
  ⟨fun p _ k N hk hA hN ↦ suslinR1_monicLocal_of_finite (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinR1_monicLocal_of_finite (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_R1_of_finite

/-- **The gap from the finite Statement and R2**: `SuslinLocalHorrocksStatement`. -/
theorem suslinR1_localHorrocks_of_fin (h1 : SuslinR1FiniteStatement)
    (h2 : SuslinHorrocksR2Statement) : SuslinLocalHorrocksStatement :=
  suslinR1_localHorrocks_of_R1_R2 (suslinR1_R1_of_finite h1) h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1_localHorrocks_of_fin

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

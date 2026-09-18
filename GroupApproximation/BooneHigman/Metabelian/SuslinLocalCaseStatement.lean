import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local case, part 4: the local Statement and clearing denominators

Lane `bh-met-88`.  Target: `SuslinDilationAnalyticLocallyElementary A N`
(`SuslinDilationAnalyticStatement.lean`): for a normalized `τ ∈ SL_N(A[X])` and a maximal
ideal `𝔪` there is `a ∉ 𝔪` with `τ ∈ E_N(A_a[X])`.  Route: (1) the local case over `A_𝔪[X]`,
then (2) clearing denominators from `A_𝔪` to some `A_a`.

**Isolated Statement.**  `SuslinLocalCaseStatement A N`: for normalized `τ ∈ SL_N(A[X])` and a
maximal `𝔪`, the image of `τ` in `GL_N(A_𝔪[X])` is elementary.

* **Step (2), proved in full** (`suslinDilAn_locallyElementary_of_localCase`): via
  `suslinLocalCase_away_of_loc` (`SuslinLocalCaseLift.lean`), which lifts the finitely many
  elementary factors to some `A_b`, `b ∉ 𝔪`, then kills the finitely many entry discrepancies
  over some `A_{b c}` (`suslinLocalCase_eventually_units_eq`).
* **Converse** (`suslinLocalCase_of_locallyElementary`): map `A_a → A_𝔪`.

**LOUD: only EQUIVALENT, not logically weaker.**  Both implications are proved, so
`SuslinLocalCaseStatement A N ↔ SuslinDilationAnalyticLocallyElementary A N` for every `A`, and
`SuslinLocalCaseFamilyStatement ↔ SuslinDilationAnalyticStatement`.  What is strictly removed is
the proof content of step (2), clearing denominators, which is proved here.  What remains open
is step (1) alone: the local case over `A_𝔪[X]`, i.e. local Horrocks / Suslin over a regular
local ring.  It is NOT proved in this lane.

**LOUD: FALSE for general rings.**  For a local ring `R`, `SuslinLocalCaseStatement R N` says
that every normalized `τ ∈ SL_N(R[X])` is elementary.  Together with Suslin's local-global
principle and induction on the number of variables, this would give `SL_N(R[t₁,…,t_p]) = E_N` for
every local `R`.  So every reduced local ring would be `K₁`-regular, hence `K₀`-regular (Vorst),
hence `Pic R[t] = 0`, hence seminormal (Traverso–Swan).  The local cusp
`k[x,y]_{(x,y)}/(y² - x³)` is reduced, local and not seminormal.  So the Statement is only
asserted for the two coefficient families (`SuslinLocalCaseFamilyStatement`).

**Truth check for the families.**  TRUE, by Suslin's theorem (A. A. Suslin, 1977).  For
`A = 𝔽_p[x₁,…,x_k]` or `ℤ[1/m][x₁,…,x_k]` and `N ≥ 3`, `SL_N(A[X]) = E_N(A[X])`, and `E_N` maps
into `E_N`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The local case**: for every normalized `τ ∈ SL_N(A[X])` and maximal ideal `𝔪`, the image
of `τ` in `GL_N(A_𝔪[X])` is elementary. -/
def SuslinLocalCaseStatement (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
          elementaryMatrixUnitMap (ι := Fin N)
              (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
            elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalCaseStatement

/-- **Step (2), clearing denominators**: the local case gives the locally elementary
Statement. -/
theorem suslinDilAn_locallyElementary_of_localCase {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinLocalCaseStatement A N) : SuslinDilationAnalyticLocallyElementary A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨a, ha, hmem⟩ := suslinLocalCase_away_of_loc (Localization.AtPrime 𝔪) 𝔪.primeCompl τ
    (h τ hdet h0 𝔪 h𝔪)
  exact ⟨a, Ideal.mem_primeCompl_iff.1 ha, hmem⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_locallyElementary_of_localCase

/-- The converse: the two Statements are equivalent for every ring. -/
theorem suslinLocalCase_of_locallyElementary {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinDilationAnalyticLocallyElementary A N) : SuslinLocalCaseStatement A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨a, ha, hmem⟩ := h τ hdet h0 𝔪 h𝔪
  have ha' : a ∈ 𝔪.primeCompl := Ideal.mem_primeCompl_iff.2 ha
  have hmap : elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (suslinLocalCase_toLoc (Localization.AtPrime 𝔪) ha'))
        (elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (algebraMap A (Localization.Away a))) τ) ∈
      elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)) :=
    elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ hmem)
  rwa [suslinLocalCase_map_poly_comp, suslinLocalCase_toLoc_comp] at hmap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_of_locallyElementary

/-- The local case gives the generated Quillen Statement in rank `N ≥ 3`. -/
theorem suslinLocalCase_generatedQuillen {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (h : SuslinLocalCaseStatement A N) : SuslinDilationGeneratedQuillen A N :=
  suslinDilAn_generated_of_locallyElementary hN (suslinDilAn_locallyElementary_of_localCase h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_generatedQuillen

/-- **The family Statement**: `SuslinLocalCaseStatement` for the two coefficient families,
under the hypotheses of `SuslinDilationAnalyticStatement`. -/
def SuslinLocalCaseFamilyStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinLocalCaseStatement (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinLocalCaseStatement (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalCaseFamilyStatement

/-- The family Statement gives the localized Statement. -/
theorem suslinLocalCase_analytic_of_family (h : SuslinLocalCaseFamilyStatement) :
    SuslinDilationAnalyticStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinDilAn_locallyElementary_of_localCase (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinDilAn_locallyElementary_of_localCase (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_analytic_of_family

/-- The family Statement gives the generated Statement. -/
theorem suslinLocalCase_generated_of_family (h : SuslinLocalCaseFamilyStatement) :
    SuslinDilationGeneratedStatement :=
  suslinDilationGenerated_of_analytic (suslinLocalCase_analytic_of_family h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_generated_of_family

/-- The converse: the family Statement is equivalent to the localized Statement. -/
theorem suslinLocalCase_family_of_analytic (h : SuslinDilationAnalyticStatement) :
    SuslinLocalCaseFamilyStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinLocalCase_of_locallyElementary (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinLocalCase_of_locallyElementary (h.2 m k N hA hN)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_family_of_analytic

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

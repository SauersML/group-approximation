import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksRow
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, part 4: the split Statement and the reduction to it

Lane `bh-met-90a`.  Target: `SuslinLocalHorrocksStatement` (the gap `hH` of
`Envelope.hmClosed_finitelyPresentedMetabelian_of_six`).  The deepest existing residual is
`SuslinLocalCaseFamilyStatement` (`SuslinLocalCaseStatement.lean`): for normalized
`τ ∈ SL_N(A[X])` and maximal `𝔪`, the image `τ_𝔪` of `τ` in `GL_N(A_𝔪[X])` is elementary.

**Proved outright here (the Horrocks content).**  The local Horrocks theorem in row form,
`suslinHorrocks_row` (`SuslinHorrocksRow.lean`): over a local ring and for `N ≥ 3`, a row of an
invertible matrix over `R[X]` with a monic entry is carried to `e_r` by elementary column
operations.  It holds for every local ring, and the proof uses only Euclidean division.

**Isolated Statement.**  `SuslinHorrocksSplitLocal A N` has two parts, for each normalized `τ`
and maximal `𝔪`:
* (R1) *monic production*: some `τ_𝔪 F`, with `F ∈ E_N(A_𝔪[X])`, has a monic entry;
* (R2) *stabilizer step*: if a row `r` of some `τ_𝔪 F`, with `F ∈ E_N`, is `e_r`, then
  `τ_𝔪 ∈ E_N`.

By local Horrocks, R1 and R2 give the local case (`suslinHorrocks_localCase_of_split`).

**LOUD: only EQUIVALENT, not logically weaker.**  Conversely the local case gives R1 (take
`F = τ_𝔪⁻¹`, so the entry is `1`) and R2 (trivially) once `N ≥ 1`
(`suslinHorrocks_split_of_localCase`).  So `SuslinHorrocksSplitStatement ↔
SuslinLocalCaseFamilyStatement`.  What is strictly removed is the proof content of the Horrocks
step between a monic entry and a basis row, which is proved here for all local rings.  What
remains open is (R1) producing a monic entry (Suslin's change of variables) and (R2) the
stabilizer step (the rank-`N - 1` stable problem: `K₁`-regularity of `A_𝔪`).

**Truth check.**  TRUE for the two families: `SuslinLocalCaseFamilyStatement` holds by Suslin's
theorem (A. A. Suslin, 1977), and it implies the split Statement.  As for
`SuslinLocalCaseStatement`, the split Statement is FALSE for general rings `A` (see the cusp
counterexample in `SuslinLocalCaseStatement.lean`), so it is only asserted for the families.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The split local Statement**: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, (R1) some
`τ_𝔪 F`, with `F` elementary, has a monic entry, and (R2) if some row `r` of some `τ_𝔪 F`, with
`F` elementary, is `e_r`, then `τ_𝔪` is elementary. -/
def SuslinHorrocksSplitLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          (∃ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∃ r t : Fin N,
            (((elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
                  (Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪)))ˣ) :
                Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r t).Monic) ∧
          ∀ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∀ r : Fin N,
            (∀ c : Fin N, ((elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
                  (Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪)))ˣ) :
                Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r c =
                  if c = r then 1 else 0) →
              elementaryMatrixUnitMap (ι := Fin N)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
                elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinHorrocksSplitLocal

/-- **The reduction**: by local Horrocks (`suslinHorrocks_row`), the split Statement gives the
local case in rank `N ≥ 3`. -/
theorem suslinHorrocks_localCase_of_split {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (h : SuslinHorrocksSplitLocal A N) : SuslinLocalCaseStatement A N := by
  intro τ hdet h0 𝔪 h𝔪
  obtain ⟨⟨F, hF, r, t, ht⟩, hstab⟩ := h τ hdet h0 𝔪 h𝔪
  obtain ⟨F2, hF2, hrow⟩ := suslinHorrocks_row (by rw [Fintype.card_fin]; exact hN) _ r t ht
  refine hstab (F * F2) (Subgroup.mul_mem _ hF hF2) r fun c ↦ ?_
  rw [← mul_assoc]
  exact hrow c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_localCase_of_split

/-- The converse: the local case gives the split Statement in rank `N ≥ 1`. -/
theorem suslinHorrocks_split_of_localCase {A : Type*} [CommRing A] {N : ℕ} (hN : 1 ≤ N)
    (h : SuslinLocalCaseStatement A N) : SuslinHorrocksSplitLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  have hmem := h τ hdet h0 𝔪 h𝔪
  refine ⟨⟨_, inv_mem hmem, ⟨0, by omega⟩, ⟨0, by omega⟩, ?_⟩, fun _ _ _ _ ↦ hmem⟩
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  exact Polynomial.monic_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_split_of_localCase

/-- **The family split Statement**: `SuslinHorrocksSplitLocal` for the two coefficient
families, under the hypotheses of `SuslinLocalCaseFamilyStatement`. -/
def SuslinHorrocksSplitStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SuslinHorrocksSplitLocal (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SuslinHorrocksSplitLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinHorrocksSplitStatement

/-- The family split Statement gives the family local case. -/
theorem suslinHorrocks_localCaseFamily_of_split (h : SuslinHorrocksSplitStatement) :
    SuslinLocalCaseFamilyStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinHorrocks_localCase_of_split hN (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinHorrocks_localCase_of_split hN (h.2 m k N hA hN)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_localCaseFamily_of_split

/-- The converse: the two family Statements are equivalent. -/
theorem suslinHorrocks_split_of_localCaseFamily (h : SuslinLocalCaseFamilyStatement) :
    SuslinHorrocksSplitStatement :=
  ⟨fun p _ k N hk hA hN ↦ suslinHorrocks_split_of_localCase (by omega) (h.1 p k N hk hA hN),
    fun m k N hA hN ↦ suslinHorrocks_split_of_localCase (by omega) (h.2 m k N hA hN)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_split_of_localCaseFamily

/-- **The target from the split Statement**: `SuslinLocalHorrocksStatement`. -/
theorem suslinHorrocks_localHorrocks_of_split (h : SuslinHorrocksSplitStatement) :
    SuslinLocalHorrocksStatement :=
  suslinLocalHorrocks_of_dilationGenerated
    (suslinLocalCase_generated_of_family (suslinHorrocks_localCaseFamily_of_split h))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_localHorrocks_of_split

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

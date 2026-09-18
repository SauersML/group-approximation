import GroupApproximation.BooneHigman.Metabelian.SuslinR1Statement
import GroupApproximation.BooneHigman.Metabelian.SuslinR2Core
import GroupApproximation.Meta.AxiomGuard

/-!
# Stabilizer step (R2), part 3: reduction of R2 to the normalized coordinate-block case

Lane `bh-met-90k`.  Target: `SuslinHorrocksR2Statement`, R2 alone for the two families.  It
is already defined by lane `bh-met-90j` (`SuslinR1Statement.lean`, via `SuslinR1StabLocal`),
and is imported, not redefined.

**Isolated Statement.**  `SuslinR2BlockLocal A N`: for normalized `τ ∈ SL_N(A[X])`, maximal
`𝔪`, `F ∈ E_N(A_𝔪[X])` and `r`, if `τ_𝔪 F` lies in `coordinateBlock (A_𝔪[X]) r` (row and
column `r` are those of the identity, i.e. `τ_𝔪 F = diag(σ, 1)` up to reindexing) and
`(τ_𝔪 F)(0) = 1`, then `τ_𝔪 ∈ E_N(A_𝔪[X])`.

**Reduction, proved here** (`suslinR2_stabLocal_of_blockLocal`).  R2 gives only that row `r` of
`τ_𝔪 F` is `e_r`.  Column `r` is cleared by elementary right factors, and the value at `X = 0`
is normalized by a constant elementary factor (`suslinR2_block_core`).

**LOUD: logically EQUIVALENT, not weaker.**  A normalized block has row `r` equal to `e_r`,
so R2 implies the block form trivially (`suslinR2_blockLocal_of_stabLocal`).  What is
strictly removed is proof content: the column clearing and the normalization at `X = 0`.  What
remains is the heart of R2: `diag(σ, 1) ∈ E_N(A_𝔪[X])` for `σ ∈ SL_{N-1}(A_𝔪[X])` with
`σ(0) = 1`, of the special form `σ ⊕ 1 = τ_𝔪 F`.  That is the stable `K₁`-regularity of
`A_𝔪`.

**LOUD: the suggested rank induction ("R2 at rank `N` from SplitLocal at rank `N - 1`") is NOT
provable as stated.**
* Type mismatch.  `SuslinHorrocksSplitLocal A (N - 1)` concerns images `τ'_𝔪` of matrices `τ'`
  over `A[X]`.  The block `σ` of `τ_𝔪 F` lives over `A_𝔪[X]` and is in general not the image
  of a matrix over `A[X]`.  The families `CharPPoly`, `SIntPoly` are not closed under
  localization, so the rank-`(N - 1)` Statement cannot be applied to `A_𝔪` either.
* False base case.  For `N = 3` the induction lands in rank `2`.  There the conclusion
  `τ_𝔪 ∈ E_2` fails: the normalized Cohn matrix is not in `E_2(B[X])` for any domain `B` that
  is not a field, e.g. `B = F_p[t]_{(t)}`.  The rank-`2` local case is FALSE for the families,
  so no induction can start there.  The `N ≥ 3` constraint of `suslinHorrocks_row` is exactly
  what excludes it.
* The τ-free stable variant, "every `σ ⊕ 1` with `σ(0) = 1` over `A_𝔪[X]` is in
  `E_N(A_𝔪[X])`", is a `K₁`-regularity/stability theorem (Vorst-type in characteristic `p`,
  with a mixed-characteristic analogue for `ℤ[1/m]`).  It is logically STRONGER than the block
  Statement and is NOT asserted here.

**Truth check.**  `SuslinR2BlockLocal` follows from the local case
(`suslinR2_blockLocal_of_localCase`), so the family version is TRUE by Suslin's theorem.  Like
the local case it is FALSE for general `A` (cusp counterexample), so it is only asserted for
the families (`SuslinR2Family.lean`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **R2 in normalized block form**: for normalized `τ ∈ SL_N(A[X])` and maximal `𝔪`, if
`τ_𝔪 F`, with `F` elementary, is a coordinate block at `r` with value `1` at `X = 0`, then
`τ_𝔪` is elementary. -/
def SuslinR2BlockLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          ∀ F ∈ elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)), ∀ r : Fin N,
            elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F ∈
              coordinateBlock (Polynomial (Localization.AtPrime 𝔪)) r →
            elementaryMatrixUnitMap (ι := Fin N)
                (Polynomial.constantCoeff (R := Localization.AtPrime 𝔪))
                (elementaryMatrixUnitMap (ι := Fin N)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F) = 1 →
              elementaryMatrixUnitMap (ι := Fin N)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
                elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR2BlockLocal

/-- **The reduction**: the normalized block form gives R2 (`SuslinR1StabLocal`), in every rank
and for every commutative ring. -/
theorem suslinR2_stabLocal_of_blockLocal {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinR2BlockLocal A N) : SuslinR1StabLocal A N := by
  intro τ hdet h0 𝔪 h𝔪 F hF r hrow
  obtain ⟨F', hF', hblock, hnorm⟩ := suslinR2_block_core _
    (suslinR2_constantCoeff_map (algebraMap A (Localization.AtPrime 𝔪)) τ h0) F hF r hrow
  exact h τ hdet h0 𝔪 h𝔪 F' hF' r hblock hnorm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_stabLocal_of_blockLocal

/-- The converse (LOUD: the two are equivalent): R2 gives the normalized block form. -/
theorem suslinR2_blockLocal_of_stabLocal {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinR1StabLocal A N) : SuslinR2BlockLocal A N := by
  intro τ hdet h0 𝔪 h𝔪 F hF r hblock _
  have hb : IsCoordinateBlock r (elementaryMatrixUnitMap (ι := Fin N)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F) := hblock
  refine h τ hdet h0 𝔪 h𝔪 F hF r fun c ↦ ?_
  rw [hb.1 c]
  by_cases hc : c = r
  · rw [if_pos hc.symm, if_pos hc]
  · rw [if_neg (Ne.symm hc), if_neg hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_blockLocal_of_stabLocal

/-- **Truth witness**: the local case gives the normalized block form. -/
theorem suslinR2_blockLocal_of_localCase {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinLocalCaseStatement A N) : SuslinR2BlockLocal A N :=
  fun τ hdet h0 𝔪 h𝔪 _ _ _ _ _ ↦ h τ hdet h0 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_blockLocal_of_localCase

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

import GroupApproximation.BooneHigman.Metabelian.SuslinR1IntLead
import GroupApproximation.BooneHigman.Metabelian.SuslinR1Columns
import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# R1 over `ℤ[1/m]`: the primewise coordinate Statement

Lane `bh-met-90w`.  `SuslinR1IntPrimewiseLocal A N` weakens `SuslinR1FinCoordLocal A N`
(one entry of `φ(τ) ε` with UNIT leading coefficient) to a statement about the ideal
`I = (φ(τ) ε)_{r, j ≠ t}` of the entries of row `r` outside column `t`:

* `I` contains a polynomial whose leading coefficient is a positive INTEGER `c`
  (over `ℤ[1/m][s]` this is what a Nagata-type change of variables naturally gives), and
* for each of the finitely many primes `p ∣ c`, `I` contains a polynomial whose leading
  coefficient is coprime to `p` (a separate witness for each prime).

`suslinR1Int_coordLocal_of_primewise`: the leading coefficients of `I` form an ideal
(`suslinR1Int_leadSup`), which is the unit ideal by the primewise criterion; so `I` contains a
monic polynomial, and a column operation (`suslinR1_monic_of_mem_span`) makes entry `(r, t)`
monic.  `suslinR1Int_primewiseLocal_of_coord` is the converse (`c = 1`, no primes), so the two
`ℤ[1/m]` Statements are EQUIVALENT (`suslinR1Int_primewise_iff_intCoord`).  The primewise
form only allows more witnesses; it is not a strictly weaker proposition.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- The ideal of the entries of row `r` of `M` outside column `t`. -/
def suslinR1Int_rowIdeal {A : Type*} [CommRing A] {N : ℕ}
    (M : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) (r t : Fin N) :
    Ideal (Polynomial A) :=
  Ideal.span (Set.range fun j : {j : Fin N // j ≠ t} ↦
    (M : Matrix (Fin N) (Fin N) (Polynomial A)) r j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_rowIdeal

theorem suslinR1Int_entry_mem_rowIdeal {A : Type*} [CommRing A] {N : ℕ}
    (M : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) (r : Fin N) {j t : Fin N}
    (h : j ≠ t) :
    (M : Matrix (Fin N) (Fin N) (Polynomial A)) r j ∈ suslinR1Int_rowIdeal M r t := by
  unfold suslinR1Int_rowIdeal
  exact Ideal.subset_span ⟨⟨j, h⟩, rfl⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_entry_mem_rowIdeal

/-- **The primewise coordinate Statement.**  For every normalized `τ ∈ SL_N(A[X])` there are
a ring automorphism `φ` of `A[X]`, an elementary `ε`, a row `r`, a column `t` and a positive
integer `c` such that the row ideal `I` of `φ(τ) ε` (row `r`, columns `≠ t`) contains a
polynomial with leading coefficient `c`, and for each prime `p ∣ c` one whose leading
coefficient is coprime to `p`. -/
def SuslinR1IntPrimewiseLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∃ φ : Polynomial A ≃+* Polynomial A, ∃ ε ∈ elementaryGroup (Fin N) (Polynomial A),
          ∃ r t : Fin N, ∃ c : ℕ, 0 < c ∧
            (∃ q ∈ suslinR1Int_rowIdeal
                (elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom τ * ε) r t,
              q.leadingCoeff = (c : A)) ∧
            ∀ p : ℕ, p.Prime → p ∣ c → ∃ q ∈ suslinR1Int_rowIdeal
                (elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom τ * ε) r t,
              IsCoprime q.leadingCoeff (p : A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1IntPrimewiseLocal

/-- **The reduction.**  The primewise Statement gives the coordinate Statement. -/
theorem suslinR1Int_coordLocal_of_primewise {A : Type*} [CommRing A] {N : ℕ}
    (h : SuslinR1IntPrimewiseLocal A N) : SuslinR1FinCoordLocal A N := by
  intro τ hdet hnorm
  obtain ⟨φ, ε, hε, r, t, c, hc, h0, hp⟩ := h τ hdet hnorm
  obtain _ | _ := subsingleton_or_nontrivial A
  · exact ⟨φ, ε, hε, r, t, isUnit_of_subsingleton _⟩
  · obtain ⟨q, hq, hqm⟩ := suslinR1Int_monic_of_primewise c hc h0 hp
    obtain ⟨F, hF, hFm⟩ := suslinR1_monic_of_mem_span
      (elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom τ * ε) r t hqm hq
    have hunit : ∀ g : Polynomial A, g.Monic → IsUnit g.leadingCoeff := fun g hg ↦ by
      rw [hg.leadingCoeff]
      exact isUnit_one
    refine ⟨φ, ε * F, mul_mem hε hF, r, t, ?_⟩
    rw [← mul_assoc]
    exact hunit _ hFm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_coordLocal_of_primewise

/-- **The converse** (`N ≥ 2`): a unit leading coefficient `u` at `(r, t)` puts the monic
`C(u⁻¹) · entry` in the row ideal outside any other column `t'`; take `c = 1`. -/
theorem suslinR1Int_primewiseLocal_of_coord {A : Type*} [CommRing A] {N : ℕ} (hN : 2 ≤ N)
    (h : SuslinR1FinCoordLocal A N) : SuslinR1IntPrimewiseLocal A N := by
  intro τ hdet hnorm
  obtain ⟨φ, ε, hε, r, t, hu⟩ := h τ hdet hnorm
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨t', ht'⟩ := exists_ne t
  have hmon := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hu.val_inv_mul
  refine ⟨φ, ε, hε, r, t', 1, Nat.one_pos,
    ⟨Polynomial.C ((hu.unit⁻¹ : Aˣ) : A) * _,
      Ideal.mul_mem_left _ _ (suslinR1Int_entry_mem_rowIdeal _ r ht'.symm), ?_⟩,
    fun p hp hpd ↦ absurd (Nat.dvd_one.1 hpd) hp.one_lt.ne'⟩
  rw [Nat.cast_one]
  exact hmon.leadingCoeff

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_primewiseLocal_of_coord

/-- **The primewise `ℤ[1/m]` Statement** (the residual gap): `SuslinR1IntPrimewiseLocal` for
the family `ℤ[1/m][s_1,…,s_k]`, under the hypotheses of `SuslinR1FinIntCoordStatement`. -/
def SuslinR1IntPrimewiseStatement : Prop :=
  ∀ (m k N : ℕ),
    (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
      SuslinR1IntPrimewiseLocal (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1IntPrimewiseStatement

/-- **The reduction**: the primewise Statement gives the `ℤ` coordinate Statement. -/
theorem suslinR1Int_intCoord_of_primewise (h : SuslinR1IntPrimewiseStatement) :
    SuslinR1FinIntCoordStatement :=
  fun m k N hA hN ↦ suslinR1Int_coordLocal_of_primewise (h m k N hA hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_intCoord_of_primewise

/-- **Truth check**: the `ℤ` coordinate Statement gives the primewise one. -/
theorem suslinR1Int_primewise_of_intCoord (hc : SuslinR1FinIntCoordStatement) :
    SuslinR1IntPrimewiseStatement :=
  fun m k N hA hN ↦ suslinR1Int_primewiseLocal_of_coord (by omega) (hc m k N hA hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_primewise_of_intCoord

/-- The primewise and the coordinate `ℤ[1/m]` Statements are equivalent. -/
theorem suslinR1Int_primewise_iff_intCoord :
    SuslinR1IntPrimewiseStatement ↔ SuslinR1FinIntCoordStatement :=
  ⟨suslinR1Int_intCoord_of_primewise, suslinR1Int_primewise_of_intCoord⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_primewise_iff_intCoord

/-- **The target, from the primewise Statement and R2.** -/
theorem suslinR1Int_finite_of_primewise (h : SuslinR1IntPrimewiseStatement)
    (h2 : SuslinHorrocksR2Statement) : SuslinR1FiniteStatement :=
  suslinR1Fin_finite_of_intCoord (suslinR1Int_intCoord_of_primewise h) h2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_finite_of_primewise

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

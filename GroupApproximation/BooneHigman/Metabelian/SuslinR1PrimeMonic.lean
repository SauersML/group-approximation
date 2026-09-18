import GroupApproximation.BooneHigman.Metabelian.SuslinR1PrimeAvoid
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.ZInv
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import GroupApproximation.Meta.AxiomGuard

/-!
# R1 over `ℤ[1/m]`: the primewise Statement from a matrix-free monic Statement

Lane `bh-met-91i`, part 2.  Target: `SuslinR1IntPrimewiseStatement`.  NOT closed; the gap is
isolated as the matrix-free `suslinR1Prime_MonicStatement`, with the reduction
`suslinR1Prime_primewise_of_monic` proved here (no literature input in the proof).

**The residual** `suslinR1Prime_MonicStatement`: for `m ≠ 0` and `B = ℤ[1/m][s_1,…,s_k][X]`,
every ideal `J ⊆ B` lying in no principal ideal `(π)` with `π` prime contains some `q` that
becomes MONIC in `X` after a ring automorphism `φ` of `B`.

**Truth.**  `B` is a UFD (a polynomial ring over the UFD `ℤ[1/m]`), so its height-one primes
are principal; hence `J` has height `≥ 2 > 1 = dim ℤ[1/m]` (or `J = B`).  The claim is then the
`d = 1` case of Suslin's monic polynomial theorem (ht `J > dim R` gives a monic after an
`R`-automorphism of `R[x_1,…,x_n]`).  LOUD: this is a special case of a LITERATURE theorem
(Suslin), stated here as the open residual Statement, never assumed.

**Why it is strictly smaller in proof content (not logically weaker, not equivalent).**
The residual is pure commutative algebra: no matrices, no `φ(τ) ε` bookkeeping, no primes
of `ℤ`, no normalization.  Everything else is proved: the unimodular row, Davis prime
avoidance and the column operation (`suslinR1Prime_avoidCol`), transport of the row ideal
along `φ`, the trivial ring `m = 0`, and `c = 1`.  Its SHAPE is more general than the
target's (all such ideals, not only row ideals), so it is not a consequence of the target
by a formal argument; it is true by Suslin's theorem.

**Truth check of the suggested route (reduce mod `p`, then lift).**  With `φ, ε` fixed the
lifting step is FALSE: for `k = 0`, `τ = [[1+pX, X, 0], [-p²X, 1-pX, 0], [0, 0, 1]]` is
normalized with `det τ = 1`; for row `1`, column `2`, the row ideal `(1+pX)` has all leading
coefficients in `pℤ`, but it is the unit ideal mod `p`.  Even at height `2` in fixed
coordinates, `(s, pX - 1) ⊆ ℤ[s][X]` has leading-coefficient ideal `(s, p)`; one needs a
change of variables.  The Jacobson-type residual "`∀ p ∤ m`, some leading coefficient is
coprime to `p`" was rejected: it is only an EQUIVALENT restatement of the target.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- A ring endomorphism of `A[X]` carries the row ideal of `M` into that of `f(M)`. -/
theorem suslinR1Prime_map_mem_rowIdeal {A : Type*} [CommRing A] {N : ℕ}
    (f : Polynomial A →+* Polynomial A) (M : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (r t : Fin N) {x : Polynomial A} (hx : x ∈ suslinR1Int_rowIdeal M r t) :
    f x ∈ suslinR1Int_rowIdeal (elementaryMatrixUnitMap (ι := Fin N) f M) r t := by
  have h := Ideal.mem_map_of_mem f hx
  unfold suslinR1Int_rowIdeal at h ⊢
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_map_mem_rowIdeal

/-- **The reduction, for one ring.**  If every ideal of `A[X]` in no principal prime ideal
contains an element that is monic after an automorphism, the primewise local Statement holds
in every size `N ≥ 3` (with `c = 1`). -/
theorem suslinR1Prime_primewiseLocal_of_monicLocal {A : Type*} [CommRing A] [Nontrivial A]
    [WfDvdMonoid (Polynomial A)] {N : ℕ} (hN : 3 ≤ N)
    (hmon : ∀ J : Ideal (Polynomial A),
      (∀ π : Polynomial A, Prime π → ¬J ≤ Ideal.span {π}) →
      ∃ φ : Polynomial A ≃+* Polynomial A, ∃ q ∈ J, (φ q).Monic) :
    SuslinR1IntPrimewiseLocal A N := by
  intro τ _ _
  obtain ⟨ε, hε, t, havoid⟩ := suslinR1Prime_avoidCol hN τ ⟨0, by omega⟩
  obtain ⟨φ, q, hq, hqm⟩ := hmon _ havoid
  refine ⟨φ, elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom ε,
    elementaryGroup_map_le (ι := Fin N) φ.toRingHom (Subgroup.mem_map_of_mem _ hε),
    ⟨0, by omega⟩, t, 1, Nat.one_pos, ⟨φ q, ?_, ?_⟩,
    fun p hp hpd ↦ absurd (Nat.dvd_one.1 hpd) hp.one_lt.ne'⟩
  · rw [← map_mul (elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom) τ ε]
    exact suslinR1Prime_map_mem_rowIdeal φ.toRingHom (τ * ε) _ t hq
  · rw [Nat.cast_one]
    exact hqm.leadingCoeff

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_primewiseLocal_of_monicLocal

/-- `ℤ[1/0]` is the zero ring, hence so is `ℤ[1/0][s_1,…,s_k]`. -/
theorem suslinR1Prime_zero_eq_one (k : ℕ) : (0 : Chain.SIntPoly 0 k) = 1 := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)
  have e : algebraMap ℤ (Localization.Away ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = 0 :=
    (map_natCast (algebraMap ℤ (Localization.Away ((0 : ℕ) : ℤ))) 0).trans Nat.cast_zero
  rw [e, isUnit_zero_iff] at hu
  have h : (MvPolynomial.C 0 : Chain.SIntPoly 0 k) = MvPolynomial.C 1 := by
    rw [hu]
  rwa [map_zero, map_one] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_zero_eq_one

/-- Over the zero ring the primewise local Statement is trivial. -/
theorem suslinR1Prime_primewiseLocal_of_zero_eq_one {A : Type*} [CommRing A] {N : ℕ}
    (hN : 0 < N) (h01 : (0 : A) = 1) : SuslinR1IntPrimewiseLocal A N := by
  intro τ _ _
  exact ⟨RingEquiv.refl _, 1, Subgroup.one_mem _, ⟨0, hN⟩, ⟨0, hN⟩, 1, Nat.one_pos,
    ⟨0, Submodule.zero_mem _, eq_of_zero_eq_one h01 _ _⟩,
    fun p hp hpd ↦ absurd (Nat.dvd_one.1 hpd) hp.one_lt.ne'⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_primewiseLocal_of_zero_eq_one

/-- **The residual Statement** (matrix-free; the `d = 1` case of Suslin's monic polynomial
result over `ℤ[1/m]`, see the module docstring): for `m ≠ 0`, every ideal of
`ℤ[1/m][s_1,…,s_k][X]` lying in no principal prime ideal contains an element that is monic
in `X` after a ring automorphism. -/
def suslinR1Prime_MonicStatement : Prop :=
  ∀ (m k : ℕ), m ≠ 0 → ∀ J : Ideal (Polynomial (Chain.SIntPoly m k)),
    (∀ π : Polynomial (Chain.SIntPoly m k), Prime π → ¬J ≤ Ideal.span {π}) →
      ∃ φ : Polynomial (Chain.SIntPoly m k) ≃+* Polynomial (Chain.SIntPoly m k),
        ∃ q ∈ J, (φ q).Monic

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_MonicStatement

/-- **The reduction**: the monic Statement gives the primewise `ℤ[1/m]` Statement. -/
theorem suslinR1Prime_primewise_of_monic (h : suslinR1Prime_MonicStatement) :
    SuslinR1IntPrimewiseStatement := by
  intro m k N _ hN
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact suslinR1Prime_primewiseLocal_of_zero_eq_one (by omega) (suslinR1Prime_zero_eq_one k)
  · haveI : IsDomain (Localization.Away (m : ℤ)) := CharZeroHost.isDomain_away hm.ne'
    haveI : WfDvdMonoid (Polynomial (Chain.SIntPoly m k)) := IsNoetherianRing.wfDvdMonoid
    exact suslinR1Prime_primewiseLocal_of_monicLocal hN (h m k hm.ne')

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_primewise_of_monic

/-- The monic Statement gives the `ℤ` coordinate Statement. -/
theorem suslinR1Prime_intCoord_of_monic (h : suslinR1Prime_MonicStatement) :
    SuslinR1FinIntCoordStatement :=
  suslinR1Int_intCoord_of_primewise (suslinR1Prime_primewise_of_monic h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_intCoord_of_monic

/-- The monic Statement and R2 give the finite R1 Statement. -/
theorem suslinR1Prime_finite_of_monic (h : suslinR1Prime_MonicStatement)
    (h2 : SuslinHorrocksR2Statement) : SuslinR1FiniteStatement :=
  suslinR1Int_finite_of_primewise (suslinR1Prime_primewise_of_monic h) h2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_finite_of_monic

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

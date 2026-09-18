import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import Mathlib.Algebra.MvPolynomial.Equiv
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin input, part 5: reduction to the one-variable step

Lane `bh-met-23`.  `PolynomialSuslinStatement` (in `AbsorptionEndpoint.lean`) asks for
`SL_N = E_N` for `N ≥ 3` over `F_p[s_0, ..., s_{k-1}]` and over `ℤ[1/m][t_0, ..., t_{k-1}]`.
Here we prove it from the **one-variable step** `SuslinOneVariableStatement`: if `SL_{N'} = E_{N'}`
for all `N' ≥ 3` over `A` (one of these coefficient rings with `k` variables), then
`SL_N = E_N` for `N ≥ 3` over `A[X]`.

The reduction `polynomialSuslin_of_oneVariable` is an induction on `k`:

* `k = 0`: `F_p` is a field (`specialLinearInElementary_of_field`) and `ℤ[1/m]` has a
  well-founded division (`specialLinearInElementary_away`, every `m`, including `m = 0`);
* `k = 1` in characteristic `p`: `F_p[X]` is Euclidean
  (`specialLinearInElementary_zmodPolynomial`), so the one-variable step is only assumed for
  `k ≥ 1`;
* `k → k + 1`: the one-variable step applied to the induction hypothesis, transported along
  `MvPolynomial.finSuccEquiv` (`specialLinearInElementary_of_ringEquiv`).

**Why the isolated statement is strictly smaller and true.**  It only asks for the single
passage `A ⇝ A[X]`, with the whole conclusion for `A` *given* as a hypothesis, and not for the
characteristic-`p` base `F_p[X]`; the base cases, the Euclidean algorithm over `F_p[X]` and
`ℤ[1/m]`, the induction and the transports are proved here.  It is true: by Suslin's theorem
(A. A. Suslin, *On the structure of the special linear group over polynomial rings*, 1977), for
a commutative Noetherian ring `F` of Krull dimension `d` and `n ≥ max(3, d + 2)`,
`SL_n(F[x_1, ..., x_r]) = SL_n(F) · E_n(F[x_1, ..., x_r])`.  For `F = F_p` (`d = 0`) and
`F = ℤ[1/m]` (`d ≤ 1`; the zero ring for `m = 0`) this applies at every `n ≥ 3`, and
`SL_n(F) = E_n(F)` is proved in this lane.  So every conclusion of the statement holds even
without its hypothesis.  The bound `N ≥ 3` cannot be dropped (Cohn: `SL_2(k[x, y]) ≠ E_2`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The one-variable Suslin step** for the two coefficient families (see the module
docstring for why this is strictly smaller than `PolynomialSuslinStatement`, and true). -/
def SuslinOneVariableStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p k) N') → 3 ≤ N →
        SpecialLinearInElementary (Polynomial (Chain.CharPPoly p k)) N) ∧
    ∀ (m k N : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m k) N') → 3 ≤ N →
        SpecialLinearInElementary (Polynomial (Chain.SIntPoly m k)) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinOneVariableStatement

/-- Transport to polynomials in no variables. -/
theorem suslin_mvPolynomial_zero (R : Type*) [CommRing R] {N : ℕ}
    (h : SpecialLinearInElementary R N) :
    SpecialLinearInElementary (MvPolynomial (Fin 0) R) N :=
  specialLinearInElementary_of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_mvPolynomial_zero

/-- Transport along `MvPolynomial.finSuccEquiv`. -/
theorem suslin_mvPolynomial_succ (R : Type*) [CommRing R] (k : ℕ) {N : ℕ}
    (h : SpecialLinearInElementary (Polynomial (MvPolynomial (Fin k) R)) N) :
    SpecialLinearInElementary (MvPolynomial (Fin (k + 1)) R) N :=
  specialLinearInElementary_of_ringEquiv (MvPolynomial.finSuccEquiv R k).symm.toRingEquiv h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_mvPolynomial_succ

/-- `SL_N(F_p[s_0]) = E_N` at every positive rank (transport of the Euclidean case). -/
theorem specialLinearInElementary_charPPoly_one (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 0 < N) :
    SpecialLinearInElementary (Chain.CharPPoly p 1) N :=
  suslin_mvPolynomial_succ (ZMod p) 0
    (specialLinearInElementary_of_ringEquiv
      (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0)).symm)
      (specialLinearInElementary_zmodPolynomial p hN))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_charPPoly_one

/-- **The reduction**: the one-variable step gives Suslin's theorem for both families. -/
theorem polynomialSuslin_of_oneVariable (h : SuslinOneVariableStatement) :
    PolynomialSuslinStatement := by
  refine ⟨fun p _ k ↦ ?_, fun m k ↦ ?_⟩
  · induction k with
    | zero =>
        intro N hN
        exact suslin_mvPolynomial_zero (ZMod p)
          (specialLinearInElementary_of_field (ZMod p) (by omega))
    | succ k IH =>
        intro N hN
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact specialLinearInElementary_charPPoly_one p (by omega)
        · exact suslin_mvPolynomial_succ (ZMod p) k (h.1 p k N hk IH hN)
  · induction k with
    | zero =>
        intro N hN
        exact suslin_mvPolynomial_zero (Localization.Away (m : ℤ))
          (specialLinearInElementary_away m (by omega))
    | succ k IH =>
        intro N hN
        exact suslin_mvPolynomial_succ (Localization.Away (m : ℤ)) k (h.2 m k N IH hN)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.polynomialSuslin_of_oneVariable

/-- Both chain absorption leaves from the one-variable Suslin step. -/
theorem elementaryAbsorptionStatements_of_oneVariable (h : SuslinOneVariableStatement) :
    Chain.CharPElementaryAbsorptionStatement ∧ Chain.CharZeroElementaryAbsorptionStatement :=
  elementaryAbsorptionStatements_of_suslin (polynomialSuslin_of_oneVariable h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.elementaryAbsorptionStatements_of_oneVariable

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation

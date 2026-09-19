import GroupApproximation.CharClass.LerayHirschGradedIso
import GroupApproximation.CharClass.CohomologyLHRestrict

/-!
# The mod-2 Chern classes are unchanged by a transport of the total space

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`LerayHirschGradedIso.lerayHirschGraded_of_iso` moves a Leray–Hirsch instance
along an isomorphism of total spaces over one base.  The Thom class is
characterised by the transported instance's coefficients, while `lixChern` reads
the original one's, so the two are only comparable once the transport is known to
leave the coefficients alone.  It does.

The reason is uniqueness rather than a computation.  The transport carries each
column term to the corresponding column term, so the original coefficient family
still combines to the top cup power downstairs; `lhCoeff_unique` then says it *is*
the transported instance's coefficient family, with no case analysis and no
degree bookkeeping.

Nothing here mentions bundles, so it holds of whatever supplies the two
compatibilities.

## Main declarations

* `LH.lhMap_eq_sum_lhDomain` — `lhMap` as a sum of column terms.
* `LH.lhMap_of_iso` — the combination downstairs is the pullback of the combination upstairs.
* `LH.gammaCoeff_of_iso` — **the coefficients are unchanged.**
* `LH.gamma_of_iso` — **the mod-2 Chern classes are unchanged.**
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LH

variable {X P Q : TopCat.{0}}

/-- `lhMap` is the sum of its column terms.  Every index of `lhDomainCard` admits
its own degree, so no summand is in the vanishing branch. -/
theorem lhMap_eq_sum_lhDomain (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n a = ∑ i : Fin (lhDomainCard r n), lhTerm π ξ n (i : ℕ) (a i) :=
  Finset.sum_congr rfl
    (fun i _ => (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm)

/-- **The combination downstairs is the pullback of the combination upstairs.** -/
theorem lhMap_of_iso (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod2 P 2) (ξQ : Hmod2 Q 2) (hξ : pull e.hom 2 ξ = ξQ) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap πQ ξQ r n a = pull e.hom n (lhMap π ξ r n a) := by
  rw [lhMap_eq_sum_lhDomain, lhMap_eq_sum_lhDomain, pull_sum]
  exact Finset.sum_congr rfl
    (fun i _ => (LHCast.pull_lhTerm e.hom π πQ hπ ξ ξQ hξ n (i : ℕ) (a i)).symm)

/-- **The Leray–Hirsch coefficients of the top cup power are unchanged by the
transport.**  The original family still combines to the top cup power downstairs,
so uniqueness identifies it with the transported family. -/
theorem gammaCoeff_of_iso (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X)
    (hπ : e.hom ≫ π = πQ) (ξ : Hmod2 P 2) (ξQ : Hmod2 Q 2)
    (hξ : pull e.hom 2 ξ = ξQ) {r : ℕ} (L : LerayHirschGraded π ξ r) :
    L.gammaCoeff
      = (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L).gammaCoeff := by
  refine LerayHirschGraded.lhCoeff_unique
    (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L) (2 * r) (cupPowE ξQ r)
    L.gammaCoeff ?_
  rw [lhMap_of_iso e π πQ hπ ξ ξQ hξ r (2 * r) L.gammaCoeff,
    L.lhMap_gammaCoeff, pull_cupPowE, hξ]

/-- **The mod-2 Chern classes are unchanged by the transport.** -/
theorem gamma_of_iso (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod2 P 2) (ξQ : Hmod2 Q 2) (hξ : pull e.hom 2 ξ = ξQ) {r : ℕ}
    (L : LerayHirschGraded π ξ r) (k : ℕ) :
    L.gamma k = (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L).gamma k := by
  by_cases hk : 0 < k ∧ k ≤ r
  · rw [LerayHirschGraded.gamma_eq_gammaOf L hk.1 hk.2,
      LerayHirschGraded.gamma_eq_gammaOf _ hk.1 hk.2,
      LerayHirschGraded.gammaOf, LerayHirschGraded.gammaOf,
      gammaCoeff_of_iso e π πQ hπ ξ ξQ hξ L]
  · by_cases hk0 : k = 0
    · subst hk0
      rw [LerayHirschGraded.gamma_zero, LerayHirschGraded.gamma_zero]
    · rw [LerayHirschGraded.gamma_eq_zero_of_gt L (by omega),
        LerayHirschGraded.gamma_eq_zero_of_gt _ (by omega)]

/-! Printed on every build. -/

#print axioms gamma_of_iso

end LH

end

end GroupApproximation.CharClass

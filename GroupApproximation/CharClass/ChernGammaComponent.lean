import GroupApproximation.CharClass.ChernGammaBridge

/-!
# The bridge between the two Chern classes

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`ChernGammaBridge` puts the ring relation in `lhFun` form.  Taking its degree-`2r`
component turns it into an `lhMap` statement, and the Leray–Hirsch coordinates of
`ξ^r` are `gammaCoeff` by definition, so uniqueness of coordinates identifies the
polynomial's coefficients with the degreewise ones.  Reading that off at the index
`r - k` is the bridge.

This is what lets a consumer holding `LerayHirschGraded.gamma` — the Thom class's
Leray–Hirsch coordinates — talk about `LerayHirschData.chern`, which is what the
endgame's `topClass` is built from.

## Main declarations

* `component_chern_eq_gamma` — **the bridge.**

## Manuscript status

Machinery.  The identity `hclass` is stated across.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}

/-- **The ring Chern class, read in its own degree, is the degreewise one.**

Both are the coefficient of `ξ^{r-k}` in the relation satisfied by `ξ^r`; the
proof is that the relation has unique Leray–Hirsch coordinates, so the two ways of
reading it off agree. -/
theorem component_chern_eq_gamma [Nonempty X] (L : LerayHirschGraded π ξ r) (k : ℕ) :
    TotalH.component X (2 * k) ((lerayHirschData_of_graded L).chern k) = L.gamma k := by
  set D := lerayHirschData_of_graded L with hD
  letI := D.algebra
  set c : Fin r → TotalH X := fun i => D.chernPolynomial.coeff (i : ℕ) with hc
  have hcomp : lhMap π ξ r (2 * r)
      (fun i : Fin (lhDomainCard r (2 * r)) => degFun X r (2 * r) c (i : ℕ))
      = cupPowE ξ r := by
    rw [← component_lhFun π ξ r (2 * r) c, ← chern_relation_lhFun L, totalH_of_pow,
      TotalH.component_of]
  have huniq : (fun i : Fin (lhDomainCard r (2 * r)) => degFun X r (2 * r) c (i : ℕ))
      = L.gammaCoeff :=
    L.lhCoeff_unique (2 * r) (cupPowE ξ r) _ hcomp
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have hcoeff : D.chern 0 = 1 := by
      show chernClass D.powerBasis 0 = 1
      rw [chernClass_of_le D.powerBasis (Nat.zero_le _), Nat.sub_zero]
      have h : (chernPoly D.powerBasis).coeff (chernPoly D.powerBasis).natDegree = 1 :=
        (chernPoly_monic D.powerBasis).coeff_natDegree
      rwa [natDegree_chernPoly D.powerBasis] at h
    rw [hcoeff, L.gamma_zero, ← TotalH.of_one X, TotalH.component_of]
  · rcases Nat.lt_or_ge r k with hkr | hkr
    · rw [L.gamma_eq_zero_of_gt hkr]
      have hz : D.chern k = 0 := chernClass_eq_zero_of_lt D.powerBasis hkr
      rw [hz, map_zero]
    · have hidx : r - k < lhDomainCard r (2 * r) := by
        rw [lhDomainCard_two_mul]
        omega
      have hval : degFun X r (2 * r) c (r - k)
          = L.gammaCoeff (⟨r - k, hidx⟩ : Fin (lhDomainCard r (2 * r))) :=
        congrFun huniq ⟨r - k, hidx⟩
      have hdeg : 2 * r - 2 * (r - k) = 2 * k := by omega
      have hdf : degFun X r (2 * r) c (r - k)
          = TotalH.component X (2 * r - 2 * (r - k)) (D.chern k) := by
        rw [degFun, dif_pos (show r - k < r by omega)]
        congr 1
        show D.chernPolynomial.coeff (r - k) = D.chern k
        show (chernPoly D.powerBasis).coeff (r - k) = chernClass D.powerBasis k
        rw [chernClass_of_le D.powerBasis hkr]
        rfl
      rw [L.gamma_eq_gammaOf hk1 hkr]
      show TotalH.component X (2 * k) (D.chern k)
          = cohCast (show 2 * r - 2 * (r - k) = 2 * k by omega)
            (L.gammaCoeff ⟨r - k, hidx⟩)
      rw [← hval, hdf, ← component_cohCast X hdeg (D.chern k)]

end

end LH
end CharClass
end GroupApproximation

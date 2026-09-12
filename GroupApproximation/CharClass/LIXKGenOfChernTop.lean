import GroupApproximation.CharClass.LIXKGenChernOf
import GroupApproximation.CharClass.ChernClassesEvenHomogOf
import GroupApproximation.CharClass.CohomologyLHRingPiecesOf
import GroupApproximation.CharClass.CohomologyLHDegreewiseOf
import GroupApproximation.CharClass.LerayHirschGradedIso
import GroupApproximation.CharClass.ThomHyperplaneLHOf
import GroupApproximation.CharClass.LerayHirschCompactClosedOf
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The top Chern class over a field is the negated top coefficient of the hyperplane presentation

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12; the leaf `hgamma` of lane `lx-sliceK`'s
`KGen.lixHclassOf_of_eq`).

Over a field `K` the Thom class of the mapping-torus bundle restricts, on the base, to
`π^*(−γ_r)` with `γ_r` the top Leray–Hirsch coefficient of the **hyperplane** presentation
(`lixHclassOf`), while the Step C top class is `KGen.lixChernDegOf K n dd hgen W r`, the ring Chern
class of the compact Leray–Hirsch data on `P(W)`.  This file identifies the two.

* **The transport leaves the coefficients alone** (`gamma_of_isoOf`, the `K`-form of `LH.gamma_of_iso`):
  the hyperplane presentation is `P(W)`'s presentation moved along `hyperIso`, and uniqueness of
  coordinates identifies the coefficients.
* **The ring Chern class is the negated coordinate** (`component_chernEven_eq_neg_gammaOf`): the monic
  relation `ξ^r + c_1 ξ^{r−1} + ⋯ + c_r = 0` puts `−c_k` in the Leray–Hirsch coordinates of `ξ^r`,
  and `LerayHirschGraded.gamma k` *is* such a coordinate (`CharClass/ChernGammaBridgeOf.lean`).  Over `F₂`
  the sign is invisible.

## Main declarations

* `KGen.gamma_of_isoOf` — the coefficients are unchanged by a transport, over any ring.
* `KGen.component_chernEven_eq_neg_gammaOf` — `c_k = −γ_k` in degree `2k`, for `1 ≤ k ≤ r`.
* `KGen.neg_hyperLHOf_gamma_eq_lixChernDegOf` — **`−γ_r(hyperplane) = lixChernDegOf … W r`**.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH

set_option linter.unusedSectionVars false

/-! ## 1. The coefficients are unchanged by a transport, over any ring -/

section Transport

variable {K : Type} [CommRing K] {X P Q : TopCat.{0}}

/-- `lhMap` is the sum of its column terms, over any ring. -/
theorem lhMap_eq_sum_lhDomainOf (π : P ⟶ X) (ξ : Hmod K P 2) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n a = ∑ i : Fin (lhDomainCard r n), lhTerm π ξ n (i : ℕ) (a i) :=
  Finset.sum_congr rfl
    (fun i _ => (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm)

/-- The combination downstairs is the pullback of the combination upstairs, over any ring. -/
theorem lhMap_of_isoOf (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod K P 2) (ξQ : Hmod K Q 2) (hξ : pull e.hom 2 ξ = ξQ) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ))) :
    lhMap πQ ξQ r n a = pull e.hom n (lhMap π ξ r n a) := by
  rw [lhMap_eq_sum_lhDomainOf, lhMap_eq_sum_lhDomainOf, LH.pull_sum]
  exact Finset.sum_congr rfl
    (fun i _ => (LHCast.pull_lhTermOf e.hom π πQ hπ ξ ξQ hξ n (i : ℕ) (a i)).symm)

/-- **The Leray–Hirsch coefficients of the top cup power are unchanged by the transport**, over any
ring. -/
theorem gammaCoeff_of_isoOf (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod K P 2) (ξQ : Hmod K Q 2) (hξ : pull e.hom 2 ξ = ξQ) {r : ℕ}
    (L : LerayHirschGraded π ξ r) :
    L.gammaCoeff = (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L).gammaCoeff := by
  refine LerayHirschGraded.lhCoeff_unique
    (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L) (2 * r) (cupPowE ξQ r) L.gammaCoeff ?_
  rw [lhMap_of_isoOf e π πQ hπ ξ ξQ hξ r (2 * r) L.gammaCoeff, L.lhMap_gammaCoeff,
    pull_cupPowE, hξ]

/-- **The Chern coefficients are unchanged by the transport**, over any ring. -/
theorem gamma_of_isoOf (e : Q ≅ P) (π : P ⟶ X) (πQ : Q ⟶ X) (hπ : e.hom ≫ π = πQ)
    (ξ : Hmod K P 2) (ξQ : Hmod K Q 2) (hξ : pull e.hom 2 ξ = ξQ) {r : ℕ}
    (L : LerayHirschGraded π ξ r) (k : ℕ) :
    L.gamma k = (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L).gamma k := by
  by_cases hk : 0 < k ∧ k ≤ r
  · rw [LerayHirschGraded.gamma_eq_gammaOf L hk.1 hk.2,
      LerayHirschGraded.gamma_eq_gammaOf _ hk.1 hk.2,
      LerayHirschGraded.gammaOf, LerayHirschGraded.gammaOf,
      gammaCoeff_of_isoOf e π πQ hπ ξ ξQ hξ L]
  · by_cases hk0 : k = 0
    · subst hk0
      rw [LerayHirschGraded.gamma_zero, LerayHirschGraded.gamma_zero]
    · rw [LerayHirschGraded.gamma_eq_zero_of_gt L (by omega),
        LerayHirschGraded.gamma_eq_zero_of_gt _ (by omega)]

end Transport

/-! ## 2. The ring Chern class is the negated coordinate, over any ring -/

section Sign

variable {K : Type} [CommRing K]

/-- A component read at a degree index equal to another is the transported component. -/
theorem component_cohCastOf (Y : TopCat.{0}) {d d' : ℕ} (h : d = d') (z : TotalHOf K Y) :
    TotalHOf.component K Y d' z = cohCast h (TotalHOf.component K Y d z) := by
  subst h
  exact (cohCast_self _ _).symm

/-- A degree transport commutes with negation. -/
theorem cohCast_negOf {Y : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod K Y m) :
    cohCast h (-a) = -cohCast h a := by
  subst h
  rw [cohCast_self, cohCast_self]

set_option maxHeartbeats 400000 in
/-- **The ring Chern class, read in its own degree, is the negated Leray–Hirsch coordinate**, over
any commutative ring, for `1 ≤ k ≤ r`. -/
theorem component_chernEven_eq_neg_gammaOf {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod K P 2}
    {r : ℕ} [Nontrivial (Gen.evenPart K X)] (L : LerayHirschGraded π ξ r) (k : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    TotalHOf.component K X (2 * k) ((LerayHirschDataEvenOf.of_graded L).chern k).1
      = -(L.gamma k) := by
  have hrel := (LerayHirschDataEvenOf.of_graded L).chern_relation_lhFunEvenOf
  have h1 : ((evenTautOf K ξ ^ r : Gen.evenPart K P) : TotalHOf K P)
      = lhFunOf K π r ξ (fun i : Fin r =>
          ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (i : ℕ) :
            Gen.evenPart K X) : TotalHOf K X)) :=
    (congrArg Subtype.val hrel).trans (LHCast.coe_lhFunEvenOf K π r ξ _)
  have h2 : ((evenTautOf K ξ ^ r : Gen.evenPart K P) : TotalHOf K P)
      = TotalHOf.of K P (2 * r) (cupPowE ξ r) := by
    rw [SubmonoidClass.coe_pow]
    exact LHCast.totalHOf_of_pow K ξ r
  have hmap : lhMap π ξ r (2 * r)
      (fun i : Fin (lhDomainCard r (2 * r)) => LHCast.degFunOf K X r (2 * r)
        (fun i : Fin r =>
          ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (i : ℕ) :
            Gen.evenPart K X) : TotalHOf K X)) (i : ℕ))
      = cupPowE ξ r := by
    rw [← LHCast.component_lhFunOf K π ξ r (2 * r), ← h1, h2, TotalHOf.component_of]
  have huniq := L.lhCoeff_unique (2 * r) (cupPowE ξ r) _ hmap
  have hidx : r - k < lhDomainCard r (2 * r) := by
    rw [lhDomainCard_two_mul]
    omega
  have hval : LHCast.degFunOf K X r (2 * r)
        (fun i : Fin r =>
          ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (i : ℕ) :
            Gen.evenPart K X) : TotalHOf K X)) (r - k)
      = L.gammaCoeff ⟨r - k, hidx⟩ :=
    congrFun huniq ⟨r - k, hidx⟩
  have hchern : (LerayHirschDataEvenOf.of_graded L).chern k
      = (LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (r - k) :=
    @chernClass_of_le (Gen.evenPart K X) (Gen.evenPart K P) _ _
      (LerayHirschDataEvenOf.of_graded L).algebra
      (LerayHirschDataEvenOf.of_graded L).powerBasis k hkr
  have hdf : LHCast.degFunOf K X r (2 * r)
        (fun i : Fin r =>
          ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (i : ℕ) :
            Gen.evenPart K X) : TotalHOf K X)) (r - k)
      = -TotalHOf.component K X (2 * r - 2 * (r - k))
          ((LerayHirschDataEvenOf.of_graded L).chern k).1 := by
    rw [LHCast.degFunOf, dif_pos (show r - k < r by omega)]
    show TotalHOf.component K X (2 * r - 2 * (r - k))
        ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (r - k) :
          Gen.evenPart K X) : TotalHOf K X) = _
    rw [hchern, NegMemClass.coe_neg, map_neg]
  have hdeg : 2 * r - 2 * (r - k) = 2 * k := by omega
  rw [LerayHirschGraded.gamma_eq_gammaOf L (by omega) hkr, LerayHirschGraded.gammaOf, ← hval,
    hdf, cohCast_negOf, neg_neg, component_cohCastOf X hdeg]

end Sign

/-! ## 3. At the mapping torus -/

variable {ℓ : ℕ}

/-- **The top Chern class over a field is the negated top coefficient of the hyperplane
presentation**, at the compact Leray–Hirsch presentation of the mapping torus with the dual
tautological class of any nonzero generator.  This is `hgamma` of `KGen.lixHclassOf_of_eq`. -/
theorem neg_hyperLHOf_gamma_eq_lixChernDegOf (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2)
    (hgen0 : hgen ≠ 0)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    -((ThomChernDeg.hyperLHOf (lixBundle n G hGc hGu)
        (LH.lerayHirschGraded_compactDualOf K (lixBundle n G hGc hGu) (lixRank n dd)
          (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd) hgen hgen0)).gamma (lixRank n dd))
      = lixChernDegOf K n dd hgen (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
          (lixRank n dd) := by
  haveI : Nonempty (TopCat.of (↥sphereOne × Gen.baseM n dd)) :=
    inferInstanceAs (Nonempty (↥sphereOne × Gen.baseM n dd))
  haveI : Nontrivial (TotalHOf K (TopCat.of (↥sphereOne × Gen.baseM n dd))) :=
    nontrivial_totalHOf K (TopCat.of (↥sphereOne × Gen.baseM n dd))
  have e1 := lixChernDegOf_mappingTorus K n dd hgen hGc hGu
    (LH.lerayHirschGraded_compactDualOf K (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd) hgen hgen0) (lixRank n dd)
  have e2 := component_chernEven_eq_neg_gammaOf
    (LH.lerayHirschGraded_compactDualOf K (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd) hgen hgen0) (lixRank n dd)
    (one_le_lixRank n dd) le_rfl
  have e3 := gamma_of_isoOf (ThomChernDeg.hyperIso (lixBundle n G hGc hGu))
    (projMapOf (lixBundle n G hGc hGu)) (ThomChernDeg.hyperProj (lixBundle n G hGc hGu))
    (ThomChernDeg.hyperIso_hom_comp (lixBundle n G hGc hGu))
    (LH.tautEulerDualK K hgen (lixBundle n G hGc hGu))
    (pull (ThomChernDeg.hyperIso (lixBundle n G hGc hGu)).hom 2
      (LH.tautEulerDualK K hgen (lixBundle n G hGc hGu))) rfl
    (LH.lerayHirschGraded_compactDualOf K (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd) hgen hgen0) (lixRank n dd)
  rw [e1]
  exact (congrArg Neg.neg e3.symm).trans e2.symm

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.gamma_of_isoOf
#audit_axioms KGen.component_chernEven_eq_neg_gammaOf
#audit_axioms KGen.neg_hyperLHOf_gamma_eq_lixChernDegOf

end GroupApproximation.CharClass

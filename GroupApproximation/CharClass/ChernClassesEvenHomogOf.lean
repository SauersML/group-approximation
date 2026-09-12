import GroupApproximation.CharClass.CohomologyLHRingDataOf
import GroupApproximation.CharClass.ChernGammaBridgeOf

/-!
# The Chern classes over `K` are homogeneous

`LerayHirschDataEvenOf.of_graded L` defines Chern classes `γ_k` in the even part of `H^*(X; K)`
from a Leray–Hirsch presentation.  A consumer reading them degree by degree needs to know that
`γ_k` lives in the single degree `2k`, and this file proves it, over any commutative ring and with
no nontriviality hypothesis.

The argument is uniqueness of coordinates.  `ξ^r` is the homogeneous class `of (2r) (ξ^{⌣r})`, and
the preimage of a homogeneous class under the ring-level combination can be chosen homogeneous
coordinate by coordinate (the `i`-th entry in degree `n − 2i`); the combination is injective, so the
actual coordinates of `ξ^r`, which are the negated lower coefficients of the Chern polynomial
(`chern_relation_lhFunEvenOf`), are homogeneous.  `γ_k` is the coefficient at `r − k`, so it lies
in degree `2r − 2(r − k) = 2k`.  The end cases `γ_0 = 1` and `γ_k = 0` above the rank are separate,
and a trivial even part makes every class zero.

## Main declarations

* `LHCast.exists_homog_preimage_lhFunOf` — a homogeneous class has homogeneous coordinates.
* `LerayHirschDataEvenOf.chern_eq_of_graded` — **`γ_k` is concentrated in degree `2k`**.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

set_option maxHeartbeats 1000000 in
/-- **A homogeneous class has homogeneous Leray–Hirsch coordinates**, over any ring: the `i`-th
coordinate of a class of degree `n` can be taken in degree `n − 2i`. -/
theorem exists_homog_preimage_lhFunOf {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2}
    {r : ℕ} (L : LerayHirschGraded π ξ r) (n : ℕ) (w : Hmod K P n) :
    ∃ c : Fin r → TotalHOf K X,
      (∀ i : Fin r, ∃ x : TotalPieceOf K X (n - 2 * (i : ℕ)),
        c i = TotalHOf.of K X (n - 2 * (i : ℕ)) x) ∧
      lhFunOf K π r ξ c = TotalHOf.of K P n w := by
  obtain ⟨a, ha⟩ := (L.bij n).2 w
  refine ⟨fun i => if h : (i : ℕ) < lhDomainCard r n then
    TotalHOf.of K X (n - 2 * (i : ℕ)) (a ⟨(i : ℕ), h⟩) else 0, fun i => ?_, ?_⟩
  · by_cases h : (i : ℕ) < lhDomainCard r n
    · exact ⟨a ⟨(i : ℕ), h⟩, dif_pos h⟩
    · exact ⟨0, by simp only [dif_neg h, map_zero]⟩
  · ext n'
    show TotalHOf.component K P n' (lhFunOf K π r ξ _)
      = TotalHOf.component K P n' (TotalHOf.of K P n w)
    rw [component_lhFunOf]
    rcases eq_or_ne n' n with rfl | hne
    · rw [TotalHOf.component_of, ← ha]
      congr 1
      funext j
      have h1 : ((j : ℕ) < r) := lt_rank_of_lhDomain j
      simp only [degFunOf, dif_pos h1, dif_pos j.isLt, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K P hne]
      have hzero : (fun j : Fin (lhDomainCard r n') =>
          degFunOf K X r n' (fun i => if h : (i : ℕ) < lhDomainCard r n then
            TotalHOf.of K X (n - 2 * (i : ℕ)) (a ⟨(i : ℕ), h⟩) else 0) (j : ℕ)) = 0 := by
        funext j
        have h1 : ((j : ℕ) < r) := lt_rank_of_lhDomain j
        have h2 : 2 * (j : ℕ) ≤ n' := two_mul_le_of_lhDomain j
        simp only [degFunOf, dif_pos h1]
        by_cases h3 : (j : ℕ) < lhDomainCard r n
        · rw [dif_pos h3]
          have h4 : 2 * (j : ℕ) ≤ n :=
            two_mul_le_of_lhDomain (⟨(j : ℕ), h3⟩ : Fin (lhDomainCard r n))
          exact TotalHOf.component_of_ne K X (by omega) _
        · rw [dif_neg h3]
          exact map_zero _
      rw [hzero, lhMap_zeroOf]

end LHCast

/-- A degree transport does not move a class in the total ring. -/
private theorem totalHOf_of_cohCast_eq {K : Type} [CommRing K] {X : TopCat.{0}} {m m' : ℕ}
    (h : m = m') (a : TotalPieceOf K X m) :
    TotalHOf.of K X m' (cohCast h a) = TotalHOf.of K X m a := by
  subst h
  rw [cohCast_self]

set_option maxHeartbeats 400000 in
/-- **The Chern classes over `K` are homogeneous**: `γ_k` is concentrated in degree `2k`, over any
commutative ring. -/
theorem LerayHirschDataEvenOf.chern_eq_of_graded {K : Type} [CommRing K] {X P : TopCat.{0}}
    {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r) (k : ℕ) :
    ∃ x : TotalPieceOf K X (2 * k),
      ((LerayHirschDataEvenOf.of_graded L).chern k : TotalHOf K X)
        = TotalHOf.of K X (2 * k) x := by
  classical
  by_cases hnt : Nontrivial (Gen.evenPart K X)
  · rcases lt_or_ge r k with hlt | hle
    · refine ⟨0, ?_⟩
      rw [(LerayHirschDataEvenOf.of_graded L).chern_eq_zero_of_lt hlt, map_zero]
      rfl
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · refine ⟨one (K := K) X, ?_⟩
        rw [(LerayHirschDataEvenOf.of_graded L).chern_zero, TotalHOf.of_one]
        rfl
      · have hrel := (LerayHirschDataEvenOf.of_graded L).chern_relation_lhFunEvenOf
        have h1 : ((evenTautOf K ξ ^ r : Gen.evenPart K P) : TotalHOf K P)
            = lhFunOf K π r ξ (fun i : Fin r =>
                ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (i : ℕ) :
                  Gen.evenPart K X) : TotalHOf K X)) :=
          (congrArg Subtype.val hrel).trans (LHCast.coe_lhFunEvenOf K π r ξ _)
        have h2 : ((evenTautOf K ξ ^ r : Gen.evenPart K P) : TotalHOf K P)
            = TotalHOf.of K P (2 * r) (cupPowE ξ r) := by
          rw [SubmonoidClass.coe_pow]
          exact LHCast.totalHOf_of_pow K ξ r
        obtain ⟨c, hc, hcfun⟩ := LHCast.exists_homog_preimage_lhFunOf L (2 * r) (cupPowE ξ r)
        have heq := LHCast.lhFunOf_injective L ((h1.symm.trans h2).trans hcfun.symm)
        have hi : r - k < r := by omega
        obtain ⟨x, hx⟩ := hc ⟨r - k, hi⟩
        have hx' : c ⟨r - k, hi⟩ = TotalHOf.of K X (2 * r - 2 * (r - k)) x := hx
        have hval : ((-(LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (r - k) :
              Gen.evenPart K X) : TotalHOf K X) = c ⟨r - k, hi⟩ :=
          congrFun heq ⟨r - k, hi⟩
        have hcoeff : (((LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (r - k) :
              Gen.evenPart K X) : TotalHOf K X)
            = -TotalHOf.of K X (2 * r - 2 * (r - k)) x := by
          rw [← hx', ← hval, NegMemClass.coe_neg, neg_neg]
        refine ⟨cohCast (show 2 * r - 2 * (r - k) = 2 * k by omega) (-x), ?_⟩
        have hchern : (LerayHirschDataEvenOf.of_graded L).chern k
            = (LerayHirschDataEvenOf.of_graded L).chernPolynomial.coeff (r - k) :=
          @chernClass_of_le (Gen.evenPart K X) (Gen.evenPart K P) _ _
            (LerayHirschDataEvenOf.of_graded L).algebra
            (LerayHirschDataEvenOf.of_graded L).powerBasis k hle
        rw [hchern, hcoeff, totalHOf_of_cohCast_eq, map_neg]
  · haveI : Subsingleton (Gen.evenPart K X) := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim ((LerayHirschDataEvenOf.of_graded L).chern k) 0, map_zero]
    rfl

end

end GroupApproximation.CharClass

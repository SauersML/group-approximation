import GroupApproximation.CharClass.CohomologyLHRingPiecesOf
import GroupApproximation.CharClass.ChernClassesEvenOf
import GroupApproximation.Meta.AxiomGuard

/-!
# `LerayHirschDataOf` and `LerayHirschDataEvenOf` from `LerayHirschGraded`, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyLHRingInj`, `CohomologyLHRingSurj` and `CohomologyLHRingData` with
coefficients in a commutative ring `K`.  The geometry produces `LerayHirschGraded`, bijectivity of
`lhMap` in each degree; lane `lix-lh`'s Chern classes over `K` consume ring-level bijectivity of
`lhFunOf` (`LerayHirschDataOf`) or of its even-part restriction `lhFunEvenOf`
(`LerayHirschDataEvenOf`).  This file is the bridge, and every step is the degree bookkeeping of
`CohomologyLHRingPiecesOf.component_lhFunOf`.

* **Injectivity**: to reach the `i`-th coefficient in degree `m`, look at degree `2i + m`, where the
  index `i` is in range.
* **Surjectivity**: `lhFunOf` is additive, so it suffices to hit a concentrated class, and there the
  witness is a finite explicit tuple.
* **The even parts**: `ξ` has degree two, so a class whose Leray–Hirsch combination is even has even
  coefficients (in an odd degree `2i + m` the combination reads the odd component `m` of the `i`-th
  coefficient), and the bijection restricts.

`LerayHirschDataOf` also asks that the base ring be commutative and the pulled-back classes central;
neither follows from graded Leray–Hirsch, so they are hypotheses of `lerayHirschDataOf_of_graded`.
The even-part data asks for nothing else.

## Main declarations

* `LHCast.lhFunOf_injective`, `LHCast.lhFunOf_surjective`, `LHCast.lhFunOf_bijective`.
* `LHCast.lerayHirschDataOf_of_graded` — **the constructor over `K`**.
* `LHCast.coe_lhFunEvenOf`, `LHCast.isEven_coeff_of_lhFunOf`.
* `LHCast.lhFunEvenOf_bijective_of_graded`, `LerayHirschDataEvenOf.of_graded` — **the even-part
  constructor**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. Additivity -/

theorem lhFunOf_zero (K : Type) [CommRing K] (π : P ⟶ X) (r : ℕ) (ξ : Hmod K P 2) :
    lhFunOf K π r ξ 0 = 0 := by
  show ∑ i : Fin r, TotalHOf.map K π ((0 : Fin r → TotalHOf K X) i)
      * TotalHOf.of K P 2 ξ ^ (i : ℕ) = 0
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Pi.zero_apply, map_zero, zero_mul]

theorem lhFunOf_add (K : Type) [CommRing K] (π : P ⟶ X) (r : ℕ) (ξ : Hmod K P 2)
    (c c' : Fin r → TotalHOf K X) :
    lhFunOf K π r ξ (c + c') = lhFunOf K π r ξ c + lhFunOf K π r ξ c' := by
  show ∑ i : Fin r, TotalHOf.map K π ((c + c') i) * TotalHOf.of K P 2 ξ ^ (i : ℕ)
      = (∑ i : Fin r, _) + ∑ i : Fin r, _
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, map_add, add_mul])

theorem lhMap_zeroOf {K : Type} [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2) (r n : ℕ) :
    lhMap π ξ r n 0 = 0 := by
  simp only [lhMap]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Pi.zero_apply, pull_zero, zero_cup, CharClass.cohCast_zero]

/-! ## 2. Injectivity -/

set_option maxHeartbeats 1000000 in
/-- **The ring-level combination is injective**, over any ring.  Reach the `i`-th coefficient in
degree `m` by looking at degree `2i + m`, where `i` is in range. -/
theorem lhFunOf_injective {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : Function.Injective (lhFunOf K π r ξ) := by
  intro c c' h
  funext i
  ext m
  have hn : (i : ℕ) < lhDomainCard r (2 * (i : ℕ) + m) :=
    (mem_lhDomain_iff r (2 * (i : ℕ) + m) (i : ℕ)).mpr ⟨i.isLt, by omega⟩
  have hcomp := congrArg (TotalHOf.component K P (2 * (i : ℕ) + m)) h
  rw [component_lhFunOf, component_lhFunOf] at hcomp
  have hval := congrFun ((L.bij (2 * (i : ℕ) + m)).1 hcomp) ⟨(i : ℕ), hn⟩
  simp only [degFunOf, dif_pos i.isLt] at hval
  have hm : 2 * (i : ℕ) + m - 2 * (i : ℕ) = m := by omega
  show TotalHOf.component K X m (c i) = TotalHOf.component K X m (c' i)
  rw [← hm]
  exact hval

/-! ## 3. Surjectivity -/

set_option maxHeartbeats 1000000 in
/-- **The ring-level combination is onto**, over any ring.  Additivity reduces it to the
concentrated elements, where the witness is finite and explicit. -/
theorem lhFunOf_surjective {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : Function.Surjective (lhFunOf K π r ξ) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, lhFunOf_zero K π r ξ⟩
  | of n w =>
    obtain ⟨a, ha⟩ := (L.bij n).2 w
    refine ⟨fun i => if h : (i : ℕ) < lhDomainCard r n then
      TotalHOf.of K X (n - 2 * (i : ℕ)) (a ⟨(i : ℕ), h⟩) else 0, ?_⟩
    ext n'
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
  | add u v hu hv =>
    obtain ⟨cu, hcu⟩ := hu
    obtain ⟨cv, hcv⟩ := hv
    exact ⟨cu + cv, by rw [lhFunOf_add, hcu, hcv]⟩

theorem lhFunOf_bijective {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : Function.Bijective (lhFunOf K π r ξ) :=
  ⟨lhFunOf_injective L, lhFunOf_surjective L⟩

/-! ## 4. The data over `K` -/

/-- **Leray–Hirsch data over `K` from the degreewise statement.**  The freeness field is the
ring-level bijectivity; commutativity of the base and centrality of the pulled-back classes are
fields of `LerayHirschDataOf` that graded Leray–Hirsch does not give, so they are hypotheses. -/
def lerayHirschDataOf_of_graded {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (hcomm : ∀ a b : TotalHOf K X, a * b = b * a)
    (hcentral : ∀ (c : TotalHOf K X) (x : TotalHOf K P),
      TotalHOf.map K π c * x = x * TotalHOf.map K π c) :
    LerayHirschDataOf K X P where
  proj := π
  rank := r
  taut := ξ
  mul_comm_base := hcomm
  map_central := hcentral
  free := lhFunOf_bijective L

@[simp] theorem lerayHirschDataOf_of_graded_proj {K : Type} [CommRing K] {π : P ⟶ X}
    {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (hcomm : ∀ a b : TotalHOf K X, a * b = b * a)
    (hcentral : ∀ (c : TotalHOf K X) (x : TotalHOf K P),
      TotalHOf.map K π c * x = x * TotalHOf.map K π c) :
    (lerayHirschDataOf_of_graded L hcomm hcentral).proj = π := rfl

@[simp] theorem lerayHirschDataOf_of_graded_rank {K : Type} [CommRing K] {π : P ⟶ X}
    {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (hcomm : ∀ a b : TotalHOf K X, a * b = b * a)
    (hcentral : ∀ (c : TotalHOf K X) (x : TotalHOf K P),
      TotalHOf.map K π c * x = x * TotalHOf.map K π c) :
    (lerayHirschDataOf_of_graded L hcomm hcentral).rank = r := rfl

@[simp] theorem lerayHirschDataOf_of_graded_taut {K : Type} [CommRing K] {π : P ⟶ X}
    {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (hcomm : ∀ a b : TotalHOf K X, a * b = b * a)
    (hcentral : ∀ (c : TotalHOf K X) (x : TotalHOf K P),
      TotalHOf.map K π c * x = x * TotalHOf.map K π c) :
    (lerayHirschDataOf_of_graded L hcomm hcentral).taut = ξ := rfl

/-! ## 5. The even parts -/

/-- The even-part combination, read in the whole ring, is the ring-level combination of the
underlying classes. -/
theorem coe_lhFunEvenOf (K : Type) [CommRing K] (π : P ⟶ X) (r : ℕ) (ξ : Hmod K P 2)
    (c : Fin r → Gen.evenPart K X) :
    (lhFunEvenOf K π r ξ c : TotalHOf K P) = lhFunOf K π r ξ (fun i => (c i : TotalHOf K X)) := by
  have h : ((Gen.evenPart K P).subtype (lhFunEvenOf K π r ξ c) : TotalHOf K P)
      = ∑ i : Fin r, (Gen.evenPart K P).subtype (Gen.evenMap K π (c i))
          * (Gen.evenPart K P).subtype (evenTautOf K ξ) ^ (i : ℕ) := by
    rw [lhFunEvenOf, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, map_pow])
  exact h

set_option maxHeartbeats 1000000 in
/-- **Even combinations have even coefficients.**  In an odd degree `2i + m` the combination
reads the odd component `m` of the `i`-th coefficient. -/
theorem isEven_coeff_of_lhFunOf {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (c : Fin r → TotalHOf K X)
    (hc : TotalHOf.IsEven (lhFunOf K π r ξ c)) (i : Fin r) : TotalHOf.IsEven (c i) := by
  intro m hm
  have hn : (i : ℕ) < lhDomainCard r (2 * (i : ℕ) + m) :=
    (mem_lhDomain_iff r (2 * (i : ℕ) + m) (i : ℕ)).mpr ⟨i.isLt, by omega⟩
  have hodd : Odd (2 * (i : ℕ) + m) := by
    obtain ⟨k, hk⟩ := hm
    exact ⟨(i : ℕ) + k, by omega⟩
  have hcomp : lhMap π ξ r (2 * (i : ℕ) + m)
        (fun j => degFunOf K X r (2 * (i : ℕ) + m) c (j : ℕ))
      = lhMap π ξ r (2 * (i : ℕ) + m) 0 := by
    rw [← component_lhFunOf, hc _ hodd, lhMap_zeroOf]
  have hval := congrFun ((L.bij (2 * (i : ℕ) + m)).1 hcomp) ⟨(i : ℕ), hn⟩
  simp only [degFunOf, dif_pos i.isLt, Pi.zero_apply] at hval
  have hm' : 2 * (i : ℕ) + m - 2 * (i : ℕ) = m := by omega
  rw [← hm']
  exact hval

set_option maxHeartbeats 1000000 in
/-- **Leray–Hirsch on the even parts, from the degreewise statement**, over any ring: the `free`
field of `LerayHirschDataEvenOf`. -/
theorem lhFunEvenOf_bijective_of_graded {K : Type} [CommRing K] {π : P ⟶ X} {ξ : Hmod K P 2}
    {r : ℕ} (L : LerayHirschGraded π ξ r) : Function.Bijective (lhFunEvenOf K π r ξ) := by
  constructor
  · intro c c' h
    have h' : lhFunOf K π r ξ (fun i => (c i : TotalHOf K X))
        = lhFunOf K π r ξ (fun i => (c' i : TotalHOf K X)) := by
      rw [← coe_lhFunEvenOf, ← coe_lhFunEvenOf, h]
    funext i
    exact Subtype.ext (congrFun (lhFunOf_injective L h') i)
  · intro z
    obtain ⟨c, hc⟩ := lhFunOf_surjective L (z : TotalHOf K P)
    have hzeven : TotalHOf.IsEven (lhFunOf K π r ξ c) := by
      rw [hc]
      exact Gen.mem_evenPart.mp z.2
    have heven : ∀ i, TotalHOf.IsEven (c i) := isEven_coeff_of_lhFunOf L c hzeven
    refine ⟨fun i => ⟨c i, Gen.mem_evenPart.mpr (heven i)⟩, Subtype.ext ?_⟩
    rw [coe_lhFunEvenOf]
    exact hc

end LHCast

/-- **Even-part Leray–Hirsch data from the degreewise statement**, over any ring. -/
def LerayHirschDataEvenOf.of_graded {K : Type} [CommRing K] {X P : TopCat.{0}} {π : P ⟶ X}
    {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r) : LerayHirschDataEvenOf K X P where
  proj := π
  rank := r
  taut := ξ
  free := LHCast.lhFunEvenOf_bijective_of_graded L

end

/-! Audited on every build. -/

#audit_axioms LHCast.lhFunOf_bijective
#audit_axioms LHCast.lhFunEvenOf_bijective_of_graded

end GroupApproximation.CharClass

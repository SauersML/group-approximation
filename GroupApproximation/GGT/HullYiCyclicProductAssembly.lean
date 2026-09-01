import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullYiMatchedProductRigidity

/-!
# Algebraic assembly of Hull's cyclic-product `yi` witnesses

Hull's proof of Lemma 5.6 first chooses a finite detecting family
`f₀,…,fₖ₋₁`, with `k ≥ 3`, and nonzero powers `aᵢ` satisfying

`E(fᵢ) = C_G(aᵢ)`.

It then chooses two cyclic products of such powers which are loxodromic,
pairwise non-commensurable, and avoid the finitely many commensurability classes
already selected.  The sole remaining step for cyclicity is geometric: for
each element of the elementary closure of a product, DGO Lemma 4.21(b) supplies
one full cyclic run of matched components.  The connector equations returned
by that run are exactly the hypotheses of
`elementaryClosure_eq_zpowers_of_matchedProduct`.

This file makes that handoff literal.  `YiOrientationPureProductPair` contains
the source data available immediately before the consecutive-component
argument.  `HasConsecutiveComponentMatch` is only the match output, with no
cyclicity conclusion hidden in it.  The assembly below proves membership of
the products in the suitable subgroup and derives `E(h) = ⟨h⟩` for both
products from those connector equations.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- The ordered product of a `Fin`-indexed family.  The order is the natural
order `0,1,…,k-1`, as in Hull's word `a₁⋯ aₖ`. -/
def orderedFinProduct : {k : ℕ} → (Fin k → G) → G
  | 0, _ => 1
  | _k + 1, a => a 0 * orderedFinProduct (fun i => a i.succ)

/-- An ordered product of elements of a subgroup remains in the subgroup. -/
theorem orderedFinProduct_mem (T : Subgroup G) :
    ∀ {k : ℕ} (a : Fin k → G), (∀ i, a i ∈ T) → orderedFinProduct a ∈ T := by
  intro k
  induction k with
  | zero =>
      intro a _
      exact T.one_mem
  | succ k ih =>
      intro a ha
      exact T.mul_mem (ha 0) (ih (fun i => a i.succ) (fun i => ha i.succ))

/-- Hull's centralizer condition is stable under passing to any nonzero
multiple of the chosen exponent.

The forward inclusion is preservation of commutation under powers.  For the
reverse inclusion, commuting with `f ^ (n * m)` is itself a nonzero
conjugate-power witness for membership in `E(f)`.  No geometric input is used. -/
theorem elementaryClosure_eq_centralizer_zpow_mul {f : G} {n : ℤ} (hn : n ≠ 0)
    (hcentral : (elementaryClosure f : Set G) =
      {x : G | Commute x (f ^ n)}) {m : ℤ} (hm : m ≠ 0) :
    (elementaryClosure f : Set G) =
      {x : G | Commute x ((f ^ n) ^ m)} := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ({x : G | Commute x (f ^ n)} : Set G) := by
      rw [← hcentral]
      exact hx
    exact hx'.zpow_right m
  · intro hx
    have hcomm : Commute x (f ^ (n * m)) := by
      rw [zpow_mul]
      exact hx
    refine mem_elementaryClosure.mpr
      ⟨n * m, n * m, mul_ne_zero hn hm, mul_ne_zero hn hm, ?_⟩
    calc
      x * f ^ (n * m) * x⁻¹ = f ^ (n * m) * x * x⁻¹ := by rw [hcomm.eq]
      _ = f ^ (n * m) := by group

/-- The complete source data immediately before Hull applies his consecutive-
component lemma.

The detector `f` is orientation-pure through the centralizer equalities and
detects the trivial radical through `intersection_eq_one`.  Each letter of each
product is a nonzero power of the corresponding detector.  The product-level
loxodromy, non-commensurability, and finite avoidance are precisely the output
of the preceding DGO Corollary 6.12 / Hull Lemma 3.9 selection; cyclicity is
deliberately absent. -/
structure YiOrientationPureProductPair
    (A : HullGeneratingSet G) (T : Subgroup G) (F : Finset G) where
  k : ℕ
  three_le : 3 ≤ k
  detector : Fin k → G
  detector_mem : ∀ i, detector i ∈ T
  detector_loxodromic : ∀ i,
    IsLoxodromic (detector i) (Cayley.base A.alphabet)
  detector_nonCommensurable : PairwiseNonCommensurable detector
  exponent : Fin k → ℤ
  exponent_ne_zero : ∀ i, exponent i ≠ 0
  base_centralizer : ∀ i,
    (elementaryClosure (detector i) : Set G) =
      {x : G | Commute x (detector i ^ exponent i)}
  multiplier : Bool → Fin k → ℤ
  multiplier_ne_zero : ∀ b i, multiplier b i ≠ 0
  letter : Bool → Fin k → G
  letter_eq : ∀ b i,
    letter b i = (detector i ^ exponent i) ^ multiplier b i
  intersection_eq_one : ∀ x : G,
    (∀ i, x ∈ elementaryClosure (detector i)) → x = 1
  product_loxodromic : ∀ b,
    IsLoxodromic (orderedFinProduct (letter b))
      (Cayley.base A.alphabet)
  product_nonCommensurable :
    PairwiseNonCommensurable (fun b => orderedFinProduct (letter b))
  product_avoids : ∀ b,
    AvoidsFiniteCommensurabilityOneSided F
      (orderedFinProduct (letter b))

namespace YiOrientationPureProductPair

variable {A : HullGeneratingSet G} {T : Subgroup G} {F : Finset G}

/-- The cyclic product represented by the prepared pair. -/
def product (P : YiOrientationPureProductPair A T F) (b : Bool) : G :=
  orderedFinProduct (P.letter b)

/-- Every product letter is a nonzero power of its detector. -/
theorem letter_is_nonzero_power (P : YiOrientationPureProductPair A T F)
    (b : Bool) (i : Fin P.k) :
    ∃ n : ℤ, n ≠ 0 ∧ P.letter b i = P.detector i ^ n := by
  refine ⟨P.exponent i * P.multiplier b i,
    mul_ne_zero (P.exponent_ne_zero i) (P.multiplier_ne_zero b i), ?_⟩
  rw [P.letter_eq, ← zpow_mul]

/-- The base centralizer equality remains valid for every selected product
letter. -/
theorem centralizer_letter (P : YiOrientationPureProductPair A T F)
    (b : Bool) (i : Fin P.k) :
    (elementaryClosure (P.detector i) : Set G) =
      {x : G | Commute x (P.letter b i)} := by
  rw [P.letter_eq]
  exact elementaryClosure_eq_centralizer_zpow_mul
    (P.exponent_ne_zero i) (P.base_centralizer i)
      (P.multiplier_ne_zero b i)

/-- Every prepared product lies in the suitable subgroup.  This is derived,
not stored: each letter is a power of a detector already in the subgroup. -/
theorem product_mem (P : YiOrientationPureProductPair A T F) (b : Bool) :
    P.product b ∈ T := by
  apply orderedFinProduct_mem T
  intro i
  obtain ⟨n, _hn, hletter⟩ := P.letter_is_nonzero_power b i
  rw [hletter]
  exact Subgroup.zpow_mem T (P.detector_mem i) n

/-- The exact consecutive-component output used by Hull's connector
calculation.  It contains no loxodromy, non-commensurability, avoidance, or
cyclicity conclusion.

For `t ∈ E(h)`, the `k` matched components give connector labels
`c₀,…,cₖ`.  Each initial connector belongs to the corresponding
`E(fᵢ)`, and the terminal connector is conjugation by the matched letter
`aᵢ`.  The final equation is Hull's prefix calculation. -/
def HasConsecutiveComponentMatch
    (P : YiOrientationPureProductPair A T F) : Prop :=
  ∀ b (t : G), t ∈ elementaryClosure (P.product b) →
    ∃ (l m : ℤ) (p : G) (c : Fin (P.k + 1) → G),
      (∀ i : Fin P.k,
        c i.castSucc ∈ elementaryClosure (P.detector i)) ∧
      (∀ i : Fin P.k,
        c i.succ = (P.letter b i)⁻¹ * c i.castSucc * P.letter b i) ∧
      t = P.product b ^ l * p * c 0 * p⁻¹ * P.product b ^ (-m)

/-- The consecutive-component match forces a prepared product to have cyclic
elementary closure.  All geometry has disappeared at this point: this is the
connector propagation and prefix cancellation formalized in
`HullYiMatchedProductRigidity`. -/
theorem elementaryClosure_product_eq_zpowers
    (P : YiOrientationPureProductPair A T F)
    (hmatch : P.HasConsecutiveComponentMatch) (b : Bool) :
    elementaryClosure (P.product b) = Subgroup.zpowers (P.product b) := by
  exact elementaryClosure_eq_zpowers_of_matchedProduct
    (lt_of_lt_of_le (by decide : 0 < 3) P.three_le)
      P.detector (P.letter b) (P.product b)
      (P.centralizer_letter b) P.intersection_eq_one (hmatch b)

/-- A prepared orientation-pure product pair plus the literal consecutive
match is the local one-sided Yi witness. -/
theorem exists_yiPair_of_consecutiveComponentMatch
    (P : YiOrientationPureProductPair A T F)
    (hmatch : P.HasConsecutiveComponentMatch) :
    ∃ g : Bool → G, (∀ b, g b ∈ T) ∧
      (∀ b, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable g ∧
      (∀ b, elementaryClosure (g b) = Subgroup.zpowers (g b)) ∧
      ∀ b, AvoidsFiniteCommensurabilityOneSided F (g b) := by
  refine ⟨P.product, P.product_mem, ?_, ?_, ?_, ?_⟩
  · exact P.product_loxodromic
  · exact P.product_nonCommensurable
  · exact P.elementaryClosure_product_eq_zpowers hmatch
  · exact P.product_avoids

end YiOrientationPureProductPair

/-- Selection of the source data preceding the consecutive-component argument.
This is Hull's orientation-pure detector together with his sufficiently deep
choice of two cyclic products.  It does not assert the component match or the
cyclicity conclusion obtained from it. -/
def YiOrientationPureProductPairSelection : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {T : Subgroup G},
    Suitable A.alphabet T → ∀ F : Finset G,
      Nonempty (YiOrientationPureProductPair A T F)

/-- The remaining geometric producer, stated uniformly over exactly the
prepared products on which Hull applies DGO Lemma 4.21(b). -/
def YiConsecutiveComponentMatchStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {T : Subgroup G}
    {F : Finset G} (P : YiOrientationPureProductPair A T F),
      P.HasConsecutiveComponentMatch

/-- The source-facing assembly theorem.  Once the orientation-pure products
are selected, the exact DGO consecutive-component match is the only remaining
input to the local Yi producer. -/
theorem yiSuitablePairAvoidingFiniteOneSided_of_productSelection_of_match
    (hselect : YiOrientationPureProductPairSelection.{u})
    (hmatch : YiConsecutiveComponentMatchStatement.{u}) :
    YiSuitablePairAvoidingFiniteOneSided.{u} := by
  intro G _ A T hT F
  obtain ⟨P⟩ := hselect A hT F
  exact P.exists_yiPair_of_consecutiveComponentMatch (hmatch P)

end HullSC
end GroupApproximation

import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullYiMatchedProductRigidity
import GroupApproximation.GGT.HullYiAlphabetTransfer

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

This file makes that handoff literal.  `YiOrientationPureProductFamily` contains
the source data available immediately before the consecutive-component
argument.  `HasConsecutiveComponentMatch` is the match output.  The selection
interface returns both together, so the DGO depth can be chosen before the
product exponents.  The assembly below proves membership of the products in
the suitable subgroup and derives `E(h) = ⟨h⟩` for both products from those
connector equations.
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
product is a nonzero power of the corresponding detector.  Product-level
loxodromy and pairwise non-commensurability are precisely the output of the
preceding DGO Corollary 6.12 / Hull Lemma 3.9 selection.  Finite avoidance is
derived below by counting, and cyclicity is deliberately absent. -/
structure YiOrientationPureProductFamily
    (A : HullGeneratingSet G) (T : Subgroup G) (ι : Type*) where
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
  multiplier : ι → Fin k → ℤ
  multiplier_ne_zero : ∀ j i, multiplier j i ≠ 0
  letter : ι → Fin k → G
  letter_eq : ∀ j i,
    letter j i = (detector i ^ exponent i) ^ multiplier j i
  intersection_eq_one : ∀ x : G,
    (∀ i, x ∈ elementaryClosure (detector i)) → x = 1
  productAlphabet : Alphabet G
  base_subset_productAlphabet :
    A.alphabet.carrier ⊆ productAlphabet.carrier
  product_loxodromic_enlarged : ∀ j,
    IsLoxodromic (orderedFinProduct (letter j))
      (Cayley.base productAlphabet)
  product_nonCommensurable :
    PairwiseNonCommensurable (fun j => orderedFinProduct (letter j))

namespace YiOrientationPureProductFamily

variable {A : HullGeneratingSet G} {T : Subgroup G} {ι : Type*}

/-- The cyclic product represented by the prepared pair. -/
def product (P : YiOrientationPureProductFamily A T ι) (j : ι) : G :=
  orderedFinProduct (P.letter j)

/-- Every product letter is a nonzero power of its detector. -/
theorem letter_is_nonzero_power (P : YiOrientationPureProductFamily A T ι)
    (j : ι) (i : Fin P.k) :
    ∃ n : ℤ, n ≠ 0 ∧ P.letter j i = P.detector i ^ n := by
  refine ⟨P.exponent i * P.multiplier j i,
    mul_ne_zero (P.exponent_ne_zero i) (P.multiplier_ne_zero j i), ?_⟩
  rw [P.letter_eq, ← zpow_mul]

/-- The base centralizer equality remains valid for every selected product
letter. -/
theorem centralizer_letter (P : YiOrientationPureProductFamily A T ι)
    (j : ι) (i : Fin P.k) :
    (elementaryClosure (P.detector i) : Set G) =
      {x : G | Commute x (P.letter j i)} := by
  rw [P.letter_eq]
  exact elementaryClosure_eq_centralizer_zpow_mul
    (P.exponent_ne_zero i) (P.base_centralizer i)
      (P.multiplier_ne_zero j i)

/-- Hull's Lemma A.1 brings the selected products back from the enlarged
cone-off alphabet to the manuscript's prescribed alphabet. -/
theorem product_loxodromic (P : YiOrientationPureProductFamily A T ι) (j : ι) :
    IsLoxodromic (P.product j) (Cayley.base A.alphabet) :=
  isLoxodromic_base_of_subset P.base_subset_productAlphabet
    (P.product_loxodromic_enlarged j)

/-- Every prepared product lies in the suitable subgroup.  This is derived,
not stored: each letter is a power of a detector already in the subgroup. -/
theorem product_mem (P : YiOrientationPureProductFamily A T ι) (j : ι) :
    P.product j ∈ T := by
  apply orderedFinProduct_mem T
  intro i
  obtain ⟨n, _hn, hletter⟩ := P.letter_is_nonzero_power j i
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
    (P : YiOrientationPureProductFamily A T ι) : Prop :=
  ∀ j (t : G), t ∈ elementaryClosure (P.product j) →
    ∃ (l m : ℤ) (p : G) (c : Fin (P.k + 1) → G),
      (∀ i : Fin P.k,
        c i.castSucc ∈ elementaryClosure (P.detector i)) ∧
      (∀ i : Fin P.k,
        c i.succ = (P.letter j i)⁻¹ * c i.castSucc * P.letter j i) ∧
      t = P.product j ^ l * p * c 0 * p⁻¹ * P.product j ^ (-m)

/-- The consecutive-component match forces a prepared product to have cyclic
elementary closure.  All geometry has disappeared at this point: this is the
connector propagation and prefix cancellation formalized in
`HullYiMatchedProductRigidity`. -/
theorem elementaryClosure_product_eq_zpowers
    (P : YiOrientationPureProductFamily A T ι)
    (hmatch : P.HasConsecutiveComponentMatch) (j : ι) :
    elementaryClosure (P.product j) = Subgroup.zpowers (P.product j) := by
  exact elementaryClosure_eq_zpowers_of_matchedProduct
    (lt_of_lt_of_le (by decide : 0 < 3) P.three_le)
      P.detector (P.letter j) (P.product j)
      (P.centralizer_letter j) P.intersection_eq_one (hmatch j)

/-- From `|F| + 2` prepared products, finite commensurability counting selects
two products outside every class represented by `F`.  Thus finite avoidance is
derived from Hull's actual large candidate family rather than assumed of an
already selected pair. -/
theorem exists_yiPair_of_consecutiveComponentMatch
    (F : Finset G)
    (P : YiOrientationPureProductFamily A T (Fin (F.card + 2)))
    (hmatch : P.HasConsecutiveComponentMatch) :
    ∃ g : Bool → G, (∀ b, g b ∈ T) ∧
      (∀ b, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable g ∧
      (∀ b, elementaryClosure (g b) = Subgroup.zpowers (g b)) ∧
      ∀ b, AvoidsFiniteCommensurabilityOneSided F (g b) := by
  obtain ⟨i, j, hij, hiF, hjF⟩ :=
    finiteCommensurabilityAvoidance F P.product P.product_nonCommensurable
  let g : Bool → G := fun b => bif b then P.product j else P.product i
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b
    · exact P.product_mem i
    · exact P.product_mem j
  · intro b
    cases b
    · exact P.product_loxodromic i
    · exact P.product_loxodromic j
  · intro b c hbc p q hp hq t
    cases b <;> cases c
    · exact (hbc rfl).elim
    · change t * P.product i ^ p * t⁻¹ ≠ P.product j ^ q
      exact P.product_nonCommensurable i j hij p q hp hq t
    · change t * P.product j ^ p * t⁻¹ ≠ P.product i ^ q
      exact P.product_nonCommensurable j i hij.symm p q hp hq t
    · exact (hbc rfl).elim
  · intro b
    cases b
    · exact P.elementaryClosure_product_eq_zpowers hmatch i
    · exact P.elementaryClosure_product_eq_zpowers hmatch j
  · intro b
    cases b
    · exact avoidsFiniteCommensurability_iff_oneSided.mp hiF
    · exact avoidsFiniteCommensurability_iff_oneSided.mp hjF

end YiOrientationPureProductFamily

/-- **Hull's product selection with its immediate component match.**

The existential packages the prepared family together with the match proved at
the same DGO depth.  This preserves Hull's order: choose the Lemma 4.21(b)
constant, choose the powers beyond it, then apply the lemma before forgetting
the depth witnesses. -/
def YiOrientationPureProductFamilySelection : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {T : Subgroup G},
    Suitable A.alphabet T → ∀ F : Finset G,
      ∃ P : YiOrientationPureProductFamily A T (Fin (F.card + 2)),
        P.HasConsecutiveComponentMatch

/-- An explicit prepared family and its match inhabit the combined local
selection interface.  This is the constructor model for the repaired
quantifier order. -/
theorem exists_combinedProductSelection_model
    {A : HullGeneratingSet G} {T : Subgroup G} {F : Finset G}
    (P : YiOrientationPureProductFamily A T (Fin (F.card + 2)))
    (hmatch : P.HasConsecutiveComponentMatch) :
    ∃ Q : YiOrientationPureProductFamily A T (Fin (F.card + 2)),
      Q.HasConsecutiveComponentMatch :=
  ⟨P, hmatch⟩

/-- The source-facing assembly theorem.  Selection and matching use one
existential, so the local Yi producer cannot lose the depth at which its cyclic
letters were chosen. -/
theorem yiSuitablePairAvoidingFiniteOneSided_of_productSelection_of_match
    (hselect : YiOrientationPureProductFamilySelection.{u}) :
    YiSuitablePairAvoidingFiniteOneSided.{u} := by
  intro G _ A T hT F
  obtain ⟨P, hmatch⟩ := hselect A hT F
  exact P.exists_yiPair_of_consecutiveComponentMatch F hmatch

end HullSC
end GroupApproximation

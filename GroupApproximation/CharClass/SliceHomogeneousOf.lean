import GroupApproximation.CharClass.ChernClassesEvenOf
import GroupApproximation.CharClass.ChernSplittingOfPowers
import GroupApproximation.CharClass.WuSymmetric

/-!
# Symmetric functions of degree-two classes are homogeneous, over `K`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm; the coefficient-generic form of
`SliceHomogeneous`.

Over a field `K` at an odd prime the cohomology ring `TotalHOf K X` is only graded-commutative, so
products of classes are formed in the commutative even part `Gen.evenPart K X` and read back in
`TotalHOf K X` through the coercion.  A product of `card` degree-two classes lies in degree
`2 · card`, so the elementary symmetric function of degree `q` is concentrated in degree `2q`:
taking the component and putting it back is the identity on it.

That is what identifies a Chern class, which the splitting principle delivers as an elementary
symmetric function of the roots, with a class homogeneous of its own degree.

## Main declarations

* `exists_of_prodOf` — a product of `card` degree-two classes sits in degree `2 · card`.
* `of_component_of_prodOf`, `of_component_esymmOnOf` — **the symmetric function is homogeneous.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

noncomputable section

variable {K : Type} [CommRing K] {X : TopCat.{0}} {σ : Type} [DecidableEq σ]

/-- A product of `B.card` classes of degree two lies in degree `2 * B.card`. -/
theorem exists_of_prodOf (B : Finset σ) (y : σ → Hmod K X 2) :
    ∃ a : Hmod K X (2 * B.card),
      ((∏ l ∈ B, evenTautOf K (y l) : Gen.evenPart K X) : TotalHOf K X)
        = TotalHOf.of K X (2 * B.card) a := by
  induction B using Finset.induction_on with
  | empty =>
      refine ⟨cohCast (by simp) (one (K := K) X), ?_⟩
      rw [TotalHOf.of_cohCast, TotalHOf.of_one]
      show evenCoe K X (∏ l ∈ (∅ : Finset σ), evenTautOf K (y l)) = 1
      rw [Finset.prod_empty, map_one]
  | @insert w B hw ih =>
      obtain ⟨a, ha⟩ := ih
      have hcard : (insert w B).card = B.card + 1 := Finset.card_insert_of_notMem hw
      refine ⟨cohCast (show 2 + 2 * B.card = 2 * (insert w B).card by rw [hcard]; ring)
        (cup (y w) a), ?_⟩
      rw [TotalHOf.of_cohCast, TotalHOf.of_mul, ← ha]
      show evenCoe K X (∏ l ∈ insert w B, evenTautOf K (y l))
        = evenCoe K X (evenTautOf K (y w)) * evenCoe K X (∏ l ∈ B, evenTautOf K (y l))
      rw [Finset.prod_insert hw, map_mul]

/-- Taking the degree-`2q` component of such a product and putting it back is the identity. -/
theorem of_component_of_prodOf (B : Finset σ) (y : σ → Hmod K X 2) (q : ℕ) (hq : B.card = q) :
    TotalHOf.of K X (2 * q) (TotalHOf.component K X (2 * q)
        ((∏ l ∈ B, evenTautOf K (y l) : Gen.evenPart K X) : TotalHOf K X))
      = ((∏ l ∈ B, evenTautOf K (y l) : Gen.evenPart K X) : TotalHOf K X) := by
  subst hq
  obtain ⟨a, ha⟩ := exists_of_prodOf B y
  rw [ha, TotalHOf.component_of]

/-- **The elementary symmetric function of degree-two classes is homogeneous of degree `2q`**,
over any coefficient ring. -/
theorem of_component_esymmOnOf (s : Finset σ) (y : σ → Hmod K X 2) (q : ℕ) :
    TotalHOf.of K X (2 * q) (TotalHOf.component K X (2 * q)
        ((esymmOn s (fun l => evenTautOf K (y l)) q : Gen.evenPart K X) : TotalHOf K X))
      = ((esymmOn s (fun l => evenTautOf K (y l)) q : Gen.evenPart K X) : TotalHOf K X) := by
  have hsum : ((esymmOn s (fun l => evenTautOf K (y l)) q : Gen.evenPart K X) : TotalHOf K X)
      = ∑ B ∈ s.powersetCard q,
          ((∏ l ∈ B, evenTautOf K (y l) : Gen.evenPart K X) : TotalHOf K X) := by
    show evenCoe K X (esymmOn s (fun l => evenTautOf K (y l)) q) = _
    rw [esymmOn_def, map_sum]
    rfl
  rw [hsum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun B hB =>
    of_component_of_prodOf B y q (Finset.mem_powersetCard.mp hB).2

end

end CharClass
end GroupApproximation

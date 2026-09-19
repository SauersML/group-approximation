import GroupApproximation.CharClass.SliceEsymm
import GroupApproximation.CharClass.SteenrodTotal

/-!
# The symmetric functions of degree-two classes are homogeneous

`chernOf` is the degree-`2k` *component* of the Chern class, while the splitting
principle delivers the class itself as an elementary symmetric function of the
roots.  Those agree only because the symmetric function is concentrated in degree
`2k`, and that is what this file proves: taking the component and putting it back
is the identity on it.

The degree grows by two at each factor, so the induction carries a transport, and
`Steenrod.of_cohCast` absorbs it: a class transported along an equality of degrees
is the same element of the graded ring.  That is why the statement can be about
`2 * B.card` without a cast appearing anywhere in it.

## Main declarations

* `exists_of_prod` — a product of `card` degree-two classes sits in degree
  `2 * card`.
* `of_component_esymmOn` — **the symmetric function is homogeneous.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

noncomputable section

variable {X : TopCat.{0}} {σ : Type} [DecidableEq σ]

/-- A product of `B.card` classes of degree two lies in degree `2 * B.card`. -/
theorem exists_of_prod (B : Finset σ) (y : σ → Hmod2 X 2) :
    ∃ a : Hmod2 X (2 * B.card),
      (∏ l ∈ B, TotalH.of X 2 (y l)) = TotalH.of X (2 * B.card) a := by
  induction B using Finset.induction_on with
  | empty =>
      refine ⟨cohCast (by simp) (one X), ?_⟩
      rw [Finset.prod_empty, Steenrod.of_cohCast, TotalH.of_one]
  | @insert w B hw ih =>
      obtain ⟨a, ha⟩ := ih
      have hcard : (insert w B).card = B.card + 1 := Finset.card_insert_of_notMem hw
      refine ⟨cohCast (show 2 + 2 * B.card = 2 * (insert w B).card by
        rw [hcard]; ring) (cup (y w) a), ?_⟩
      rw [Steenrod.of_cohCast, TotalH.of_mul, Finset.prod_insert hw, ha]

/-- Taking the degree-`2q` component of such a product and putting it back is the
identity. -/
theorem of_component_of_prod (B : Finset σ) (y : σ → Hmod2 X 2) (q : ℕ)
    (hq : B.card = q) :
    TotalH.of X (2 * q) (TotalH.component X (2 * q) (∏ l ∈ B, TotalH.of X 2 (y l)))
      = ∏ l ∈ B, TotalH.of X 2 (y l) := by
  subst hq
  obtain ⟨a, ha⟩ := exists_of_prod B y
  rw [ha, TotalH.component_of]

/-- **The elementary symmetric function of degree-two classes is homogeneous of
degree `2q`.** -/
theorem of_component_esymmOn (s : Finset σ) (y : σ → Hmod2 X 2) (q : ℕ) :
    TotalH.of X (2 * q) (TotalH.component X (2 * q)
        (esymmOn s (fun l => TotalH.of X 2 (y l)) q))
      = esymmOn s (fun l => TotalH.of X 2 (y l)) q := by
  rw [esymmOn_def, map_sum, map_sum]
  exact Finset.sum_congr rfl fun B hB =>
    of_component_of_prod B y q (Finset.mem_powersetCard.mp hB).2

end

end CharClass
end GroupApproximation

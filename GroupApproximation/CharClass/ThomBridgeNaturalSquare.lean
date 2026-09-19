import GroupApproximation.CharClass.ThomBridgeNaturalHyper

/-!
# A commuting square of spaces gives a commuting square of relative pullbacks

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The tool the whole naturality layer runs on, isolated so that each square costs
one application instead of a `relPullback_comp` chase.

Every step of the Thom bridge is a `relPullback`, so naturality of any of them is
a square of `relPullback`s, and a square of `relPullback`s commutes as soon as the
underlying square of **spaces** does.  Both routes are `relPullback` along the two
composites, which are equal maps, and `relPullback` does not depend on which
proof witnesses the map-of-pairs condition.

`ThomBridgeNaturalHyper.relPullback_id_comm` is the special case where two of the
four edges are identities; it is kept because it is what the hyperplane step
consumes directly and its hypotheses are already in that shape.

## Main declaration

* `relPullback_comm_of_map_eq` — a commuting square of spaces, transported.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

variable {W X Y Z : TopCat.{0}}

/-- **A commuting square of spaces gives a commuting square of relative
pullbacks.**  The six map-of-pairs conditions are arguments, so the statement
holds of whatever supplies them; only `hcomm` carries content. -/
theorem relPullback_comm_of_map_eq (a : Y ⟶ X) (b : W ⟶ Y) (c : Z ⟶ X) (d : W ⟶ Z)
    (hcomm : b ≫ a = d ≫ c)
    {A : Set X} {B : Set Y} {C : Set Z} {D : Set W}
    (ha : ∀ x ∈ B, (ConcreteCategory.hom a) x ∈ A)
    (hb : ∀ x ∈ D, (ConcreteCategory.hom b) x ∈ B)
    (hc : ∀ x ∈ C, (ConcreteCategory.hom c) x ∈ A)
    (hd : ∀ x ∈ D, (ConcreteCategory.hom d) x ∈ C)
    (hba : ∀ x ∈ D, (ConcreteCategory.hom (b ≫ a)) x ∈ A)
    (hdc : ∀ x ∈ D, (ConcreteCategory.hom (d ≫ c)) x ∈ A)
    (n : ℕ) :
    relPullback (ZMod 2) a ha n ≫ relPullback (ZMod 2) b hb n
      = relPullback (ZMod 2) c hc n ≫ relPullback (ZMod 2) d hd n := by
  rw [← relPullback_comp (ZMod 2) b a hb ha hba n,
    ← relPullback_comp (ZMod 2) d c hd hc hdc n]
  exact relPullback_eq_of_eq (ZMod 2) hcomm hba n

/-! Printed on every build. -/

#print axioms relPullback_comm_of_map_eq

end

end GroupApproximation.CharClass

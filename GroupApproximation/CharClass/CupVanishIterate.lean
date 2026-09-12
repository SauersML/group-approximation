import GroupApproximation.CharClass.CupVanishSub
import GroupApproximation.CharClass.ChernTotalRing

/-!
# A product over a finite cover vanishes

Iterating the two-set theorem over a finite open cover: if each factor vanishes on
its own member of the cover, the product of all of them is zero.

The induction runs in the **total ring**, not in the graded groups.  That is not a
convenience: the product of `k` classes of degree `d` has degree `k * d`, and
every step would need a transport along `Nat.succ_mul` inside the type of a class.
In the total ring degrees are plain naturals and equal values name the same
component, so the whole induction carries the degree as an existential and no cast
appears anywhere.

The ambient union changes at every step, which is why the two-set theorem is used
in its `A ⊔ B` form and the union is supplied as an *equation* rather than
rewritten: the type `opSpace W` depends on `W`, so a rewrite of the open would be
a dependent motive, while an equation is discharged by `subst` inside the lemma.

## Main declarations

* `coverSup` — the union of the first `k` members.
* `exists_prod_vanishing_on_coverSup` — the induction.
* `prod_eq_zero_of_cover` — **the product over a finite cover is zero.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The top open -/

/-- The inclusion of the top open is an isomorphism. -/
def opTopIso (X : TopCat.{0}) : opSpace (⊤ : Opens X) ≅ X where
  hom := opIncl ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- A class vanishing on the whole space vanishes. -/
theorem eq_zero_of_pull_opIncl_top {n : ℕ} {a : Hmod2 X n}
    (h : pull (opIncl (⊤ : Opens X)) n a = 0) : a = 0 := by
  have h' : pull (opTopIso X).hom n a = 0 := h
  calc a = pull (𝟙 X) n a := (pull_id n a).symm
    _ = pull ((opTopIso X).inv ≫ (opTopIso X).hom) n a := by rw [(opTopIso X).inv_hom_id]
    _ = pull (opTopIso X).inv n (pull (opTopIso X).hom n a) := pull_comp _ _ n a
    _ = pull (opTopIso X).inv n 0 := by rw [h']
    _ = 0 := pull_zero _ n

/-! ## 2. The ambient union as an equation -/

/-- The two-set theorem with the union supplied as an equation, so that the call
site never rewrites inside `opSpace`. -/
theorem pull_cup_eq_zero_of_eq_sup (A B W : Opens X) (hW : A ⊔ B = W) {p q : ℕ}
    (hpq : 0 < p + q) (a : Hmod2 X p) (b : Hmod2 X q)
    (ha : pull (opIncl A) p a = 0) (hb : pull (opIncl B) q b = 0) :
    pull (opIncl W) (p + q) (cup a b) = 0 := by
  subst hW
  exact pull_cup_eq_zero_of_sup A B hpq a b ha hb

/-! ## 3. The union of the first `k` members -/

/-- The union of the first `k` members of a family of opens. -/
def coverSup (U : ℕ → Opens X) (k : ℕ) : Opens X := (Finset.range k).sup U

theorem coverSup_one (U : ℕ → Opens X) : coverSup U 1 = U 0 := by
  rw [coverSup, Finset.range_one, Finset.sup_singleton]

theorem coverSup_succ (U : ℕ → Opens X) (k : ℕ) :
    coverSup U k ⊔ U k = coverSup U (k + 1) := by
  refine le_antisymm (sup_le (Finset.sup_le fun l hl => ?_) ?_) (Finset.sup_le fun l hl => ?_)
  · exact Finset.le_sup (Finset.mem_range.mpr
      (Nat.lt_succ_of_lt (Finset.mem_range.mp hl)))
  · exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hl) with h | rfl
    · exact le_sup_of_le_left (Finset.le_sup (Finset.mem_range.mpr h))
    · exact le_sup_right

/-! ## 4. The induction -/

/-- **The induction.**  The product of the first `k + 1` factors is homogeneous of
some positive degree and vanishes on the union of the first `k + 1` members. -/
theorem exists_prod_vanishing_on_coverSup (U : ℕ → Opens X) (d : ℕ) (hd : 0 < d)
    (a : ℕ → Hmod2 X d) (ha : ∀ l, pull (opIncl (U l)) d (a l) = 0) (k : ℕ) :
    ∃ (m : ℕ) (c : Hmod2 X m), 0 < m ∧
      (∏ l ∈ Finset.range (k + 1), TotalH.of X d (a l)) = TotalH.of X m c ∧
      pull (opIncl (coverSup U (k + 1))) m c = 0 := by
  induction k with
  | zero =>
      refine ⟨d, a 0, hd, ?_, ?_⟩
      · rw [Finset.prod_range_one]
      · rw [coverSup_one]
        exact ha 0
  | succ k ih =>
      obtain ⟨m, c, hm, hprod, hvan⟩ := ih
      refine ⟨m + d, cup c (a (k + 1)), by omega, ?_, ?_⟩
      · rw [Finset.prod_range_succ, hprod, TotalH.of_mul]
      · exact pull_cup_eq_zero_of_eq_sup (coverSup U (k + 1)) (U (k + 1))
          (coverSup U (k + 1 + 1)) (coverSup_succ U (k + 1)) (by omega) c (a (k + 1))
          hvan (ha (k + 1))

/-! ## 5. The product over a cover -/

/-- **A product over a finite open cover vanishes.**  Each factor vanishes on its
own member, the members cover, so the product is zero. -/
theorem prod_eq_zero_of_cover (U : ℕ → Opens X) (r : ℕ) (hr : 0 < r)
    (hcov : coverSup U r = ⊤) (d : ℕ) (hd : 0 < d) (a : ℕ → Hmod2 X d)
    (ha : ∀ l, pull (opIncl (U l)) d (a l) = 0) :
    (∏ l ∈ Finset.range r, TotalH.of X d (a l)) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, c, _hm, hprod, hvan⟩ :=
    exists_prod_vanishing_on_coverSup U d hd a ha k
  rw [hcov] at hvan
  rw [hprod, eq_zero_of_pull_opIncl_top hvan, map_zero]

end

end GroupApproximation.CharClass

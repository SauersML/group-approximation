import GroupApproximation.CharClass.CupVanishRepOf
import GroupApproximation.CharClass.CupVanishIterate
import GroupApproximation.CharClass.ChernTotalRingOf

/-!
# A product of classes over a finite open cover vanishes, over a field

Lane `lix-cupone`: the coefficient-generic twin of `CupVanishSub` and `CupVanishIterate`, for lix-lh's
odd-primary Chern layer.  The `F₂` names are unchanged; the space-level definitions `opTopIso` and
`coverSup` carry no coefficients and are reused.

The one difference from `F₂`: `TotalHOf K X` is a `DirectSum.GRing` and not commutative, so the
product over the cover is the **ordered** product `((List.range r).map f).prod`, split off one factor
at a time by `List.prod_range_succ`.  The induction is otherwise the `F₂` one.

## Main declarations

* `pull_cup_eq_zero_of_supOf` — the two-set theorem over an ambient open `A ⊔ B`.
* `exists_prod_vanishing_on_coverSupOf` — the induction.
* `prod_eq_zero_of_coverOf` — **the ordered product over a finite cover is zero.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : TopCat.{0}}

/-- **The two-set theorem over an ambient open set, over a field.** -/
theorem pull_cup_eq_zero_of_supOf (K : Type) [Field K] (A B : Opens X) {p q : ℕ}
    (hpq : 0 < p + q) (a : Hmod K X p) (b : Hmod K X q)
    (ha : pull (opIncl A) p a = 0) (hb : pull (opIncl B) q b = 0) :
    pull (opIncl (A ⊔ B)) (p + q) (cup a b) = 0 := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hB : B ≤ A ⊔ B := le_sup_right
  rw [pull_cup]
  refine cup_eq_zero_of_absToSub_eq_zeroOf K (opRel A (A ⊔ B)) (opRel B (A ⊔ B))
    (opRel_sup_eq_top A B) hpq _ _ ?_ ?_
  · show pull (opIncl (opRel A (A ⊔ B))) p (pull (opIncl (A ⊔ B)) p a) = 0
    rw [← pull_comp, ← relIso_hom_comp_opIncl A (A ⊔ B) hA, pull_comp, ha, pull_zero]
  · show pull (opIncl (opRel B (A ⊔ B))) q (pull (opIncl (A ⊔ B)) q b) = 0
    rw [← pull_comp, ← relIso_hom_comp_opIncl B (A ⊔ B) hB, pull_comp, hb, pull_zero]

/-- A class vanishing on the whole space vanishes, over any ring. -/
theorem eq_zero_of_pull_opIncl_topOf {K : Type} [CommRing K] {n : ℕ} {a : Hmod K X n}
    (h : pull (opIncl (⊤ : Opens X)) n a = 0) : a = 0 := by
  have h' : pull (opTopIso X).hom n a = 0 := h
  calc a = pull (𝟙 X) n a := (pull_id n a).symm
    _ = pull ((opTopIso X).inv ≫ (opTopIso X).hom) n a := by rw [(opTopIso X).inv_hom_id]
    _ = pull (opTopIso X).inv n (pull (opTopIso X).hom n a) := pull_comp _ _ n a
    _ = pull (opTopIso X).inv n 0 := by rw [h']
    _ = 0 := pull_zero _ n

/-- The two-set theorem with the union supplied as an equation. -/
theorem pull_cup_eq_zero_of_eq_supOf (K : Type) [Field K] (A B W : Opens X) (hW : A ⊔ B = W)
    {p q : ℕ} (hpq : 0 < p + q) (a : Hmod K X p) (b : Hmod K X q)
    (ha : pull (opIncl A) p a = 0) (hb : pull (opIncl B) q b = 0) :
    pull (opIncl W) (p + q) (cup a b) = 0 := by
  subst hW
  exact pull_cup_eq_zero_of_supOf K A B hpq a b ha hb

/-- **The induction.**  The ordered product of the first `k + 1` factors is homogeneous of some
positive degree and vanishes on the union of the first `k + 1` members. -/
theorem exists_prod_vanishing_on_coverSupOf (K : Type) [Field K] (U : ℕ → Opens X) (d : ℕ)
    (hd : 0 < d) (a : ℕ → Hmod K X d) (ha : ∀ l, pull (opIncl (U l)) d (a l) = 0) (k : ℕ) :
    ∃ (m : ℕ) (c : Hmod K X m), 0 < m ∧
      ((List.range (k + 1)).map fun l => TotalHOf.of K X d (a l)).prod = TotalHOf.of K X m c ∧
      pull (opIncl (coverSup U (k + 1))) m c = 0 := by
  induction k with
  | zero =>
      refine ⟨d, a 0, hd, ?_, ?_⟩
      · rw [List.prod_range_succ, List.range_zero, List.map_nil, List.prod_nil, one_mul]
      · rw [coverSup_one]
        exact ha 0
  | succ k ih =>
      obtain ⟨m, c, hm, hprod, hvan⟩ := ih
      refine ⟨m + d, cup c (a (k + 1)), by omega, ?_, ?_⟩
      · rw [List.prod_range_succ, hprod, TotalHOf.of_mul]
      · exact pull_cup_eq_zero_of_eq_supOf K (coverSup U (k + 1)) (U (k + 1))
          (coverSup U (k + 1 + 1)) (coverSup_succ U (k + 1)) (by omega) c (a (k + 1))
          hvan (ha (k + 1))

/-- **An ordered product over a finite open cover vanishes**, over a field.  Each factor vanishes on
its own member and the members cover. -/
theorem prod_eq_zero_of_coverOf (K : Type) [Field K] (U : ℕ → Opens X) (r : ℕ) (hr : 0 < r)
    (hcov : coverSup U r = ⊤) (d : ℕ) (hd : 0 < d) (a : ℕ → Hmod K X d)
    (ha : ∀ l, pull (opIncl (U l)) d (a l) = 0) :
    ((List.range r).map fun l => TotalHOf.of K X d (a l)).prod = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, c, _hm, hprod, hvan⟩ := exists_prod_vanishing_on_coverSupOf K U d hd a ha k
  rw [hcov] at hvan
  rw [hprod, eq_zero_of_pull_opIncl_topOf hvan, map_zero]

/-- Over every field, the ordered product of positive-degree classes, each vanishing on one member
of a finite open cover, is zero in the cohomology ring. -/
def PrintedCupVanishCover : Prop :=
  ∀ (K : Type) [Field K] (X : TopCat.{0}) (U : ℕ → Opens X) (r : ℕ), 0 < r →
    coverSup U r = ⊤ → ∀ (d : ℕ), 0 < d → ∀ (a : ℕ → Hmod K X d),
      (∀ l, pull (opIncl (U l)) d (a l) = 0) →
        ((List.range r).map fun l => TotalHOf.of K X d (a l)).prod = 0

theorem printedCupVanishCover : PrintedCupVanishCover := by
  intro K _ X U r hr hcov d hd a ha
  exact prod_eq_zero_of_coverOf K U r hr hcov d hd a ha

#audit_closed_axioms printedCupVanishCover

end

end GroupApproximation.CharClass

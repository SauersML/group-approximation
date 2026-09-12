import GroupApproximation.CharClass.LerayHirschFinite
import GroupApproximation.CharClass.LerayHirschMVOf

/-!
# Leray–Hirsch over a finite cover, over a field

The coefficient-generic form of `LerayHirschFinite` §2–3.  The induction on the length of the
list is the `F₂` one word for word; the only change is the two-set step it calls, which over a
field `K` is `LerayHirschMVOf.LHOver_supOf`.  The distributivity lemma `inf_foldr_sup` carries no
coefficients and is reused.

## Main declarations

* `LHOver_foldrOf` — the induction over the length.
* `bijective_lhSum_of_finite_coverOf` — **Leray–Hirsch over a finite cover, over a field**.
* `lerayHirschGraded_of_finite_coverOf` — the same, in the published interface.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X P : TopCat.{0}}

/-- **Leray–Hirsch over a finite union of good open sets, over a field.**  The induction is on the
length, because the step applies the hypothesis to a different list of the same length. -/
theorem LHOver_foldrOf (K : Type) [Field K] (f : P ⟶ X) (ξ : Hmod K P 2) (r : ℕ)
    (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A) :
    ∀ (k : ℕ) (L : List (Opens X)), L.length ≤ k → (∀ B ∈ L, Good B) →
      ∀ A : Opens X, Good A → LHOver f ξ r (L.foldr (· ⊔ ·) A) := by
  intro k
  induction k with
  | zero =>
    intro L hL _ A hA
    cases L with
    | nil => exact hLH A hA
    | cons B L' => exact absurd hL (by simp)
  | succ k ih =>
    intro L hL hGood A hA
    cases L with
    | nil => exact hLH A hA
    | cons B L' =>
      have hB : Good B := hGood B (by simp)
      have hGood' : ∀ C ∈ L', Good C := fun C hC => hGood C (by simp [hC])
      have hL' : L'.length ≤ k := by
        have h := hL
        simp only [List.length_cons] at h
        omega
      have h1 : LHOver f ξ r (L'.foldr (· ⊔ ·) A) := ih L' hL' hGood' A hA
      have h2 : LHOver f ξ r (B ⊓ L'.foldr (· ⊔ ·) A) := by
        rw [inf_foldr_sup]
        refine ih (L'.map (B ⊓ ·)) (by simpa using hL') ?_ (B ⊓ A) (hinf B A hB)
        intro C hC
        obtain ⟨D, _, rfl⟩ := List.mem_map.mp hC
        exact hinf B D hB
      show LHOver f ξ r (B ⊔ L'.foldr (· ⊔ ·) A)
      exact LHOver_supOf K f ξ r B (L'.foldr (· ⊔ ·) A) (hLH B hB) h1 h2

/-- **Leray–Hirsch over a finite cover, over a field.**  If the powers of `ξ` are a basis over
every member of a finite family of open sets that is closed under intersection with anything, and
that family covers, they are a basis over the whole total space. -/
theorem bijective_lhSum_of_finite_coverOf (K : Type) [Field K] (f : P ⟶ X) (ξ : Hmod K P 2)
    (r : ℕ) (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A)
    (L : List (Opens X)) (hGood : ∀ B ∈ L, Good B)
    (A : Opens X) (hA : Good A) (hcover : L.foldr (· ⊔ ·) A = ⊤) (n : ℕ) :
    Function.Bijective (lhSum f ξ r n) := by
  refine LHOver_top f ξ r ?_ n
  rw [← hcover]
  exact LHOver_foldrOf K f ξ r Good hinf hLH L.length L le_rfl hGood A hA

/-- **The same, in the published interface.** -/
theorem lerayHirschGraded_of_finite_coverOf (K : Type) [Field K] (f : P ⟶ X) (ξ : Hmod K P 2)
    (r : ℕ) (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A)
    (L : List (Opens X)) (hGood : ∀ B ∈ L, Good B)
    (A : Opens X) (hA : Good A) (hcover : L.foldr (· ⊔ ·) A = ⊤) :
    LerayHirschGraded f ξ r :=
  lerayHirschGraded_of_bijective f ξ r fun n =>
    bijective_lhSum_of_finite_coverOf K f ξ r Good hinf hLH L hGood A hA hcover n

end

end LH
end CharClass
end GroupApproximation
